import Langlands.GroupScheme.Reductive.GeometricAdjoint

/-! # Nontrivial geometric fibres and arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} {G H : GroupScheme S}

/-- The represented group functor has a point distinct from the identity,
possibly on a non-affine test scheme. -/
def HasNontrivialPoint (G : GroupScheme S) : Prop :=
  ∃ (U : Over S) (x : U ⟶ G.X), x ≠ 1

/-- Nontriviality of the whole group functor is inequality of its full and
identity subgroup functors. -/
theorem hasNontrivialPoint_iff_top_ne_bot :
    HasNontrivialPoint G ↔ (⊤ : SubgroupFunctor G) ≠ ⊥ := by
  constructor
  · rintro ⟨U, x, hx⟩ heq
    have h : x ∈ (⊤ : SubgroupFunctor G).carrier U := Subgroup.mem_top _
    rw [heq, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h
    exact hx h
  · intro hn
    by_contra h
    apply hn
    apply SubgroupFunctor.ext
    intro U
    apply le_antisymm ?_ bot_le
    intro x _
    change x = 1
    by_contra hx
    exact h ⟨U, x, hx⟩

/-- Isomorphisms preserve an actual witness of functorial nontriviality. -/
theorem HasNontrivialPoint.of_iso (hG : HasNontrivialPoint G) (e : G ≅ H) :
    HasNontrivialPoint H := by
  obtain ⟨U, x, hx⟩ := hG
  refine ⟨U, x ≫ e.hom.hom.hom, fun h => hx ?_⟩
  have h' := congrArg (fun y => y ≫ e.inv.hom.hom) h
  simpa only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using h'

/-- Nontriviality is invariant under isomorphism of group schemes. -/
theorem hasNontrivialPoint_iff_of_iso (e : G ≅ H) :
    HasNontrivialPoint G ↔ HasNontrivialPoint H :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- A nontrivial pullback gives a nontrivial point of the original group
by forgetting the new base of its test scheme. -/
theorem HasNontrivialPoint.of_baseChange (b : T ⟶ S)
    (hG : HasNontrivialPoint ((GroupScheme.baseChange b).obj G)) :
    HasNontrivialPoint G := by
  obtain ⟨U, x, hx⟩ := hG
  refine ⟨(Over.map b).obj U, baseChangePointsEquiv b G U x, fun h => hx ?_⟩
  exact (baseChangePointsEquiv b G U).map_eq_one_iff.mp h

/-- Fpqc pullback preserves nontriviality of the full group functor. -/
theorem HasNontrivialPoint.baseChange_fpqc (b : T ⟶ S)
    [Flat b] [Surjective b] [QuasiCompact b] (hG : HasNontrivialPoint G) :
    HasNontrivialPoint ((GroupScheme.baseChange b).obj G) := by
  apply hasNontrivialPoint_iff_top_ne_bot.mpr
  intro h
  apply hasNontrivialPoint_iff_top_ne_bot.mp hG
  apply SubgroupFunctor.eq_bot_of_baseChange_eq_bot b
  rwa [SubgroupFunctor.top_baseChange]

/-- An arbitrary field extension preserves and reflects nontriviality
of the full functor of points. -/
theorem hasNontrivialPoint_fieldExtension_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    HasNontrivialPoint ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) ↔
      HasNontrivialPoint G := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k K
  let : Surjective (algebraBaseMap k K) := hs
  let : Flat (algebraBaseMap k K) := hf
  let : QuasiCompact (algebraBaseMap k K) := hq
  exact ⟨HasNontrivialPoint.of_baseChange _,
    HasNontrivialPoint.baseChange_fpqc _⟩

variable (G)

/-- Each chosen geometric fibre has a point distinct from the identity
on some relative test scheme. -/
def IsFibrewiseNontrivial : Prop :=
  ∀ s : S, HasNontrivialPoint (geometricFiber G s)

/-- A field-valued pullback and its residue-field fibre have the same
functorial nontriviality. -/
theorem fieldNontrivial_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    HasNontrivialPoint ((GroupScheme.baseChange b).obj G) ↔
      HasNontrivialPoint
        ((GroupScheme.baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  exact (hasNontrivialPoint_iff_of_iso (fieldPointFiberIso G b)).trans
    (hasNontrivialPoint_fieldExtension_iff
      (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
      ((GroupScheme.baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G))

/-- A geometric fibre is nontrivial exactly when the actual residue-field
fibre is nontrivial. -/
theorem geometricNontrivial_iff_residueFiber (s : S) :
    HasNontrivialPoint (geometricFiber G s) ↔
      HasNontrivialPoint ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G) := by
  have h := fieldNontrivial_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rwa [himage] at h

/-- Any field-valued point tests nontriviality of the chosen geometric fibre
at its image. -/
theorem fieldNontrivial_iff_geometricFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    HasNontrivialPoint ((GroupScheme.baseChange b).obj G) ↔
      HasNontrivialPoint (geometricFiber G (b (IsLocalRing.closedPoint k))) :=
  (fieldNontrivial_iff_residueFiber G b).trans
    (geometricNontrivial_iff_residueFiber G _).symm

variable {G}

/-- Fibrewise nontriviality is invariant under group-scheme isomorphism. -/
theorem IsFibrewiseNontrivial.of_iso (hG : IsFibrewiseNontrivial G) (e : G ≅ H) :
    IsFibrewiseNontrivial H := by
  intro s
  exact (hG s).of_iso ((GroupScheme.baseChange (geometricPoint S s)).mapIso e)

/-- Nontrivial geometric fibres remain nontrivial along every morphism
of base schemes. -/
theorem IsFibrewiseNontrivial.baseChange (b : T ⟶ S)
    (hG : IsFibrewiseNontrivial G) :
    IsFibrewiseNontrivial ((GroupScheme.baseChange b).obj G) := by
  intro t
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := fieldNontrivial_iff_geometricFiber G (geometricPoint T t ≫ b)
  rw [himage] at hfield
  exact (hfield.mpr (hG (b t))).of_iso
    (baseChangeCompIso b (geometricPoint T t) G)

/-- A scheme-surjective pullback reflects nontrivial geometric fibres. -/
theorem IsFibrewiseNontrivial.of_baseChange (b : T ⟶ S) [Surjective b]
    (hG : IsFibrewiseNontrivial ((GroupScheme.baseChange b).obj G)) :
    IsFibrewiseNontrivial G := by
  intro s
  obtain ⟨t, rfl⟩ := b.surjective s
  have h := (hG t).of_iso (baseChangeCompIso b (geometricPoint T t) G).symm
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := (fieldNontrivial_iff_geometricFiber G (geometricPoint T t ≫ b)).mp h
  rwa [himage] at hfield

/-- The nontrivial geometric-fibre condition can be checked after any
scheme-surjective base change. -/
theorem isFibrewiseNontrivial_baseChange_iff (b : T ⟶ S) [Surjective b] :
    IsFibrewiseNontrivial ((GroupScheme.baseChange b).obj G) ↔
      IsFibrewiseNontrivial G :=
  ⟨IsFibrewiseNontrivial.of_baseChange b, IsFibrewiseNontrivial.baseChange b⟩

end Langlands.GroupScheme
