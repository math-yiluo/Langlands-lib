import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Simply connected and nontrivial geometric fibres under base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A group scheme has a nonidentity point on some relative test scheme. -/
def HasNontrivialPoints {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  ∃ (T : Over S) (x : T ⟶ G.X), x ≠ 1

theorem hasNontrivialPoints_iff_top_ne_bot {S : Scheme.{u}} (G : GroupScheme S) :
    HasNontrivialPoints G ↔ (⊤ : SubgroupFunctor G) ≠ ⊥ := by
  classical
  constructor
  · rintro ⟨T, x, hx⟩ h
    have hx' : x ∈ (⊥ : SubgroupFunctor G).carrier T := by
      rw [← h]
      exact Subgroup.mem_top x
    exact hx (by simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hx')
  · intro h
    by_contra hn
    apply h
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    have hx : x = 1 := by
      by_contra hx
      exact hn ⟨T, x, hx⟩
    simp only [SubgroupFunctor.top_carrier, SubgroupFunctor.bot_carrier,
      Subgroup.mem_top, Subgroup.mem_bot, hx]

/-- Nontriviality on all relative tests is invariant under group isomorphism. -/
theorem hasNontrivialPoints_iff_of_iso {S : Scheme.{u}}
    {G H : GroupScheme S} (e : G ≅ H) :
    HasNontrivialPoints G ↔ HasNontrivialPoints H := by
  constructor
  · rintro ⟨T, x, hx⟩
    refine ⟨T, x ≫ e.hom.hom.hom, ?_⟩
    intro he
    have hh := congrArg (fun y => y ≫ e.inv.hom.hom) he
    apply hx
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using hh
  · rintro ⟨T, x, hx⟩
    refine ⟨T, x ≫ e.inv.hom.hom, ?_⟩
    intro he
    have hh := congrArg (fun y => y ≫ e.hom.hom.hom) he
    apply hx
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using hh

/-- Fpqc base change preserves and reflects nontriviality of the full point functor. -/
theorem hasNontrivialPoints_baseChange_iff {S T : Scheme.{u}} (G : GroupScheme S)
    (b : T ⟶ S) [Flat b] [Surjective b] [QuasiCompact b] :
    HasNontrivialPoints ((baseChange b).obj G) ↔ HasNontrivialPoints G := by
  rw [hasNontrivialPoints_iff_top_ne_bot, hasNontrivialPoints_iff_top_ne_bot]
  constructor
  · intro h he
    apply h
    simpa only [SubgroupFunctor.top_baseChange, SubgroupFunctor.bot_baseChange] using
      congrArg (fun F : SubgroupFunctor G => F.baseChange b) he
  · intro h he
    apply h
    exact SubgroupFunctor.eq_bot_of_baseChange_eq_bot b
      (by simpa only [SubgroupFunctor.top_baseChange] using he)

/-- Arbitrary field extension preserves and reflects algebraic simple connectedness. -/
theorem isSimplyConnected_fieldExtension_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSimplyConnected ((baseChange (algebraBaseMap k K)).obj G) ↔
      IsSimplyConnected G := by
  constructor
  · intro h
    exact IsSimplyConnected.of_fieldExtension isSemisimpleFieldExtension
      centralIsogenyBaseChange (IsSemisimple.of_fieldExtension h.isSemisimple) h
  · exact isSimplyConnectedFieldExtension k K G

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Simple connectedness of every chosen geometric fibre. -/
def IsFibrewiseSimplyConnected : Prop :=
  ∀ s : S, IsSimplyConnected (geometricFiber G s)

/-- Nontriviality of every chosen geometric fibre, on its full point functor. -/
def HasNontrivialGeometricFibres : Prop :=
  ∀ s : S, HasNontrivialPoints (geometricFiber G s)

/-- A field-valued pullback is simply connected precisely when its residue-field
fibre is simply connected. -/
theorem fieldSimplyConnected_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsSimplyConnected ((baseChange b).obj G) ↔
      IsSimplyConnected
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  exact (isSimplyConnected_iff_of_iso (fieldPointFiberIso G b)).trans
    (isSimplyConnected_fieldExtension_iff
      (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
      ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G))

/-- Simple connectedness of the chosen geometric fibre is equivalent to simple
connectedness over the actual residue field. -/
theorem geometricSimplyConnected_iff_residueFiber (s : S) :
    IsSimplyConnected (geometricFiber G s) ↔
      IsSimplyConnected ((baseChange (S.fromSpecResidueField s)).obj G) := by
  have h := fieldSimplyConnected_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rwa [himage] at h

/-- An actual field-valued point detects simple connectedness of the geometric
fibre at its image. -/
theorem fieldSimplyConnected_iff_geometricFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsSimplyConnected ((baseChange b).obj G) ↔
      IsSimplyConnected (geometricFiber G (b (IsLocalRing.closedPoint k))) :=
  (fieldSimplyConnected_iff_residueFiber G b).trans
    (geometricSimplyConnected_iff_residueFiber G _).symm

/-- Nontriviality of a field-valued pullback is equivalent to nontriviality of
the actual residue-field fibre at its image. -/
theorem fieldNontrivialPoints_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    HasNontrivialPoints ((baseChange b).obj G) ↔
      HasNontrivialPoints
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  obtain ⟨hs, hf, hq⟩ :=
    fieldExtension_fpqc (S.residueField (b (IsLocalRing.closedPoint k))) k
  let : Surjective (Spec.map (fieldPointResidueMap b)) := hs
  let : Flat (Spec.map (fieldPointResidueMap b)) := hf
  let : QuasiCompact (Spec.map (fieldPointResidueMap b)) := hq
  exact (hasNontrivialPoints_iff_of_iso (fieldPointFiberIso G b)).trans
    (hasNontrivialPoints_baseChange_iff _ _)

/-- Nontriviality of a geometric fibre can be tested over the residue field. -/
theorem geometricNontrivialPoints_iff_residueFiber (s : S) :
    HasNontrivialPoints (geometricFiber G s) ↔
      HasNontrivialPoints ((baseChange (S.fromSpecResidueField s)).obj G) := by
  have h := fieldNontrivialPoints_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rwa [himage] at h

/-- An actual field-valued point detects nontriviality of the geometric fibre
at its image. -/
theorem fieldNontrivialPoints_iff_geometricFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    HasNontrivialPoints ((baseChange b).obj G) ↔
      HasNontrivialPoints (geometricFiber G (b (IsLocalRing.closedPoint k))) :=
  (fieldNontrivialPoints_iff_residueFiber G b).trans
    (geometricNontrivialPoints_iff_residueFiber G _).symm

variable {G} {T : Scheme.{u}} (b : T ⟶ S)

/-- The simply connected geometric fibre condition pulls back along every
scheme morphism. -/
theorem IsFibrewiseSimplyConnected.baseChange (hG : IsFibrewiseSimplyConnected G) :
    IsFibrewiseSimplyConnected ((baseChange b).obj G) := by
  intro t
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := fieldSimplyConnected_iff_geometricFiber G (geometricPoint T t ≫ b)
  rw [himage] at hfield
  have h := hfield.mpr (hG (b t))
  exact h.of_iso (baseChangeCompIso b (geometricPoint T t) G).symm

/-- Fibrewise nontriviality pulls back along every scheme morphism. -/
theorem HasNontrivialGeometricFibres.baseChange (hG : HasNontrivialGeometricFibres G) :
    HasNontrivialGeometricFibres ((baseChange b).obj G) := by
  intro t
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := fieldNontrivialPoints_iff_geometricFiber G (geometricPoint T t ≫ b)
  rw [himage] at hfield
  have h := hfield.mpr (hG (b t))
  exact (hasNontrivialPoints_iff_of_iso
    (baseChangeCompIso b (geometricPoint T t) G)).mp h

end Langlands.GroupScheme
