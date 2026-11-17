import Langlands.GroupScheme.Adjoint.GeometricBaseChange
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Reductive.GenericFiberGeometry

/-! # Adjoint geometric fibres and arbitrary base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Triviality of the full centre is preserved and reflected by an fpqc base change. -/
theorem center_eq_bot_baseChange_iff {S T : Scheme.{u}} (G : GroupScheme S)
    (b : T ⟶ S) [Flat b] [Surjective b] [QuasiCompact b] :
    center ((GroupScheme.baseChange b).obj G) = ⊥ ↔ center G = ⊥ := by
  constructor
  · intro h
    apply SubgroupFunctor.eq_bot_of_baseChange_eq_bot b
    rwa [← center_baseChange]
  · exact center_eq_bot_baseChange b

/-- Adjointness ascends along every field extension. -/
theorem IsAdjoint.baseChange_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsAdjoint G) :
    IsAdjoint ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  ⟨isSemisimpleFieldExtension k K G hG.isSemisimple,
    center_eq_bot_baseChange _ hG.center_eq_bot⟩

/-- Adjointness is reflected by every field extension. -/
theorem IsAdjoint.of_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsAdjoint ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    IsAdjoint G := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k K
  let : Surjective (algebraBaseMap k K) := hs
  let : Flat (algebraBaseMap k K) := hf
  let : QuasiCompact (algebraBaseMap k K) := hq
  exact ⟨IsSemisimple.of_fieldExtension hG.isSemisimple,
    (center_eq_bot_baseChange_iff G (algebraBaseMap k K)).mp hG.center_eq_bot⟩

/-- Arbitrary field extension preserves and reflects adjointness. -/
theorem isAdjoint_fieldExtension_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsAdjoint ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) ↔ IsAdjoint G :=
  ⟨IsAdjoint.of_fieldExtension, IsAdjoint.baseChange_fieldExtension⟩

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Every chosen geometric fibre is an adjoint semisimple group. -/
def IsFibrewiseAdjoint : Prop :=
  ∀ s : S, IsAdjoint (geometricFiber G s)

/-- Adjointness of a specified field-valued pullback can be tested on the
residue-field fibre at its image. -/
theorem fieldAdjoint_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsAdjoint ((GroupScheme.baseChange b).obj G) ↔
      IsAdjoint
        ((GroupScheme.baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  exact (isAdjoint_iff_of_iso (fieldPointFiberIso G b)).trans
    (isAdjoint_fieldExtension_iff
      (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
      ((GroupScheme.baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G))

/-- Adjointness of a chosen geometric fibre is equivalent to adjointness
over the actual residue field. -/
theorem geometricAdjoint_iff_residueFiber (s : S) :
    IsAdjoint (geometricFiber G s) ↔
      IsAdjoint ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G) := by
  have h := fieldAdjoint_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rwa [himage] at h

/-- A field-valued point detects adjointness of the geometric fibre at its image. -/
theorem fieldAdjoint_iff_geometricFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsAdjoint ((GroupScheme.baseChange b).obj G) ↔
      IsAdjoint (geometricFiber G (b (IsLocalRing.closedPoint k))) :=
  (fieldAdjoint_iff_residueFiber G b).trans
    (geometricAdjoint_iff_residueFiber G _).symm

variable {G} {T : Scheme.{u}} (b : T ⟶ S)

/-- The adjoint geometric-fibre condition pulls back along any scheme morphism. -/
theorem IsFibrewiseAdjoint.baseChange (hG : IsFibrewiseAdjoint G) :
    IsFibrewiseAdjoint ((GroupScheme.baseChange b).obj G) := by
  intro t
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := fieldAdjoint_iff_geometricFiber G (geometricPoint T t ≫ b)
  rw [himage] at hfield
  have h := hfield.mpr (hG (b t))
  exact h.of_iso (baseChangeCompIso b (geometricPoint T t) G).symm

/-- A scheme-surjective base change reflects the adjoint geometric-fibre condition. -/
theorem IsFibrewiseAdjoint.of_baseChange [Surjective b]
    (hG : IsFibrewiseAdjoint ((GroupScheme.baseChange b).obj G)) :
    IsFibrewiseAdjoint G := by
  intro s
  obtain ⟨t, rfl⟩ := b.surjective s
  have h := (hG t).of_iso (baseChangeCompIso b (geometricPoint T t) G)
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  have hfield := (fieldAdjoint_iff_geometricFiber G (geometricPoint T t ≫ b)).mp h
  rwa [himage] at hfield

/-- Adjoint geometric fibres can be checked after any scheme-surjective base change. -/
theorem isFibrewiseAdjoint_baseChange_iff [Surjective b] :
    IsFibrewiseAdjoint ((GroupScheme.baseChange b).obj G) ↔ IsFibrewiseAdjoint G :=
  ⟨IsFibrewiseAdjoint.of_baseChange b, IsFibrewiseAdjoint.baseChange b⟩

end Langlands.GroupScheme
