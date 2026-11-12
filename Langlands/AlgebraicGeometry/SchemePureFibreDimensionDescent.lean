import Langlands.AlgebraicGeometry.SchemeFilteredFiberGeometryProof

/-! # Pure fibre dimension alone descends along cofiltered affine limits -/

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit EtaleEquivalenceRelation.Action.TargetLimit SchemeFiberGeometry
open Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

/-- Pure dimension of every fibre descends along a cofiltered affine limit, for a
finitely presented relative morphism with quasi-compact quasi-separated target model. -/
def RelativePureFibreDimensionDescentStatement : Prop :=
  ∀ (d : ℕ) (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (S X Y : Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact b] [QuasiSeparated b]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
    HasPureDimensionFibers d (AffineLimit.baseChangeMap a b f w p) ↔
      ∃ i, HasPureDimensionFibers d (AffineLimit.baseChangeMap a b f w (t.app i))

/-- Constructibility of the actual pure-dimension locus and its cartesian
inverse-image comparison detect the condition at one stage. -/
theorem relativePureFibreDimensionDescent : RelativePureFibreDimensionDescentStatement.{u} := by
  intro d I _ _ D _ S X Y t a b f w _ _ _ _ _ c hc p hp
  have hlevel (i : I) : IsConstructible
      (pureDimensionFiberLocus d (AffineLimit.baseChangeMap a b f w (t.app i))) := by
    have : LocallyOfFinitePresentation (AffineLimit.baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    have : QuasiCompact (AffineLimit.baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    have : QuasiSeparatedSpace (pullback (t.app i) b : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) b)
    exact isConstructible_pureDimensionFiberLocus_of_sublevelProperties
      relativeDimensionSublevelProperties_proof _ d
  constructor
  · intro H
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    have H' := (pureDimensionFiberLocus_eq_univ_iff d _).mpr H
    rw [pureDimensionFiberLocus_cone a b f w D t c p hp i d] at H'
    obtain ⟨j, r, hj⟩ := exists_map_preimage_eq_univ_of_isConstructible
      (diagram D t b) (cone D t b c p hp) (isLimitCone D t b c p hp hc)
      i _ (hlevel i) H'
    have : LocallyOfFiniteType (AffineLimit.baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    refine ⟨j, (pureDimensionFiberLocus_eq_univ_iff d _).mp ?_⟩
    rw [pureDimensionFiberLocus_baseChange (morphismDiagram_cartesian a b f w D t r).flip]
    exact hj
  · rintro ⟨i, hi⟩
    apply (pureDimensionFiberLocus_eq_univ_iff d _).mp
    rw [pureDimensionFiberLocus_cone a b f w D t c p hp i d,
      (pureDimensionFiberLocus_eq_univ_iff d _).mpr hi, preimage_univ]

end Langlands.AlgebraicGeometry.SchemeLimitModel
