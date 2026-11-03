import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointStatements

/-! # Compactness of points of proper schemes from properness of point maps -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A scheme over `Spec C` has exactly one morphism over `Spec C` to the base itself. -/
instance subsingleton_hom_over_id {C : Type u} [CommRing C] (X : Over (Spec (CommRingCat.of C))) :
    Subsingleton (X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of C)))) :=
  ⟨fun f g => by
    have hf := Over.w f
    have hg := Over.w g
    simp only [Over.mk_hom] at hf hg
    exact Over.OverMorphism.ext (hf.trans hg.symm)⟩

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] [LocallyCompactSpace K]

variable (K) in
/-- Clause B of `LocalFieldProperPointProperties` follows from clause A, applied to the
structure morphism of a proper scheme viewed as a morphism to the base `Spec K`. -/
theorem properSchemeLocalPointCompactness_of_properness (hnd : ¬ DiscreteTopology K)
    (h : SchemePointLocalPropernessProperty K hnd) :
    ProperSchemeLocalPointCompactnessProperty K hnd := by
  intro X _
  let Y : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let f : X ⟶ Y := Over.homMk X.hom (by simp [Y])
  have : IsProper f.left := show IsProper X.hom from inferInstance
  have : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact Y.hom := inferInstanceAs (QuasiCompact (𝟙 _))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (𝟙 _))
  have hp := h X Y f
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  have : Subsingleton (RingPoint K Y K) :=
    inferInstanceAs (Subsingleton (ringTest K K ⟶ Over.mk (𝟙 _)))
  refine ⟨?_⟩
  -- The preimage of `univ` is definitionally `univ`.
  exact hp.isCompact_preimage Set.subsingleton_univ.isCompact

end Langlands.AlgebraicGeometry.PointTopology
