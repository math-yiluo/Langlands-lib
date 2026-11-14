import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent
import Langlands.GroupScheme.SmoothConnectedNormalizerProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Geometry and closed normalizers of relative tori -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

variable {S : Scheme.{u}} {T : GroupScheme S}

/-- An étale form of a finite split torus is smooth over its base. -/
theorem IsTorus.smooth (hT : IsTorus T) : Smooth T.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun _ => ⟨inferInstance, inferInstance⟩)
  have : MorphismProperty.IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => (h𝒰 i).smooth

/-- All field-valued fibres of a relative torus are connected. -/
theorem IsTorus.geometricallyConnected (hT : IsTorus T) :
    GeometricallyConnected T.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  have (i : 𝒰.I₀) : Etale (𝒰.f i) := 𝒰.map_prop i
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun _ => ⟨inferInstance, inferInstance⟩)
  have : IsZariskiLocalAtTarget (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  have : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective :=
    GeometricallyConnected.descendsAlong_surjective
  have : MorphismProperty.DescendsAlong
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.DescendsAlong.of_le (fun _ _ _ h => h.1.1)
  have : MorphismProperty.IsLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => ?_
  exact ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr
    fun _K _ b => ((h𝒰 i).baseChange b).connectedSpace⟩

/-- The normalizer of a closed relative torus in a smooth affine group has
an actual closed representative whose inclusion is locally of finite presentation. -/
theorem closedNormalizer {G : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (N : GroupScheme S) (j : N ⟶ G),
      IsClosedSubgroup j ∧ LocallyOfFinitePresentation j.hom.hom.left ∧
        (torusNormalizer i).IsRepresentedBy j :=
  smoothConnectedNormalizer S G T.toGrp i hi hT.smooth hT.geometricallyConnected

section ChosenNormalizer

variable {G : GroupScheme S} {T : CommGroupScheme S}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)

/-- A chosen actual normalizer group scheme for a closed relative torus. -/
noncomputable def normalizerGroupScheme : GroupScheme S :=
  (closedNormalizer i hT hi).choose

/-- The inclusion of the chosen normalizer in the ambient group. -/
noncomputable def normalizerHom : normalizerGroupScheme i hT hi ⟶ G :=
  (closedNormalizer i hT hi).choose_spec.choose

/-- The chosen inclusion is closed, locally finitely presented, and represents
the actual normalizer on every scheme test. -/
theorem normalizerHom_spec :
    IsClosedSubgroup (normalizerHom i hT hi) ∧
      LocallyOfFinitePresentation (normalizerHom i hT hi).hom.hom.left ∧
        (torusNormalizer i).IsRepresentedBy (normalizerHom i hT hi) :=
  (closedNormalizer i hT hi).choose_spec.choose_spec

end ChosenNormalizer

end Langlands.GroupScheme.RelativeTorus
