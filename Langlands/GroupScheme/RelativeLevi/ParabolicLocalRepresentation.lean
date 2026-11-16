import Langlands.GroupScheme.RelativeLevi.ParabolicLocalParameters
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Representation by the finite affine parabolic quotient chart -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.AlgebraicSpace CoproductChart

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    {I : Type u} [Finite I] {P : I → GroupScheme (Spec (CommRingCat.of R))}
    (j : ∀ a, P a ⟶ G) (hj : ∀ a, IsRelativeParabolicSubgroup (j a))
    (htypes : HasUniformParabolicFieldTypes j)

include htypes

set_option maxHeartbeats 800000 in
/-- Every actual parabolic family is etale-locally a value of the finite
smooth proper quotient chart. -/
theorem finiteAffineParabolicChart_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective
      (Scheme.etaleTopology.over (Spec (CommRingCat.of R)))
      (finiteAffineParabolicChart hG j hj) := by
  constructor
  intro T F
  let d := fun t : T.left => etaleParabolicParameter hG j hj htypes T F t
  let V := fun t : T.left => (d t).neighbourhood
  let q : ∀ t, V t ⟶ T := fun t => (d t).projection
  apply (Scheme.etaleTopology.over _).superset_covering
    (S := Sieve.ofArrows V q) ?_ ?_
  · rw [Sieve.generate_le_iff]
    intro W f hf
    obtain ⟨t⟩ := hf
    refine ⟨⟨((d t).lift ≫
      (affineParabolicQuotient hG (j (d t).index) (hj (d t).index)).quotient.projection) ≫
      sigmaOverι (affineParabolicQuotientComponents hG j hj) (d t).index⟩, ?_⟩
    exact (finiteAffineParabolicChart_app_comp hG j hj (d t).index (d t).lift).trans
      (d t).evaluates
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    exact ⟨fun t => ⟨t, (d t).point, (d t).point_over⟩, fun t => (d t).etale⟩

set_option maxHeartbeats 800000 in
/-- Uniform field types make the actual finite smooth proper quotient chart
an isomorphism of presheaves. -/
theorem finiteAffineParabolicChart_isIso :
    IsIso (finiteAffineParabolicChart hG j hj) := by
  let S := Spec (CommRingCat.of R)
  let J := Scheme.etaleTopology.over S
  let M := (finiteAffineParabolicQuotient hG j hj).val
  let H := (Langlands.AlgebraicGeometry.Sites.fppfSheafToEtaleSheaf S (Type (u + 1))).obj
    ((schemeSheaf S).obj M)
  let K := parabolicEtaleSheaf G hG
  let f : H ⟶ K := ObjectProperty.homMk (finiteAffineParabolicChart hG j hj)
  have hm : Mono (finiteAffineParabolicChart hG j hj) :=
    finiteAffineParabolicChart_mono_of_fieldTypes hG j hj htypes
  have hi : Sheaf.IsLocallyInjective f :=
    CategoryTheory.Presheaf.isLocallyInjective_of_injective J _
      (fun T => (mono_iff_injective _).mp
        (inferInstance : Mono ((finiteAffineParabolicChart hG j hj).app T)))
  have hs : Sheaf.IsLocallySurjective f :=
    finiteAffineParabolicChart_locallySurjective hG j hj htypes
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨hi, hs⟩
  exact inferInstanceAs
    (IsIso ((sheafToPresheaf J (Type (u + 1))).map f))

/-- The representing isomorphism from the actual finite smooth proper
quotient coproduct to the presheaf of actual parabolic families. -/
def finiteAffineParabolicIso :
    (schemeYoneda (Spec (CommRingCat.of R))).obj
      (finiteAffineParabolicQuotient hG j hj).val ≅ parabolicPresheaf G hG := by
  have := finiteAffineParabolicChart_isIso hG j hj htypes
  exact asIso (finiteAffineParabolicChart hG j hj)

/-- The actual finite smooth proper quotient coproduct represents parabolics
when the supplied family has uniform field types. -/
def finiteAffineParabolicRepresentation :
    (parabolicPresheaf G hG).RepresentableBy
      (finiteAffineParabolicQuotient hG j hj).val :=
  (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm
    (finiteAffineParabolicIso hG j hj htypes)

end Langlands.GroupScheme.ParabolicSubgroupModuli
