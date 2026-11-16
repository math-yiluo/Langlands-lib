import Langlands.GroupScheme.RelativeLevi.ParabolicAffineQuotientChart
import Langlands.GroupScheme.RelativeLevi.ParabolicCoproductInjectivity
import Langlands.AlgebraicGeometry.Morphisms.FiniteCoproduct

/-! # Finite smooth proper affine-base parabolic quotient charts -/

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

/-- The finite family of actual affine-base homogeneous quotient schemes. -/
def affineParabolicQuotientComponents (a : I) : Over (Spec (CommRingCat.of R)) :=
  (affineParabolicQuotient hG (j a) (hj a)).quotient.scheme

/-- The actual finite coproduct of homogeneous quotients, with its smooth proper
structure morphism to the affine base. -/
def finiteAffineParabolicQuotient :
    {M : Over (Spec (CommRingCat.of R)) // Smooth M.hom ∧ IsProper M.hom} :=
  Langlands.AlgebraicGeometry.FiniteCoproduct.smoothProperCoproduct
    (fun a => (affineParabolicQuotientComponents hG j hj a).left)
    (fun a => (affineParabolicQuotientComponents hG j hj a).hom)
    (fun a => affineParabolicQuotient_smooth hG (j a) (hj a))
    (fun a => (affineParabolicQuotient hG (j a) (hj a)).proper)

/-- The actual quotient family on each component. -/
def affineParabolicQuotientFamilies (a : I) :
    ParabolicSubgroup
      ((GroupScheme.baseChange (affineParabolicQuotientComponents hG j hj a).hom).obj G) :=
  homogeneousQuotientParabolic hG (j a) (hj a)
    (affineParabolicQuotient hG (j a) (hj a)).quotient

/-- Component quotient families glued on the actual finite coproduct scheme. -/
def finiteAffineParabolicFamily :
    ParabolicSubgroup
      ((GroupScheme.baseChange (finiteAffineParabolicQuotient hG j hj).val.hom).obj G) :=
  coproductParabolic hG (affineParabolicQuotientComponents hG j hj)
    (affineParabolicQuotientFamilies hG j hj)

/-- The natural parabolic chart from the finite smooth proper quotient coproduct. -/
def finiteAffineParabolicChart :
    (schemeYoneda (Spec (CommRingCat.of R))).obj
      (finiteAffineParabolicQuotient hG j hj).val ⟶ parabolicPresheaf G hG :=
  coproductParabolicChart hG (affineParabolicQuotientComponents hG j hj)
    (affineParabolicQuotientFamilies hG j hj)

/-- A group-valued lift in a component evaluates to the actual conjugate family. -/
theorem finiteAffineParabolicChart_app_comp {T : Over (Spec (CommRingCat.of R))}
    (a : I) (g : T ⟶ G.X) :
    (finiteAffineParabolicChart hG j hj).app (op T)
      ⟨(g ≫ (affineParabolicQuotient hG (j a) (hj a)).quotient.projection) ≫
        sigmaOverι (affineParabolicQuotientComponents hG j hj) a⟩ =
      conjugateParabolic hG (j a) (hj a) g := by
  change restrict hG
    ((g ≫ (affineParabolicQuotient hG (j a) (hj a)).quotient.projection) ≫
      sigmaOverι (affineParabolicQuotientComponents hG j hj) a)
    (coproductParabolic hG (affineParabolicQuotientComponents hG j hj)
      (affineParabolicQuotientFamilies hG j hj)) = _
  rw [← restrict_comp, restrict_coproductParabolic]
  let Q := (affineParabolicQuotient hG (j a) (hj a)).quotient
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  exact restrict_quotientParabolic_comp hG (j a) (hj a) Q.projection
    (fun U g h hgh =>
      (SubgroupFunctor.range (j a)).le_normalizer U ((Q.fibers U g h).mp hgh)) g

omit [Finite I] in
/-- The actual quotient family of each component is injective on every test scheme. -/
theorem affineParabolicQuotientFamilies_injective (a : I)
    (T : Over (Spec (CommRingCat.of R))) :
    Function.Injective (fun b : T ⟶ affineParabolicQuotientComponents hG j hj a =>
      restrict hG b (affineParabolicQuotientFamilies hG j hj a)) := by
  intro b c hbc
  exact congrArg ULift.down
    (homogeneousQuotientChart_injective hG (j a) (hj a)
      (affineParabolicQuotient hG (j a) (hj a)).quotient
      (affineParabolic_normalizer_eq hG (j a) (hj a)) T hbc)

/-- Disjointness of component families on nonempty tests makes the finite
smooth proper chart a monomorphism of the actual parabolic presheaf. -/
theorem finiteAffineParabolicChart_mono_of_disjoint
    (htype : ∀ (a b : I) (T : Over (Spec (CommRingCat.of R)))
      (x : T ⟶ affineParabolicQuotientComponents hG j hj a)
      (y : T ⟶ affineParabolicQuotientComponents hG j hj b),
      restrict hG x (affineParabolicQuotientFamilies hG j hj a) =
        restrict hG y (affineParabolicQuotientFamilies hG j hj b) →
      a = b ∨ IsEmpty T.left) :
    Mono (finiteAffineParabolicChart hG j hj) :=
  coproductParabolicChart_mono_of_disjoint hG
    (affineParabolicQuotientComponents hG j hj) (affineParabolicQuotientFamilies hG j hj)
    (affineParabolicQuotientFamilies_injective hG j hj) htype

end Langlands.GroupScheme.ParabolicSubgroupModuli
