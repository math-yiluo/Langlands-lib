import Langlands.GroupScheme.IsomorphismSchemePrecomposition
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.AutomorphicAction.FppfCenterQuotient
import Langlands.GroupScheme.NormalQuotientReductiveGluing

/-! # Source-isomorphism transport of supplied relative adjoint quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsRelativeAdjointQuotient

variable {S : Scheme.{u}} {G G' A : GroupScheme S} {q : G ⟶ A}
  (hq : IsRelativeAdjointQuotient q) (i : G' ≅ G)

include hq

/-- Changing the source by an actual isomorphism retains the full-centre quotient. -/
theorem precompose : IsRelativeAdjointQuotient (i.hom ≫ q) := by
  have := isIso_left_of_iso i
  refine ⟨IsReductive.of_iso i hq.isReductive, hq.isReductive_target,
    ?_, ?_, ?_, ?_⟩
  · let := hq.isQuotient.1
    change Flat (i.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · let := hq.isQuotient.2.1
    change Surjective (i.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · let := hq.isQuotient.2.2.1
    change LocallyOfFinitePresentation (i.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc,
      ← mem_range_kernelι_iff, hq.isQuotient.2.2.2,
      mem_center_comp_iso_iff]

/-- The source isomorphism intertwines the two canonical inner actions on every test. -/
theorem innerAction_precompose {T : Over S} (d : T ⟶ A.X) (g : T ⟶ G'.X) :
    (hq.precompose i).innerAction.act d g ≫ i.hom.hom.hom =
      hq.innerAction.act d (g ≫ i.hom.hom.hom) := by
  let hp := hq.precompose i
  let : Flat (i.hom ≫ q).hom.hom.left := hp.isQuotient.1
  let : Surjective (i.hom ≫ q).hom.hom.left := hp.isQuotient.2.1
  let : LocallyOfFinitePresentation (i.hom ≫ q).hom.hom.left := hp.isQuotient.2.2.1
  apply AutomorphicAction.hom_ext_of_fppf_local_quotient_lift (i.hom ≫ q) d
  intro W t x hx
  rw [← Category.assoc, hp.innerAction.naturality, hq.innerAction.naturality, hx,
    AutomorphicAction.act_lift_of_restrict_eq_conjugation
      hp.innerAction hp.innerAction_restrict]
  change (x * (t ≫ g) * x⁻¹) ≫ i.hom.hom.hom =
    hq.innerAction.act ((x ≫ i.hom.hom.hom) ≫ q.hom.hom)
      (t ≫ (g ≫ i.hom.hom.hom))
  rw [AutomorphicAction.act_lift_of_restrict_eq_conjugation
    hq.innerAction hq.innerAction_restrict]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

end IsRelativeAdjointQuotient

namespace OuterIsomorphismScheme

variable {S : Scheme.{u}} {G G' H A : GroupScheme S} {q : G ⟶ A}
  {hq : IsRelativeAdjointQuotient q} {I : GroupIsomorphismScheme G H}

/-- Transport an outer quotient through a source isomorphism, using the same
supplied adjoint target and its canonical full-centre action. -/
def precomposeAdjoint (O : OuterIsomorphismScheme I hq.innerAction) (i : G' ≅ G) :
    OuterIsomorphismScheme (I.precompose i) (hq.precompose i).innerAction :=
  O.precompose i (hq.precompose i).innerAction
    (fun _ d g => hq.innerAction_precompose i d g)

end OuterIsomorphismScheme

end Langlands.GroupScheme
