import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Closed-subgroup detection by an epimorphic product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G Z D C : GroupScheme S}

/-- Factor the product map through a representative containing both factors. -/
def subgroupProductFactor {F : SubgroupFunctor G} {j : C ⟶ G}
    (hj : F.IsRepresentedBy j) (i : Z ⟶ G) (d : D ⟶ G)
    (hi : SubgroupFunctor.range i ≤ F) (hd : SubgroupFunctor.range d ≤ F) :
    Z.X ⊗ D.X ⟶ C.X :=
  subgroupProductMap (hj.factorHom i hi) (hj.factorHom d hd)

/-- The factor map recovers the original multiplication after the inclusion. -/
theorem subgroupProductFactor_comp {F : SubgroupFunctor G} {j : C ⟶ G}
    (hj : F.IsRepresentedBy j) (i : Z ⟶ G) (d : D ⟶ G)
    (hi : SubgroupFunctor.range i ≤ F) (hd : SubgroupFunctor.range d ≤ F) :
    subgroupProductFactor hj i d hi hd ≫ j.hom.hom = subgroupProductMap i d := by
  simp only [subgroupProductFactor, subgroupProductMap, MonObj.mul_comp, Category.assoc]
  have hi' := congrArg (fun f => f.hom.hom) (hj.factorHom_comp i hi)
  have hd' := congrArg (fun f => f.hom.hom) (hj.factorHom_comp d hd)
  change (hj.factorHom i hi).hom.hom ≫ j.hom.hom = i.hom.hom at hi'
  change (hj.factorHom d hd).hom.hom ≫ j.hom.hom = d.hom.hom at hd'
  rw [hi', hd']

/-- A closed immersion into an affine scheme over the base is invertible if it is epi. -/
theorem isIso_of_isClosedImmersion_of_epi_over {X Y : Over S}
    (j : X ⟶ Y) [IsAffine Y.left] [IsClosedImmersion j.left] [Epi j] : IsIso j := by
  have : Epi j.left := (Over.forget S).map_epi j
  have : IsIso ((Over.forget S).map j) :=
    show IsIso j.left from IsClosedImmersion.isIso_of_injective_of_isAffine
      (Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi j.left)
  exact isIso_of_reflects_iso j (Over.forget S)

/-- A closed subgroup containing both factors of an epimorphic product is the whole group. -/
theorem SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_epi_subgroupProductMap
    {F : SubgroupFunctor G} [IsAffine G.X.left] (hF : F.HasClosedRepresentative)
    (i : Z ⟶ G) (d : D ⟶ G) [Epi (subgroupProductMap i d)]
    (hi : SubgroupFunctor.range i ≤ F) (hd : SubgroupFunctor.range d ≤ F) : F = ⊤ := by
  obtain ⟨C, j, hjc, hj⟩ := hF
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Epi j.hom.hom :=
    epi_of_epi_fac (subgroupProductFactor_comp hj i d hi hd)
  have : IsIso j.hom.hom := isIso_of_isClosedImmersion_of_epi_over j.hom.hom
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    exact Subgroup.mem_top _
  · intro _
    rw [← hj.2]
    refine ⟨x ≫ inv j.hom.hom, ?_⟩
    change (x ≫ inv j.hom.hom) ≫ j.hom.hom = x
    simp

end Langlands.GroupScheme
