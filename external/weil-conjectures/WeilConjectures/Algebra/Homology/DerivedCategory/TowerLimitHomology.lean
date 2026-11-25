/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMilnor
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit

/-!
# Cohomology of a derived limit of a tower with epimorphic cohomology transitions

Let `C` be an abelian category with exact countable products in which sequential limits of
epimorphisms project epimorphically onto the first term (`CategoryTheory.EpiπAppZeroOfEpi`), for
instance abelian sheaves on the pro-étale site
(`AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_ab`). For a homotopy limit cone `c` over a
tower `F` in `D(C)` whose cohomology tower `H^{i-1}(Fₙ)` has epimorphic transitions,
`Hⁱ(R lim F) = lim Hⁱ(Fₙ)`
(`DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimit`): this is the Milnor sequence
`0 ⟶ lim¹ H^{i-1}(Fₙ) ⟶ Hⁱ(R lim F) ⟶ lim Hⁱ(Fₙ) ⟶ 0`
(`DerivedCategory.isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit`) in the case where the
`lim¹` term vanishes (`CategoryTheory.epi_one_sub_of_epiπAppZeroOfEpi`).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **Cohomology of a derived limit with epimorphic cohomology transitions.** In an abelian
category with exact countable products in which sequential limits of epimorphisms project
epimorphically onto the first term (e.g. sheaves on a replete topos), let `c` be a homotopy
limit cone over a tower `F` in `D(C)` such that the transitions of the tower `H^{i-1}(Fₙ)` are
epimorphisms. Then `Hⁱ(R lim F) = lim Hⁱ(Fₙ)`: `1 - t` is surjective on `∏ H^{i-1}(Fₙ)`, so
the Milnor sequence gives the claim. -/
noncomputable def isLimitHomologyFunctorMapConeOfIsHomotopyLimit (hC : EpiπAppZeroOfEpi C)
    (hc : IsHomotopyLimit c) (i : ℤ)
    (hepi : ∀ n : ℕ, Epi ((homologyFunctor C (i - 1)).map (F.map (homOfLE n.le_succ).op))) :
    IsLimit ((homologyFunctor C i).mapCone c) :=
  let G := F ⋙ homologyFunctor C (i - 1)
  let t : ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) ⟶ ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) :=
    Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ G.map (homOfLE n.le_succ).op
  have ht (n : ℕ) : t ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ G.map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  have := isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit hc (i - 1) i (by lia)
    (productIsProduct _) t ht
    (epi_one_sub_of_epiπAppZeroOfEpi hC (F := G) hepi (productIsProduct _) t ht)
    (limit.isLimit _)
  IsLimit.ofPointIso (limit.isLimit _)

end DerivedCategory
