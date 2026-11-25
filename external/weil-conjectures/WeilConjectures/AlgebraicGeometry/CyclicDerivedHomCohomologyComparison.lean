/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonBijective
import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonNaturality

/-!
# Comparing free-representable derived Hom with cyclic cohomology

Source: Stacks Project, Tag 03Q8, and the free-representable interpretation of sections.
(blueprint: lem-sbc-cyclic-derived-hom-cohomology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Free-representable derived Hom computes cohomology on the fibre product, and geometric
restriction to zero forces the corresponding presheaf restriction to zero.

Source: Stacks Project, Tag 03Q8, the restricted cohomology presheaf; the free-sheaf
adjunction argument in
`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/FreeSheaf.lean`.
(blueprint: lem-sbc-cyclic-derived-hom-cohomology-comparison).

Proof: The free abelian sheaf on an etale representable corepresents evaluation. Pullback
along h takes the free sheaf on W to the free sheaf on Y times_X W, as follows from the
pullback/direct-image adjunction and the section-corepresenting universal property.
Extension by zero along the etale projection Y times_X W to Y takes the constant free
abelian sheaf to this free representable sheaf. Extension by zero is exact and left
adjoint to restriction; its derived adjunction therefore identifies Hom from the
free representable in degree zero to F[0][q] with Ext^q from the constant integer sheaf
to F restricted to Y times_X W. This is Sheaf.H. The canonical pullback identification
for constant cyclic sheaves identifies the latter coefficients with Z/e on that fibre
product. The evaluation adjunctions are natural in W: precomposition with the free
map induced by v corresponds to cohomologyMap of the induced fibre-product morphism,
followed by the constant-coefficient isomorphism. That isomorphism and the additive
comparison preserve and reflect zero, giving the implication displayed here.
No affine, nonempty, positive-degree, or nonzero-modulus hypothesis is used. -/
theorem exists_cyclicDerivedHom_cohomology_comparison {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) :
    let P := (uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod e))⟦(q : ℤ)⟧)
    ∀ W : X.Etale,
      ∃ E : P.obj (op W) ≃+ Sheaf.H ((pullback h W.hom).constantZMod e) q,
        ∀ (V : X.Etale) (v : V ⟶ W) (ξ : P.obj (op W)),
          cohomologyMap
            (pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp)
              (by simp)) _ q (E ξ) = 0 → P.map v.op ξ = 0 := by
  dsimp only
  intro W
  have hbij (V : X.Etale) : Function.Bijective (cyclicRepresentableCohomologyMap h e q V) := by
    let i := (Sheaf.functorH _ q).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst h V.hom)).app (AddCommGrpCat.of (ULift (ZMod e))))
    exact i.addCommGroupIsoToAddEquiv.bijective.comp
      (abelianRepresentableCohomologyMap_bijective h (Y.constantZMod e) q V)
  let E := AddEquiv.ofBijective (cyclicRepresentableCohomologyMap h e q W) (hbij W)
  refine ⟨E, ?_⟩
  intro V v ξ hz
  apply (hbij V).injective
  rw [map_zero]
  have hn := cyclicRepresentableCohomologyMap_naturality h e q W V v ξ
  change cohomologyMap _ _ q (cyclicRepresentableCohomologyMap h e q W ξ) = 0 at hz
  dsimp only at hn
  rw [hz, map_zero] at hn
  exact hn.symm

end AlgebraicGeometry.Etale
