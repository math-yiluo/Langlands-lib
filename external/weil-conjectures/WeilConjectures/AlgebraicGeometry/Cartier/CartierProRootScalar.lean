/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

/-- For n>0 invertible on Z, commutative rings R,A killed by n and a hom φ:R→A, let
θ:ν*(R_Z(1))→Res(ν*(A_Z(1))) be normalized on pure root tensors through the comparison adjunction
units. Then the pro-etale root map for R followed by forget(θ) equals the pro-etale root map for A
[def-sfb-cartier-reduction-data, lemma-cycle-class-cartier-divisor].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-pro-root-scalar).
Proof: Unfold the root map and cancel its common inverse roots comparison. Transpose the remaining
maps under the abelian comparison adjunction. The forgetful comparison is itself the mate of the
module comparison unit, so adjunction naturality reduces the equality to the specified tensor
normalization at a=1. Ring homomorphisms preserve one. -/
theorem pro_root_scalar (n : ℕ) (hn : 0 < n) {R A : Type (u + 1)}
    [CommRing R] [CommRing A] (φ : R →+* A) (hR : (n : R) = 0) (hA : (n : A) = 0)
    (Z : Scheme.{u}) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (θ : geoCartierLine R n hR Z ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj
        (geoCartierLine A n hA Z))
    (hθ : ∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf n).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z n R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R n Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
        (Scheme.finiteEtaleTateLine Z n A hA)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator A n Z hA W (φ a) z)) :
    cartierProRootMap R n hR Z hn hZ ≫ (cartierForget R Z).map θ =
      cartierProRootMap A n hA Z hn hZ := by
  unfold cartierProRootMap
  simp only [Category.assoc]
  congr 1
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} Z
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  unfold cartierForgetComparison
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext W z
  change θ.hom.app ((Scheme.toProEt Z).op.obj W)
      (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
        (Scheme.finiteEtaleTateLine Z n R hR)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator R n Z hR W 1 z)) =
    ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
      (Scheme.finiteEtaleTateLine Z n A hA)).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A n Z hA W 1 z)
  have hh := hθ W 1 z
  simpa only [map_one] using hh
end AlgebraicGeometry.ProEtale
