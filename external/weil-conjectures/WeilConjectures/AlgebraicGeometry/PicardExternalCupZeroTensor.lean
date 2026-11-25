/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorBijective
import WeilConjectures.AlgebraicGeometry.ExternalCupZeroGlobalSections

/-! # Degree-zero external tensor comparison

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-zero-tensor).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections of the external tensor product are the tensor of global sections,
with the identification expressed on degree-zero scalar cohomology.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-external-cup-zero-tensor).

Proof: Take a finite affine cover of X. Affine diagonal makes all pairwise
intersections affine. For each affine open V of Y, the affine pullback and tensor
section formulas identify sections of the external coefficients on U_i times V
and (U_i intersect U_j) times V with F(U_i) tensor G(V) and
F(U_i intersect U_j) tensor G(V). These identifications commute with restriction.
The sheaf equalizer computes global sections on X times V. Since tensor over the
field is exact and commutes with the finite products of this cover, that equalizer
is Gamma(X,F) tensor G(V). These identifications are natural in affine V.
Now take a finite affine cover of Y. The same equalizer argument, using affine
pairwise intersections and exact tensor with Gamma(X,F), identifies sections on
X times Y with Gamma(X,F) tensor Gamma(Y,G). Degree-zero derived global sections
are ordinary global sections. On pure tensors the affine section formulas send
s tensor t to the tensor of their projection pullbacks. The Cech/sheaf cup
compatibility, or the Ext-degree-zero evaluation-at-one comparison, identifies
this with externalCup. Thus the induced equivalence has the stated pure-tensor
formula. This argument uses no positive-degree acyclicity, and does not claim
that the tensor total and the product-cover Cech complex are isomorphic.
Empty covers and zero modules give zero section spaces on both sides. -/
theorem picardExternalCup_zero_tensor
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    : ∃ e : (scalarCohomology f F 0 ⊗[k] scalarCohomology g G 0) ≃ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) 0,
      ∀ (a : scalarCohomology f F 0) (b : scalarCohomology g G 0),
        e (a ⊗ₜ[k] b) = externalCup f g F G 0 0 a b := by
  let eF := scalarGlobalSectionsEquiv f F
  let eG := scalarGlobalSectionsEquiv g G
  let eP := scalarGlobalSectionsEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
  let eS := LinearEquiv.ofBijective (externalGlobalSectionsTensor f g F G)
    (externalGlobalSectionsTensor_bijective k X Y f g F G)
  refine ⟨((TensorProduct.congr eF eG).trans eS).trans eP.symm, ?_⟩
  intro a b
  apply eP.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul]
  exact (externalCup_zero_globalSections k X Y f g F G a b).symm

end AlgebraicGeometry.Scheme.Modules
