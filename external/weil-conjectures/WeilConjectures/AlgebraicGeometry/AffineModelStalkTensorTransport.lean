/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.AffineModelStalkPresentation

/-! # Natural intermediate stalk tensor comparisons
Source: Stacks Project, Tags 008H, 0098, 008B and 01BH. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
/-- Natural affine-model comparison after extension from the original stalk.
Source: Stacks Project, Tags 01BH and 008B.
(blueprint: new-e1-affine-model-stalk-tensor-transport)

Proof: Open restriction identifies the stalk of F at i(z) with the U-chart stalk.
The supplied e identifies it with the chart restriction of tilde M. The affine
isomorphism carries this stalk to the tilde stalk at the corresponding prime of A.
The tilde germ map is module localization at that prime. Extension to R cancels
this localization: each denominator is a unit in the original ring stalk and hence
in R. Write a localized stalk element as m/s, with s outside the corresponding prime.
Send r tensor (m/s) to (rho(s) inverse times r) tensor m. Localization equality
is preserved since the element killing the difference also maps to a unit in R;
the balancing relations follow from the composite A-to-S-to-R germ map. The
inverse sends r tensor m to r tensor (m/1), transported back along e and the
chart. Their composites are identities: on m/1 this is immediate, and on m/s
move the invertible scalar s across the tensor. Fractions generate the localized
stalk, and pure tensors generate each tensor product, so this proves both
identities on all elements. All these maps respect module
morphisms. The supplied square therefore identifies the map induced by c with the
one induced by d. Check this on pure tensors and extend by additivity. This works
for arbitrary modules, including zero modules, with no flatness hypothesis. -/
theorem exists_affine_model_stalk_tensor_transport
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (V : Z.Opens) (z : V.toScheme)
    (U : Y.affineOpens) (hzU : i z.1 ∈ U.1) :
    let A := (Γ(Y, U.1) : Type u)
    let S := (Y.presheaf.stalk (i z.1) : Type u)
    let R := (V.toScheme.presheaf.stalk z : Type u)
    let φ : S →+* R := (i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
    letI : Algebra S R := φ.toAlgebra
    let ρ : A →+* R := ((Y.presheaf.germ U.1 (i z.1) hzU) ≫
      i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
    letI : Algebra A R := ρ.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ γ : ∀ (F : Y.Modules) (M : ModuleCat.{u} A),
      ((Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) →
        (R ⊗[S] F.presheaf.stalk (i z.1)) ≃+ R ⊗[A] M,
      ∀ (F G : Y.Modules) (M N : ModuleCat.{u} A) (c : F ⟶ G) (d : M ⟶ N)
        (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M)
        (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj N),
        (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map d →
        ∀ x, γ G N eG ((c.stalkLinearMap (i z.1)).baseChange R x) =
          d.hom.baseChange R (γ F M eF x) := by
  dsimp
  let A := (Γ(Y, U.1) : Type u)
  let S := (Y.presheaf.stalk (i z.1) : Type u)
  let R := (V.toScheme.presheaf.stalk z : Type u)
  let φ : S →+* R := (i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
  let : Algebra S R := φ.toAlgebra
  let ρ : A →+* R := ((Y.presheaf.germ U.1 (i z.1) hzU) ≫
    i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
  let : Algebra A R := ρ.toAlgebra
  let ψ : A →+* S := (Y.presheaf.germ U.1 (i z.1) hzU).hom
  let : Algebra A S := ψ.toAlgebra
  let : IsScalarTower A S R := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  obtain ⟨δ, hδ⟩ := exists_affine_model_stalk_presentation (i z.1) U hzU
  let γ : ∀ (F : Y.Modules) (M : ModuleCat.{u} A),
      ((Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) →
        (R ⊗[S] F.presheaf.stalk (i z.1)) ≃+ R ⊗[A] M := fun F M e ↦
    ((δ F M e).baseChange S R).symm.toAddEquiv.trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A S R R M).toAddEquiv
  refine ⟨γ, ?_⟩
  intro F G M N c d eF eG h x
  have hn (t : R ⊗[A] M) :
      (γ G N eG).symm (d.hom.baseChange R t) =
        (c.stalkLinearMap (i z.1)).baseChange R ((γ F M eF).symm t) := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => simp [h₁, h₂]
    | tmul r m =>
      change r ⊗ₜ[S] (δ G N eG) (1 ⊗ₜ[A] d.hom m) =
        r ⊗ₜ[S] c.stalkLinearMap (i z.1) ((δ F M eF) (1 ⊗ₜ[A] m))
      rw [hδ F G M N c d eF eG h]
      rfl
  apply (γ G N eG).symm.injective
  change (γ G N eG).symm ((γ G N eG)
    ((c.stalkLinearMap (i z.1)).baseChange R x)) = _
  simpa only [AddEquiv.symm_apply_apply] using (hn ((γ F M eF) x)).symm
end AlgebraicGeometry
