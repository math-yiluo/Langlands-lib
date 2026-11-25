/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.RestrictedTensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.AffineModelStalkTensorTransport

/-! # Natural stalk comparison for the pullback of an affine tilde model

Source: Stacks Project, Tags 008H, 0098, 008B and 01BH. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- A sheaf isomorphism to an affine tilde model induces a tensor stalk
identification, naturally for morphisms respecting the affine identifications.
There is no flatness or closed immersion hypothesis.
Source: Stacks Project, Tags 008H and 0098 (inverse image stalks), 008B
(change of rings), and 01BH (associated modules).
(blueprint: new-k1-affine-model-tensor-pullback-stalk).

Proof: Restriction identifies the stalk of F at i(z) with its chart stalk.
Transport along e and the affine chart isomorphism, and identify the tilde stalk
with localization of M at the corresponding prime. Inverse-image stalk
comparison and extension-of-scalars stalk comparison, already assembled as the
natural isomorphism exists_tensorPullback_stalk_iso, identify tensor pullback
with O_Z,z tensor over O_Y,i(z) of the original stalk. Restriction to V transports
the ring and module stalks by the open immersion isomorphisms. Tensor
associativity then cancels the intermediate localization: R tensor over A of M
is the result, with A acting on R by the displayed composite germ/stalk map.
All maps are constructed from germs and pure tensors and are natural. Apply
this naturality and the supplied affine square to get the last equality.
Equality on pure tensors extends by additivity. The argument applies to all
modules without finiteness hypotheses and to zero modules; the chosen point
ensures its affine localization and neighborhoods exist. -/
theorem exists_affine_model_tensorPullback_stalk
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (V : Z.Opens) (z : V.toScheme)
    (U : Y.affineOpens) (hzU : i z.1 ∈ U.1) :
    let A := (Γ(Y, U.1) : Type u)
    let R := (V.toScheme.presheaf.stalk z : Type u)
    let ρ : A →+* R := ((Y.presheaf.germ U.1 (i z.1) hzU) ≫
      i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
    letI : Algebra A R := ρ.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ τ : ∀ (F : Y.Modules) (M : ModuleCat.{u} A),
      ((Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) →
        ((Scheme.Modules.restrictFunctor V.ι).obj
          ((Scheme.Modules.tensorPullback i).obj F)).presheaf.stalk z ≃+ R ⊗[A] M,
      ∀ (F G : Y.Modules) (M N : ModuleCat.{u} A) (c : F ⟶ G) (d : M ⟶ N)
        (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M)
        (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj N),
        (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map d →
        ∀ x, τ G N eG
          (((Scheme.Modules.restrictFunctor V.ι).map
            ((Scheme.Modules.tensorPullback i).map c)).stalkLinearMap z x) =
          d.hom.baseChange R (τ F M eF x) := by
  let ρ : (Γ(Y, U.1) : Type u) →+* (V.toScheme.presheaf.stalk z : Type u) :=
    ((Y.presheaf.germ U.1 (i z.1) hzU) ≫ i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
  let := ρ.toAlgebra
  let φ : (Y.presheaf.stalk (i z.1) : Type u) →+*
      (V.toScheme.presheaf.stalk z : Type u) := (i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
  let := φ.toAlgebra
  dsimp only
  obtain ⟨β, hβ⟩ := exists_restricted_tensorPullback_stalk i V z
  obtain ⟨γ, hγ⟩ := exists_affine_model_stalk_tensor_transport i V z U hzU
  refine ⟨fun F M e ↦ (β F).trans (γ F M e), ?_⟩
  intro F G M N c d eF eG h x
  change γ G N eG (β G _) = d.hom.baseChange _ (γ F M eF (β F x))
  rw [hβ F G c x]
  exact hγ F G M N c d eF eG h (β F x)

end AlgebraicGeometry
