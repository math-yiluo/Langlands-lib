/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassCore
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassQ

/-! # The affine diagonal ideal class map

Source: Stacks Project, Tags 08S2, 01KJ and 01R3.
(blueprint: lem-sc-diagonal-conormal-affine-ideal-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- On an affine diagonal chart the tensor multiplication kernel maps onto the
actual conormal sections, compatibly with the canonical tensor-pullback unit.
This statement is independent of any normalized derivation.
Source: Stacks Project, Tag 08S2, affine calculation; Tags 01KJ and 01R3.
(blueprint: lem-sc-diagonal-conormal-affine-ideal-class).
Proof: write A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A and J = ker(B → A).
The open W = p₁⁻¹U ∩ p₂⁻¹U is U ×_V U, affine with section ring B.
Its canonical ring coordinates send a ⊗ 1 to p₁*(a) and 1 ⊗ a to p₂*(a).
The diagonal inverse image of W is U, and its restriction is the closed immersion
induced by multiplication B → A. Restriction preserves the actual module-sheaf
kernel, identifying its sections with J, through the injective kernel inclusion.
Thus for every j in J there is a unique kernel section s whose image is r(j).
Tensor pullback commutes with restriction: the tensor formula and the inverse-image
adjunction identify the restricted pullback and its unit with those of this closed
immersion. Apply affine_conormal_sections_existence to identify conormal sections
with J/J², with the unit sending s to the quotient class of j. Compose J → J/J²
with this identification to obtain q. The quotient map is surjective, hence so is q.
The A-action through the first tensor factor descends to multiplication on the
quotient and equals the ordinary A-action on conormal sections, so q is A-linear.
The unit formula holds for every j, not only for tensor differences. This construction
uses the restricted closed diagonal and never assumes that f is separated.
If U is empty, B and both section modules are zero and the same maps apply. -/
theorem diagonalConormal_affine_ideal_class (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
    ∃ (r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W))
      (q : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) →ₗ[Γ(X, U.1)]
        Γ(diagonalConormal f, U.1)),
      Function.Surjective q ∧
      (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
        (pullback.snd f f).appLE U.1 W inf_le_right a) ∧
      (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
        (pullback.fst f f).appLE U.1 W inf_le_left a) ∧
      ∀ (hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W)
        (j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1)),
        ∃ s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom), W),
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j ∧
          q j = (diagonalConormal f).presheaf.map (homOfLE hδ).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (pullback.diagonal f))).unit.app
                (kernel (SheafOfModules.unitToPushforwardObjUnit
                  (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  obtain ⟨r, hr₂, hr₁, hlift⟩ := diagonalConormal_affine_ideal_class_core f U V hUV
  obtain ⟨e, he⟩ := diagonalConormal_affine_ideal_class_q f U V hUV r hr₂ hr₁
  let q := e.toLinearMap.comp
    ((KaehlerDifferential.fromIdeal Γ(S, V.1) Γ(X, U.1)).restrictScalars Γ(X, U.1))
  refine ⟨r, q, e.surjective.comp
    (KaehlerDifferential.fromIdeal_surjective Γ(S, V.1) Γ(X, U.1)), hr₂, hr₁, ?_⟩
  intro hδ j
  obtain ⟨s, hs⟩ := hlift j
  exact ⟨s, hs, he hδ j s hs⟩

end AlgebraicGeometry
