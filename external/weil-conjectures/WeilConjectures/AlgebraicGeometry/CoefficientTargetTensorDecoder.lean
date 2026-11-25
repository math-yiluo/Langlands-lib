/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.CoefficientIntersectionRingPushout
import WeilConjectures.AlgebraicGeometry.CoefficientIntersectionSectionModel

/-! # Injective of the coefficient tensor map

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The affine coefficient computation supplies a linear decoder on supported sections.
This assertion does not quantify over a candidate coefficient map and does not assert
injectivity. It specifies the decoder only on supported pullback-unit generators.
Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
(blueprint: aux-pc-coefficient-target-tensor-decoder).

Proof: Set A = Gamma(U,O), D = Gamma(Z,O), R = Gamma(B,O), and let N be
F(Z), with its given structural A-action. The affine intersection base-change
lemma makes I = W intersect fprime inverse image B affine. The restricted
cartesian square identifies I with Z times_U B. The affine ring computation
identifies Gamma(I,O) with R tensor_A D. Restriction preserves quasi-coherence,
so the affine pullback section theorem identifies sections of M on I with
(R tensor_A D) tensor_D N. Compare tensorPullback and pullback using uniqueness
of left adjoints and the conjugate-isomorphism unit equation; compare pullback
along the open immersions with restriction using restrictFunctorIsoPullback.
These comparisons take the restricted pullback-unit section of s to
(1 tensor 1) tensor s. The A-action is the displayed one because the canonical
chart followed by GammaSpecIso cancels. Compose coefficientSupportIso with
these identifications, and then with the balanced R-linear map sending
(r tensor d) tensor n to r tensor (d*n). This map is well-defined: balancing
over D is associativity of the D-action on N, and balancing over A uses the
structural A-action on D and N. On the specified generator its value is
1 tensor (1*s) = 1 tensor s. This gives the asserted decoder and formula.
If Z or B is empty all relevant modules vanish and the same formulas hold;
no flatness, nonemptiness, or cover is used. -/
theorem exists_coefficientTarget_tensor_decoder
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    let : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∃ l : Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B)
          →ₗ[Γ(T', B)] (Γ(T', B) ⊗[Γ(U.toScheme, ⊤)] N),
        ∀ s : N, l ((coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))) =
          (1 : Γ(T', B)) ⊗ₜ[Γ(U.toScheme, ⊤)] s := by
  classical
  dsimp only
  let A := Γ(U.toScheme, ⊤)
  let R := Γ(T', B)
  let D := Γ((f ⁻¹ᵁ U).toScheme, Z)
  let I := W ⊓ f' ⁻¹ᵁ B
  let S := Γ(X', I)
  let : Algebra A R := (g.appLE ⊤ B (by simp)).hom.toAlgebra
  let : Algebra A D := (coefficientBaseRingMap f U Z).toAlgebra
  let : Algebra D S :=
    (coefficientIntersectionRingMap f U Z g g' f' sq W hW B).toAlgebra
  let : Algebra R S := (f'.appLE B I inf_le_right).hom.toAlgebra
  let : Algebra A S := ((f'.appLE B I inf_le_right).hom.comp
    (g.appLE ⊤ B (by simp)).hom).toAlgebra
  let N : Type u := Γ(F.restrict (f ⁻¹ᵁ U).ι, Z)
  let : Module A N := Module.compHom _ (coefficientBaseRingMap f U Z)
  let M := (pullback g').obj F
  have : IsScalarTower A D N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  obtain ⟨hD, hR, hP⟩ :=
    coefficientIntersection_ring_pushout f U hU Z hZ g g' f' sq W hW B hB
  let := hD
  let := hR
  let := hP
  let : Module R Γ(M, I) := Module.compHom _ (f'.appLE B I inf_le_right).hom
  have : IsScalarTower R S Γ(M, I) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let support : Γ((pushforward (W.ι ≫ f')).obj (M.restrict W.ι), B) →ₗ[R] Γ(M, I) :=
    { toFun := (coefficientSupportIso f' M W B).hom
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by
        intro r s
        exact coefficientSupportIso_smul f' M W B r s }
  obtain ⟨e, he⟩ :=
    exists_coefficientIntersection_section_model f F U hU Z hZ g g' f' sq W hW B hB
  let c := (Algebra.IsPushout.cancelBaseChange A R D S N).toLinearMap
  refine ⟨c.comp ((e.restrictScalars R).comp support), ?_⟩
  intro s
  change c (e ((coefficientSupportIso f' M W B).hom
    ((coefficientSupportIso f' M W B).inv _))) = _
  rw [Iso.inv_hom_id_apply, he]
  exact Algebra.IsPushout.cancelBaseChange_tmul A R D S N s

end
end AlgebraicGeometry.Scheme.Modules
