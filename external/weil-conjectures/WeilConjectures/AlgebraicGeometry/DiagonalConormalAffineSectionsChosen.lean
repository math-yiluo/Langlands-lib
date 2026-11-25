/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsUnique
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineLiftInjective
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineDerivationSpan

/-! # Affine sections of the chosen diagonal conormal derivation

The affine coordinate calculation for the normalized derivation chosen by
`exists_diagonalConormalDerivation`, and the fact that normalization by the kernel class map
determines a diagonal conormal derivation (Stacks Project, Tag 08S2). -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The affine coordinate calculation for the canonical normalized derivation chosen by
`exists_diagonalConormalDerivation`.  This is the geometric affine calculation of Tags
01KJ, 01R3 and 08S2; the proof is intentionally isolated so the supplied-derivation
statement only performs transport along uniqueness. (blueprint: stage3-diagonal-conormal-chosen).
Proof: write A = Γ(X,U) and R = Γ(S,V). On W = U ×_V U the diagonal is the
closed immersion Spec(A) → Spec(A ⊗[R] A) induced by multiplication μ. Restrict
its actual sheaf-module kernel to W, obtaining the ideal ker μ. Restriction and
tensor pullback identify the conormal sections over U with (ker μ)/(ker μ)²,
compatibly with the canonical tensor-pullback unit. The multiplication-ideal
construction of KaehlerDifferential gives an A-linear equivalence with this same
quotient. Compose the two equivalences. The class of 1 ⊗ a - a ⊗ 1 corresponds
to d a on the differential side and to the chosen derivation's value on the
conormal side, by Classical.choose_spec and its normalization formula. Thus the
composite has the required d-formula. W is affine without assuming f separated. -/
theorem exists_affine_sections_for_chosen_derivation (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    let D := Classical.choose (exists_diagonalConormalDerivation f)
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
          Γ(diagonalConormal f, U.1),
        ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
          D.d (X := op U.1) a := by
  let D := Classical.choose (exists_diagonalConormalDerivation f)
  have hD : IsDiagonalConormalDerivation f D :=
    Classical.choose_spec (exists_diagonalConormalDerivation f)
  let d : ((diagonalConormal f).val.obj (op U.1)).Derivation
      (f.appLE V.1 U.1 hUV) :=
    ModuleCat.Derivation.mk (fun a ↦ D.d (X := op U.1) a)
      (fun a b ↦ map_add _ a b) (fun a b ↦ D.d_mul a b)
      (fun a ↦ by
        rw [Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app]
        exact PresheafOfModulesOfCommRing.Derivation'.d_app D _)
  let e := d.desc.hom
  have he (a : Γ(X, U.1)) : e (CommRingCat.KaehlerDifferential.d a) =
      D.d (X := op U.1) a := d.desc_d a
  have hi : Function.Injective e :=
    diagonalConormal_affine_lift_injective f U V hUV D hD e he
  have hs : Function.Surjective e := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← diagonalConormal_affine_derivation_span f U V hUV D hD]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨CommRingCat.KaehlerDifferential.d a, he a⟩
  exact ⟨LinearEquiv.ofBijective e ⟨hi, hs⟩, he⟩

/-- Normalization by the kernel class map determines a diagonal conormal derivation.
This is the uniqueness part of the difference-derivation construction in Tag 08S2.
(blueprint: stage3-diagonal-conormal-uniqueness) -/
theorem diagonalConormalDerivation_ext (f : X ⟶ S)
    {D₁ D₂ : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf}
    (h₁ : IsDiagonalConormalDerivation f D₁)
    (h₂ : IsDiagonalConormalDerivation f D₂) : D₁ = D₂ := by
  ext U a
  exact diagonalConormal_affine_sections_unique f U.unop D₁ D₂ h₁ h₂ a

end AlgebraicGeometry
