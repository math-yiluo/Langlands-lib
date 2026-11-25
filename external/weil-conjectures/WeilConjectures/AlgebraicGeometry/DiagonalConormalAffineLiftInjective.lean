/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassCore
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineIdealClassQ
import WeilConjectures.AlgebraicGeometry.AffineConormalSectionsExistence
import WeilConjectures.AlgebraicGeometry.DiagonalConormal
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Injectivity of the affine diagonal conormal lift

Source: Stacks Project, Tag 08S2, affine calculation; Tags 01KJ, 01R3 and 00RW.
(blueprint: stage3-diagonal-conormal-affine-lift-injective).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The lift of a normalized difference derivation has no kernel on an affine chart.
Source: Stacks Project, Tag 08S2, final affine calculation, and Algebra, Tag 00RW.
(blueprint: stage3-diagonal-conormal-affine-lift-injective).
Proof: put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A and J = ker(B → A), where
B → A is multiplication. By Tag 01KJ the open U ×_V U is affine with ring B,
and the diagonal restricts to the closed immersion Spec A → Spec B. Restriction
of the actual sheaf-module kernel of O → Δ_* O to this open is the tilde module
of J: restriction preserves kernels and the closed-immersion pushforward is the
module of A with its B-action by multiplication. Tensor pullback and restriction
therefore identify the conormal over U with the tilde module of A ⊗[B] J.
The tensor-over-quotient calculation gives A ⊗[B] J = J/J². Its unit sends a
kernel section to its class modulo J², by Tag 01R3. For each a in A the kernel
section whose image is 1 ⊗ a - a ⊗ 1 exists by the sectionwise kernel property.
The normalization hD identifies D(a) with the class of this section. Hence under
the conormal identification e sends da to the class of 1 ⊗ a - a ⊗ 1.
Mathlib defines the ring Kähler module to be J.Cotangent, with exactly this
formula for its universal derivation. The elements da span that module, so the
conjugate of e is the identity by linear-map extensionality on generators.
Consequently e(x) = e(y) implies x = y. This proof uses only the local diagonal,
and works for nonseparated f and for the zero ring of an empty affine chart. -/
theorem diagonalConormal_affine_lift_injective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(diagonalConormal f, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      D.d (X := op U.1) a) : Function.Injective e := by
  open CategoryTheory.Limits in
  open scoped TensorProduct in
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
  have hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W := by
    simp only [W, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]
    exact le_rfl
  obtain ⟨r, hr₂, hr₁, hlift⟩ := diagonalConormal_affine_ideal_class_core f U V hUV
  obtain ⟨c, hc⟩ := diagonalConormal_affine_ideal_class_q f U V hUV r hr₂ hr₁
  have hcd (a : Γ(X, U.1)) : c (CommRingCat.KaehlerDifferential.d a) =
      D.d (X := op U.1) a := by
    let j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1) :=
      ⟨(1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a - a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1)),
        KaehlerDifferential.one_smul_sub_smul_one_mem_ideal Γ(S, V.1) a⟩
    obtain ⟨s, hs⟩ := hlift j
    have hs' : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s =
          (pullback.snd f f).appLE U.1 W inf_le_right a -
            (pullback.fst f f).appLE U.1 W inf_le_left a := by
      rw [hs]
      change r (_ - _) = _
      rw [map_sub, hr₂, hr₁]
    exact (hc hδ j s hs).trans (hD U.1 W inf_le_left inf_le_right hδ a s hs').symm
  have hec : e = c.toLinearMap := by
    have h : ModuleCat.ofHom e = ModuleCat.ofHom c.toLinearMap := by
      apply CommRingCat.KaehlerDifferential.ext
      intro a
      exact (he a).trans (hcd a).symm
    exact congrArg (fun g ↦ g.hom) h
  rw [hec]
  exact c.injective

end AlgebraicGeometry
