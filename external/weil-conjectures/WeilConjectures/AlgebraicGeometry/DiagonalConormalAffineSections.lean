/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsBase
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSectionsUnique

/-!
# Normalized diagonal conormal sections on an affine chart

Source: Stacks Project, Tags 01KJ, 01R3, 08S2 and 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The diagonal conormal on an affine chart is the ring's Kähler differential module.
Every normalized difference derivation has the expected formula in these coordinates.
Source: Stacks Project, Tag 08S2, affine calculation; Tags 01KJ, 01R3 and 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-sections).
Proof: set `A = Γ(X,U)` and `R = Γ(S,V)`. The open `U ×_V U` in `X ×_S X` is
`Spec(A ⊗[R] A)`, and its inverse image under the diagonal is exactly `U` (Tag 01KJ).
The diagonal restricted to this open is closed, with ideal the kernel of
multiplication `A ⊗[R] A → A`. Restriction of the actual module-sheaf kernel agrees
with this ideal sheaf: restriction preserves kernels and the diagonal pushforward
restricts to the pushforward of the restricted diagonal. Tensor pullback commutes
with these restrictions. Apply `Scheme.Modules.affine_conormal_sections` to this
closed diagonal, obtaining the canonical identification of conormal sections with
`I/I²`, including its formula on ideal sections. In Mathlib `KaehlerDifferential R A`
is this cotangent quotient; its `A`-action is the quotient action through
multiplication. Hence the identification is `A`-linear. For `a ∈ A`, the ambient
section `1 ⊗ a - a ⊗ 1` belongs to the multiplication kernel, so it gives an ideal
section. The class-map formula of the affine conormal equivalence and the defining
normalization of any `D` identify its image with `D.d a`. Finally
`KaehlerDifferential.D_apply` identifies its cotangent class with `d a`. The chart
and the equivalence depend only on `f,U,V`, and this argument applies to every
normalized `D`. No global closed-immersion hypothesis on the diagonal is needed. -/
theorem diagonalConormal_affine_sections (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) ≃ₗ[Γ(X, U.1)]
        Γ(diagonalConormal f, U.1),
      ∀ (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf),
        IsDiagonalConormalDerivation f D → ∀ a : Γ(X, U.1),
          e (CommRingCat.KaehlerDifferential.d a) = D.d (X := op U.1) a := by
  obtain ⟨D₀, hD₀⟩ := exists_diagonalConormalDerivation f
  obtain ⟨e, he⟩ := exists_diagonalConormal_affine_sections_base f U V hUV D₀ hD₀
  refine ⟨e, ?_⟩
  intro D hD a
  rw [he]
  exact (diagonalConormal_affine_sections_unique f U.1 D₀ D hD₀ hD a)

end AlgebraicGeometry
