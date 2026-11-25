/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineSections

/-!
# The diagonal comparison on affine sections

Source: Stacks Project, Tag 08S2, affine calculation; Tag 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The morphism induced by a normalized difference derivation is bijective on sections
of an affine open mapping into an affine open of the base.
Source: Stacks Project, Tag 08S2, final affine calculation, and Tag 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-comparison).
Proof: put `A = Γ(X,U)` and `R = Γ(S,V)`, with the algebra structure from `f.appLE`.
The ambient open `U ×_V U` is `Spec(A ⊗_R A)` and its inverse image under the diagonal
is `U` (Tag 01KJ). Restriction of the actual kernel sheaf to this open is the ideal of
that closed immersion, namely the kernel of multiplication. Tensor pullback commutes
with these restrictions, so the canonical affine conormal sections equivalence of
Tag 01R3 identifies sections of `diagonalConormal f` over `U` with `I/I²`, including
its class-map formula. The restriction, base-open and affine isomorphisms for relative
differentials identify its sections with `Ω[A/R]` and its universal derivation with `D`.
The normalization hypothesis and the universal-property evaluation formula imply that
our morphism sends `da` to the class of `1 ⊗ a - a ⊗ 1`. These elements generate
`Ω[A/R]`, so the whole map is the canonical identification of Tag 00RW. In Mathlib,
`KaehlerDifferential R A` is exactly the cotangent of the multiplication ideal, and
`KaehlerDifferential.D_apply` gives this formula. Conjugating this linear equivalence
by the two section identifications proves bijectivity. This argument needs only this
affine chart, and makes no claim about gluing or about global invertibility. -/
theorem diagonalConormalComparison_bijective_on_affine (f : X ⟶ S)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D) (U : X.affineOpens) (V : S.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Function.Bijective (((f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D).app
      U.1) := by
  obtain ⟨eΩ, heΩ⟩ := relativeDifferentials_affine_sections f U V hUV
  obtain ⟨eC, heC⟩ := diagonalConormal_affine_sections f U V hUV
  let φ := ((f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D).val.app
    (Opposite.op U.1)
  have h : eΩ.toModuleIso.hom ≫ φ = eC.toModuleIso.hom := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change φ (eΩ (CommRingCat.KaehlerDifferential.d a)) =
      eC (CommRingCat.KaehlerDifferential.d a)
    rw [heΩ a, heC D hD a]
    exact f.relativeDifferentialsHomEquiv_symm_app_d D a
  have hφ : (φ.hom : Γ(f.relativeDifferentials, U.1) → Γ(diagonalConormal f, U.1)) =
      eC ∘ eΩ.symm := by
    funext x
    have hx := ConcreteCategory.congr_hom h (eΩ.symm x)
    change φ.hom (eΩ (eΩ.symm x)) = eC (eΩ.symm x) at hx
    simpa only [eΩ.apply_symm_apply, Function.comp_apply] using hx
  change Function.Bijective (φ.hom : _ → _)
  rw [hφ]
  exact eC.bijective.comp eΩ.symm.bijective

end AlgebraicGeometry
