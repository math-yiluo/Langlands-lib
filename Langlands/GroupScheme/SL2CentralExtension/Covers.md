# Fppf covers adjoining roots and inverting polynomials

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1). Conrad's proof uses fppf-local choices of units and roots
(for example a unit `t` with `t² - 1` a unit). This module provides them in the language of
`Loc` from `Local`. It has no separate literature source.

## Contents

- `ring g`: for `g : V ⟶ T` in `Over S`, the ring map `Γ(T.left, ⊤) →+* Γ(V.left, ⊤)` on global
  sections, with `ring_comp` and `ring_comp_apply` (restriction along a composite is the
  composite of restrictions, by `rfl`).
- `Nondeg f`: a polynomial `f : A[X]` is nowhere degenerate if `f ∉ P·A[X]` for every prime
  ideal `P` of `A`. Equivalently, its coefficients generate the unit ideal. Closure
  properties: `Nondeg.of_coeff` (a unit coefficient), `Nondeg.of_coeff₂`
  (`a·cᵢ + b·cⱼ = 1` for two coefficients), `Nondeg.mul`, `Nondeg.map` (under any ring map) and
  `Nondeg.monic`.
- `localizationAway_faithfullyFlat`: if `f` is nowhere degenerate, then `A → A[X][1/f]` is
  faithfully flat. The ring is flat as a localization of a polynomial ring. For surjectivity on
  spectra, take a prime `P` of `A`. The prime `P·A[X]` misses every power of `f`, so it extends
  to a prime of `A[X][1/f]` lying over `P`.
- `adjoinRoot_faithfullyFlat`: adjoining a root of a monic polynomial, of positive degree when
  `A` is nontrivial, is faithfully flat. If `A` is nontrivial, `AdjoinRoot p` is free and
  `A → AdjoinRoot p` is injective. If `A` is the zero ring, the map is bijective.
- `Loc.of_algebra`: over an affine test scheme `T`, a faithfully flat finitely presented ring map
  `φ : Γ(T.left, ⊤) ⟶ B` gives fppf-locally a factorization `φ ≫ ψ = g.left.appTop` of the
  restriction map. The cover is `Spec B → T.left`.
- `Loc.exists_isUnit_eval`: for a nowhere degenerate `f` over `Γ(T.left, ⊤)`, fppf-locally on
  `T` there is `r` with `f(r)` a unit. The cover is `Spec` of `A[X][1/f]`, on affine pieces.
- `Loc.exists_root`: for a monic `p` of positive degree over `Γ(T.left, ⊤)`, fppf-locally on `T`
  there is a root of `p`. The cover is `Spec` of `AdjoinRoot p`, on affine pieces.
