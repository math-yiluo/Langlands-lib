# Proof of rational invertibility with a uniform kernel annihilator

`Langlands.CommGroupScheme.isogenyInverse` proves the exact proposition
`Langlands.CommGroupScheme.IsogenyInverseStatement`. For a scheme `S`,
commutative group schemes `G` and `H` over `S`, and `f : G ⟶ H` whose
underlying scheme morphism `p` is finite, flat, and surjective, with one
integer `n ≠ 0` such that multiplication by `n` on the scheme kernel of `f`
is the zero homomorphism, it shows that the image of `f` in the
rationalization is an isomorphism. The proof descends multiplication by `n`
along `p` to a homomorphism `g : H ⟶ G`. Both composites of `f` and `g` are
multiplication by `n`, so `(1/n) ⊗ g` inverts `1 ⊗ f`.

## Helper declarations

The supporting results live in the namespace `Langlands.GroupScheme`. They
are stated for group objects `G H : Grp (Over S)`. Commutativity instances
are assumed only where a result uses them.

- `IsIsogeny.effectiveEpi`: if `f` is an isogeny, its underlying scheme
  morphism is an `EffectiveEpi`. A finite morphism is quasi-compact. Mathlib's
  instance in `Mathlib.AlgebraicGeometry.Sites.Fpqc` then makes every
  quasi-compact, surjective, flat morphism of schemes an effective
  epimorphism. Mathlib proves that instance from the fact that representable
  presheaves are fpqc sheaves.
- `IsIsogeny.tensorHom` and `IsIsogeny.epi_tensorHom`: the underlying scheme
  morphism of `f ⊗ₘ f` in `Over S` is the induced map of fiber products over
  `S`. It again satisfies the isogeny property, by
  `MorphismProperty.pullbackMap` and the published stability instances for
  `isogenyProperty` in `Langlands.AbelianScheme.IsogenyStability`. Hence it
  is an epimorphism of schemes, and `Over.epi_of_epi_left` makes
  `f ⊗ₘ f` an epimorphism in `Over S`.
- `multiplication_comp_eq_of_comp_eq` assumes `G` commutative and
  `multiplication (kernel f) n = 1`. It shows that any two scheme morphisms
  `a b : Z ⟶ G` with `a ≫ p = b ≫ p` satisfy
  `a ≫ [n]_G = b ≫ [n]_G` on underlying schemes. Both `a` and `b` are
  viewed as morphisms over `S` from the same object `Z → S`. Their quotient
  `a / b` in the group of such morphisms is sent to `1` by `f`. The
  published pullback square `kernel_isPullback f` therefore factors it as
  `k ≫ ι` through the kernel inclusion `ι`. Then
  `(a / b) ^ n = (k ≫ [n]_K) ≫ ι = 1`, using `points_multiplication` and
  the hypothesis. Commutativity gives `a ^ n = b ^ n`, which is
  `a ≫ [n]_G = b ≫ [n]_G`.
- `descentHom`, `fac_descentHom`: `EffectiveEpi.desc` applied to the
  previous lemma gives a scheme morphism `H → G`. Composed with `p` it
  equals the underlying morphism of `[n]_G`.
- `descentOver`, `comp_descentOver`: this morphism lies over `S`. The check
  cancels the epimorphism `p`, using that `[n]_G` and `p` both lie over
  `S`.
- The `IsMonHom` instance for `descentOver`: the unit law follows from the
  unit laws of `f` and `[n]_G`. The multiplication law follows by cancelling
  the epimorphism `f ⊗ₘ f`, from the multiplication laws of `f` and `[n]_G`.
- `descent` is the resulting group-scheme homomorphism `H ⟶ G`.
  `comp_descent` states `f ≫ descent = multiplication G n` and needs only
  `G` commutative. `descent_comp` states
  `descent ≫ f = multiplication H n`. Its proof cancels `p` and uses
  `multiplication_naturality f n`.

## Main theorem

Let `g` be `descent` regarded as a morphism of `CommGroupScheme S`. The
additive structure on homomorphisms is the `Additive` wrapper of the
pointwise group structure. By definition, `multiplication G n` is the
`n`-th power of `𝟙 G` there. Hence `f ≫ g = n • 𝟙 G` and
`g ≫ f = n • 𝟙 H`. The rationalized morphism `(n : ℚ)⁻¹ ⊗ₜ g` is the
inverse. By `Rationalization.comp_tmul`, the composite with
`Rationalization.inclusion.map f = 1 ⊗ₜ f` in either order is
`(n : ℚ)⁻¹ ⊗ₜ (n • 𝟙)`. Moving the integer across the tensor product gives
`(n * n⁻¹ : ℚ) ⊗ₜ 𝟙`, which is the rational identity since `n ≠ 0`.

## Provenance

This is an internal proof of the imported statement. It uses the imported
definitions, the published isogeny stability results, and Mathlib. It
follows the intended argument recorded in the statement's Markdown. That
argument rests on fpqc descent of morphisms (Stacks Project, *Descent*,
Lemma 13.7, Tag `023Q`) and on the quasi-inverse construction of
Edixhoven, van der Geer, and Moonen, *Abelian Varieties*, Proposition
(5.12); exact locations are recorded there. In the Lean proof, descent
enters only through Mathlib's `EffectiveEpi` instance for quasi-compact,
surjective, flat morphisms of schemes. No descent on base changes is used.
The multiplication law is checked by cancelling the epimorphism `f ⊗ₘ f`,
and the remaining identities by cancelling `p`. No additional hypotheses,
chosen inverses, or axioms are introduced.
