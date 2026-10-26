# Affine quotient presentation of the roots-of-unity kernel

Author: Worker 690. Worker 407 proposed the comparison on all test schemes.
The spectrum-map compatibility and the pattern for the relative universal
property come from Worker 487's published `MultiplicativeLaurent` module.

`Langlands.GroupScheme.muAffinePresentation.{u}` proves the unchanged Library
proposition `Langlands.GroupScheme.MuAffinePresentationStatement.{u}`:

```lean
∀ (A : CommRingCat.{u}) (n : ℕ), 0 < n →
  Nonempty ((mu (Spec A) n).X ≅
    Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1))))))
```

The isomorphism lies in `Over (Spec A)` and therefore preserves the specified
structural morphism. The base ring is arbitrary, including the zero ring, and
the universe `u` is unrestricted. The only numerical hypothesis is `0 < n`;
there is no assumption that `n` is invertible. The kernel `mu` is the existing
torsion kernel of the published multiplicative group scheme.

## Implemented proof

The helper declarations are in `Langlands.GroupScheme.MuAffinePresentation`.
`equation A n` abbreviates `X^n - 1`. `model A n` is exactly the spectrum of
`AdjoinRoot (equation A n)` with the canonical coefficient structural map.

First, `root_pow` specializes `AdjoinRoot.eval₂_root` to prove that the
quotient coordinate has `n`-th power one. `coordinate A n hn` promotes it to
a root of unity using `Units.ofPowEqOne`. Positivity is used here: the inverse
is the `(n-1)`-st power of the coordinate. This argument works in every
commutative ring.

For every `T : Over (Spec A)`, `roots n hn T` pulls back this coordinate
along a morphism `T ⟶ model A n`. It uses `Gm.specHomEquiv` to turn the
underlying scheme morphism into a ring map to `Γ(T.left, ⊤)`, then applies
`restrictRootsOfUnity`. `roots_val` identifies its underlying section with
the image of the quotient coordinate. `roots_comp` proves naturality for
every morphism of test schemes, with the map on global sections.

Conversely, `eval_equation` shows that a root of unity annihilates `X^n - 1`
under any coefficient ring map. `lift n T ζ` uses `AdjoinRoot.lift` to
evaluate the quotient at the underlying section of `ζ`. Its coefficient map
is fixed by `Gm.specHomEquiv T.left A T.hom`. The identity
`AdjoinRoot.lift_comp_of`, together with `Gm.specHomEquiv_specMap`, proves
that the resulting scheme morphism is over `Spec A`.

`roots_lift` evaluates the quotient coordinate to prove one inverse
identity. `lift_roots` uses `AdjoinRoot.ringHom_ext` for the other: equality
on coefficients follows from `Over.w x`, and equality on the adjoined root
follows from `AdjoinRoot.lift_root`. These identities give `homEquiv`,
a bijection between maps into `model A n` and roots of unity in the global
sections of each test scheme.

`comparison` composes the existing `mu.pointsEquiv` with the inverse of
`homEquiv`. `comparison_comp` proves its naturality using
`mu.pointsEquiv_naturality` and `roots_comp`. Finally, `iso A n hn` invokes
`CategoryTheory.Yoneda.ext` in the category `Over (Spec A)`, and the exported
theorem packages this isomorphism in `Nonempty`.

The test schemes in this argument are arbitrary. No affine-point density
claim or restriction to affine test objects is used. The proof preserves
the accepted statement pair and its imports. It does not assert compatibility
with group laws, finiteness, flatness, étaleness, or a monodromy comparison.

## Sources and provenance

The mathematical presentation is the one in the Stacks Project,
[Example 39.5.2, Tag 040M](https://stacks.math.columbia.edu/tag/040M).
The quotient construction also specializes the algebra `A[T]/(T^n-a)` in
the proof of [Lemma 59.28.1, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
to `a = 1`. The latter lemma's invertibility assumption on `n` concerns its
étaleness and exactness conclusions; those conclusions are outside this proof.
Its retained comments explicitly specify positive natural numbers.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter III, Examples 2–3, printed p.32 (PDF p.36), supplies the construction
provenance for the global-units functor and its roots-of-unity subgroup.
The implemented argument uses the Library's existing kernel construction
and a direct quotient universal property, followed by Yoneda.

The retained sources read for this contribution are:

- `stacks-mu-finite-etale-2026-10-23`, in
  `literature/Stacks Project - Roots of unity and the Kummer finite etale calculation (2026-10-23)/`.
  The complete `040M.html` and `03PL.html`, including comments, were read.
  Their SHA256 values are
  `4dc450e8ae44698c605f1d8a8a3a637ccfcbb069d2599dc0385d123a2954fdbc`
  and `a71ef76e1123074b4e38b89a72307a4c7fd8f1ecf7e99fcf94040f5ed03b5773`.
- `edixhoven-vandergeer-moonen-abelian-varieties-draft`, in
  `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`,
  SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  PDF p.36 was read.

No source-specific project errata note for these two registered sources was
found on 26 October 2026. The helper constructions are derived from Mathlib's
`AdjoinRoot` universal property, the published `Multiplicative` and
`MultiplicativeLaurent` APIs, and Mathlib's Yoneda lemma.
