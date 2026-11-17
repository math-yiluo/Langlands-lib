# Unitary archimedean Whittaker multiplicity one (Shalika 1974, Theorem 3.1)

Author: Worker 725 (Task 7297), revising the initial statement draft by Worker 779
(Task 7293).

This module states, without proof, continuous Whittaker multiplicity at most one for
unitary, topologically irreducible, admissible Hilbert representations of `GL_(n+1)(ℝ)`
and `GL_(n+1)(ℂ)`. It defines two `Prop`-valued declarations in the namespace
`Langlands.Archimedean` and proves nothing about them.

- `UnitaryWhittakerMultiplicityOneOver.{u} F` is the assertion over one field
  `F` with `[RCLike F]`.
- The entry proposition `UnitaryWhittakerMultiplicityOneStatement.{u}` is the
  conjunction `UnitaryWhittakerMultiplicityOneOver.{u} ℝ ∧
  UnitaryWhittakerMultiplicityOneOver.{u} ℂ`.

The helper is stated for any `RCLike` field so that its two cases share one text.
The entry proposition asserts only the real and complex cases. The universe `u` of
the representation space is a free level parameter.

## Exact content

Fix `F = ℝ` or `F = ℂ`, `n : ℕ` and a complex Hilbert space `E : Type u`
(`NormedAddCommGroup E`, `InnerProductSpace ℂ E`, `CompleteSpace E`). Let
`π : Langlands.GeneralLinear (n + 1) F →* (E →L[ℂ] E)` be a group homomorphism
from the actual matrix group `GL_(n+1)(F)` to the bounded complex-linear operators
on `E`. Assume the following.

1. `IsContinuousRepresentation π`: the action map `GL_(n+1)(F) × E → E` is jointly
   continuous.
2. `inner ℂ (π g v) (π g w) = inner ℂ v w` for all `g`, `v` and `w`. Since
   `π g⁻¹` is a two-sided inverse of `π g`, each `π g` is a unitary operator, so
   `π` is a unitary representation.
3. `IsTopologicallyIrreducible π`: `E` is nonzero, and every closed complex
   subspace stable under all `π g` is `0` or `E`.
4. `IsAdmissible π (unitaryCompact F (n + 1))`: for every continuous
   finite-dimensional matrix representation `τ` of the compact group
   `unitaryCompact F (n + 1)`, the space of linear maps `T : ℂ^d → E` with
   `T(τ(k)x) = π(k)(T x)` is finite-dimensional. The group
   `unitaryCompact F (n + 1)` is the full orthogonal group `O(n+1)` for `F = ℝ`
   and the unitary group `U(n+1)` for `F = ℂ`.

Let `ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter F` be a continuous,
nontrivial, circle-valued additive character of `F`. Let `ℓ₀` and `ℓ₁` be
complex-linear functionals on `smoothVectors (matrixModel F (n + 1)) π`, the
complex subspace of vectors whose orbit maps are real `C^∞` on the real Lie group
`GL_(n+1)(F)`. Assume both satisfy

```text
IsWhittakerFunctional (matrixModel F (n + 1)) π
  (Langlands.GeneralLinear.upperUnipotent (n + 1) F)
  (Langlands.Whittaker.standardCharacter ψ n) ℓ
```

That is, for every upper triangular unipotent `u` and smooth `v`,

```text
ℓ(π(u)v) = ψ(u₀,₁ + u₁,₂ + ⋯ + uₙ₋₁,ₙ) · ℓ(v),
```

and `ℓ` is continuous for the smooth-vector topology. By
`IsContinuousOnSmoothVectors`, this means that there are a finite set `S` of words
`[X₁, …, Xₖ]` in the real Lie algebra `Matrix (Fin (n+1)) (Fin (n+1)) F` and a real
constant `C` with

```text
‖ℓ(v)‖ ≤ C · ∑_{[X₁,…,Xₖ] ∈ S} ‖dπ(X₁) ⋯ dπ(Xₖ) v‖     for every smooth v.
```

The empty word gives the Hilbert norm `‖v‖`. Every `dπ(X)` is the derivative at
the identity of the orbit map, the Library's `lieDerivative`. For `F = ℂ` the
directions `X` range over complex matrices as a real vector space. This bound uses
the derivative seminorms of the smooth-vector topology. A bound by the Hilbert norm
alone, or `U`-equivariance without any continuity, is not what is assumed.

The conclusion is: if `ℓ₀ ≠ 0`, then `ℓ₁ = c • ℓ₀` for some `c : ℂ`. Equivalently,
the space of such Whittaker functionals has complex dimension at most one. No
existence of a nonzero Whittaker functional is asserted. Rank one (`n = 0`, the
group `GL_1(F)`) is included; there the unipotent subgroup is trivial and the
Whittaker condition reduces to continuity.

All objects are the existing Library ones from
`Langlands.Representation.Archimedean.SmoothVectors` (`IsContinuousRepresentation`,
`IsTopologicallyIrreducible`, `IsAdmissible`, `smoothVectors`,
`IsContinuousOnSmoothVectors`, `IsWhittakerFunctional`) and
`Langlands.Representation.Archimedean.GeneralLinear` (`matrixModel`,
`unitaryCompact`), together with `Langlands.GeneralLinear.upperUnipotent` and
`Langlands.Whittaker.standardCharacter`. The Lie group structure on
`GL_(n+1)(F)` is that of the units of the real Banach algebra of matrices with the
operator norm, as in `GeneralLinear`. The module therefore opens
`Matrix.Norms.Operator` and uses the same transparency option
`backward.isDefEq.respectTransparency false` as `GeneralLinear`. Without it the
chart instance on the units cannot be synthesized.

## Source

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2) 100
(1974), 171–193, registered as `shalika-1974-multiplicity-one`
(`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`).
The PDF page is the printed page minus 169.

The setup of §3 and Theorem 3.1 are on printed p.183 (PDF 14), and the proof runs
through printed p.185 (PDF 16). For archimedean `k`, Shalika regards
`G = GL_n(k)` as a real Lie group. `G⁰` is its identity component, `K` a fixed
maximal compact subgroup of `G⁰`, and `𝔊` the enveloping algebra `A(L)` of §2. On
printed p.179 (PDF 10), `A(L)` is the real universal enveloping algebra of
`L = Lie G`. `Ĝ` is the set of classes of unitary, admissible, irreducible
representations on a Hilbert space `𝔥`. `𝒟(Π)` is the span of the vectors `Π(f)v`
with `f ∈ C_c^∞(G)` and `v ∈ 𝔥`, and `𝔊` acts on it so that
`Π(Df) = −Π(D)Π(f)` for `D ∈ Lie(G)`. It is topologized by the seminorms
`‖v‖_D = ‖Dv‖` with `D ∈ 𝔊`. `𝒟'(Π)` is its space of continuous linear
functionals, with `G` acting by `(λ, Π(x)v) = (Π'(x⁻¹)λ, v)`. Then
`𝒟'_χ(Π) = {λ : Π'(u)λ = χ(u)λ for u ∈ U}`, where `U` is the upper triangular
unipotent group and `χ` is the fixed nondegenerate character of §1 (printed
pp.172–174, PDF 3–5). Theorem 3.1 states `dim_ℂ 𝒟'_χ(Π) ≤ 1` for all `Π ∈ Ĝ`.
The source retains the hypotheses unitary, admissible and irreducible, and this
statement keeps all three. Theorem 3.1 also covers non-archimedean `k`. That case
is not part of this module; the Library proves it separately as
`Langlands.Whittaker.localFieldMultiplicityOne`.

The Lean statement differs from the source in four points of presentation. A proof
must justify them; the module proves none of the facts used below.

1. **Gårding space versus all smooth vectors.** Shalika's functionals live on the
   Gårding space `𝒟(Π)`, the Lean functionals on all smooth vectors. Every
   `Π(f)v` is a smooth vector. On such vectors Shalika's `Π(X)`, `X ∈ Lie(G)`, is
   the derivative `d/dt Π(exp tX)v` at `t = 0`, which is the Library's
   `lieDerivative` (the sign in `Π(Df) = −Π(D)Π(f)` comes from `D` acting on `f` as
   a right-invariant vector field). So the restriction of a Lean Whittaker
   functional to `𝒟(Π)` is continuous for Shalika's seminorms and has the same
   `U`-equivariance. By Gårding's theorem, `𝒟(Π)` is dense in the smooth vectors
   for the derivative-seminorm topology. Hence a nonzero `ℓ₀` restricts to a
   nonzero functional, and `ℓ₁ − c • ℓ₀` vanishes once it vanishes on `𝒟(Π)`.
   Theorem 3.1 together with this density therefore implies the Lean conclusion.
   This density result is not proved here.
2. **Enveloping-algebra seminorms versus real Lie words.** Each `D ∈ 𝔊` is a finite
   real linear combination of products `X₁⋯Xₖ` with `Xᵢ ∈ Lie(G)`, acting as
   `dπ(X₁)⋯dπ(Xₖ)`. So each seminorm `‖Dv‖` is bounded by a finite sum of word
   seminorms, and each word seminorm is one of Shalika's seminorms. Continuity for
   either family therefore means the same finite bound as in
   `IsContinuousOnSmoothVectors`. This is the convention explained in the
   Markdown of `SmoothVectors`.
3. **Compact subgroup in the real case.** Shalika's `K` is a maximal compact
   subgroup of the identity component `G⁰`. For `GL_n(ℝ)`, `G⁰` consists of the
   matrices of positive determinant, and `K` is a `G⁰`-conjugate of `SO(n)`. The
   Lean statement uses the full orthogonal group `O(n)`. Admissibility does not
   change under conjugation by `π(g)`. `SO(n)` has index two in `O(n)`, so the two
   admissibility conditions are equivalent. Restricting a continuous representation
   of `O(n)` to `SO(n)` gives a finite sum of irreducibles. Conversely, Frobenius
   reciprocity for the finite-dimensional induced representation from `SO(n)` to
   `O(n)` identifies the `SO(n)`-intertwiners with `O(n)`-intertwiners from the
   induced representation. For `GL_n(ℂ)`, `G⁰ = G` and `U(n)` is a maximal compact
   subgroup, so nothing changes. This comparison is not proved here.
4. **Inverse-character convention.** Shalika's condition `Π'(u)λ = χ(u)λ` refers
   to the dual action `(λ, Π(x)v) = (Π'(x⁻¹)λ, v)`. It therefore means
   `λ(Π(u)v) = χ(u)⁻¹ λ(v)`. The Lean predicate is the covariant identity
   `ℓ(π(u)v) = ψ(∑ uᵢ,ᵢ₊₁) ℓ(v)`. A Lean functional for `ψ` thus lies in Shalika's
   `𝒟'_χ(Π)` for `χ(u) = ψ(−∑ uᵢ,ᵢ₊₁)`. This character has all coefficients
   `aᵢ = −1 ≠ 0` and so is nondegenerate in the sense of printed p.174 (PDF 5).
   The Lean statement covers only the standard characters `ψ(∑ uᵢ,ᵢ₊₁)` for
   arbitrary `ψ`. Shalika's theorem covers every nondegenerate `χ`, and the
   diagonal torus acts transitively on these characters (printed p.174).

No Shalika errata file was found in the project, the Library or its notes.

## What this statement does not provide

This is the local archimedean input that Shalika's global argument uses. It does
not by itself prove the global targets
`Langlands.Automorphic.CuspidalWhittakerModelComparisonStatement` or
`Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement`. Those targets
concern actual cusp functions with finite-adelic, compact and Lie-algebra
operators. The published reduction
`Langlands.Automorphic.CuspidalOperatorUnitaryMultiplicityOneReduction` already
reduces the latter to unitary central characters. Applying the present local
statement would still require the following.

- A unitary Hilbert realization of each archimedean component, with continuity,
  irreducibility and admissibility established.
- An extension of an algebraic operator equivalence to these realizations, such
  that transported Whittaker functionals still satisfy a derivative-seminorm
  bound.
- Such a bound for the actual cusp Whittaker functional, as in Shalika's
  Lemma 5.6 (printed pp.187–188, PDF 18–19).
- The restricted tensor-product and factorization argument of Shalika's
  Theorem 4.5 and Theorem 5.5 (printed pp.186–188, PDF 17–19), combining the
  archimedean and non-archimedean local uniqueness results.

Uniqueness of arbitrary algebraic Whittaker functionals on Harish-Chandra modules
is a different assertion and is not claimed here.
