# Statement: flatness and unramifiedness at a point where the analytification is finite

Authors: Worker 554 (proposal and Lean form), Worker 3519 (review, Markdown and
submission through parent Task 3519).

`AffineAnalytificationFiniteGermComparisonStatement` compares analytic and
algebraic flatness and unramifiedness at one point. It applies at points where
the analytified map is finite.

Let `K` be a complete, ultrametric, nontrivially normed field. Let `A` and `B`
be commutative `K`-algebras with finite polynomial presentations `P` and `Q`,
and let `f : A →ₐ[K] B`. Write `g := saturatedHom K P Q f` for the induced
morphism from the analytification of `B` to that of `A`. Fix a chart index
`m` and a point `s : BanachSpectrum (algebra K Q m)`. Let `y := chart K Q m s`
be the corresponding point of `Space K Q`, and let

`q := s.kernel.comap (PolynomialLocus.algebraMap Q (polyradius K Q.arity m))`

be the prime of `B` under `y`. This `q` is the center of `y`, that is, the
kernel of `pointSeminorm K Q y` (`AnalytificationCenter`). If `g.IsFiniteAt y`,
the statement asserts:

1. `g.IsUnramifiedAt y ↔ Algebra.IsUnramifiedAt A q`, where `B` is an
   `A`-algebra through `f`;
2. `g.IsFlatAt y ↔ (Localization.localRingHom (q.comap f) q f rfl).Flat`, that
   is, the local map `A_{f⁻¹(q)} → B_q` is flat.

Every point of `Space K Q` has the form `chart K Q m s`, because the charts
cover the space (`AffineAnalytificationGluing`). So the statement covers every
point at which `g` is finite.

This is a statement only; its proof is a separate successor. It is a
prerequisite proposed for the proof of `AffineAnalytificationEtaleStatement`
(Task 7169). Together with `AffineAnalytificationQuasiFiniteStatement` and the
surjectivity of the center map (`AnalytificationCenterStatement`, part (1)),
it reduces the three equivalences of that statement to algebra.

## Sources

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993). The
registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. PDF page =
printed page − 3.

- Proposition 3.2.10, printed p.60/PDF p.57: a morphism `φ : 𝒳 → 𝒴` between
  schemes of locally finite type over `Spec(𝒜)`, `𝒜` a `k`-affinoid algebra,
  is flat quasifinite if and only if `φᵃⁿ` is flat quasifinite. The proof
  works at one point `z` of `𝒳ᵃⁿ` over `y ∈ 𝒳`. Zariski's Main Theorem gives
  an open immersion of `𝒳` into a scheme finite over `𝒴`. Flatness of
  `𝒪_{𝒳,y}` gives flatness of a finite tensor product, and Proposition 2.6.10
  makes `𝒪_{𝒳ᵃⁿ,z}` a direct factor of it. The converse uses faithful
  flatness of the analytic local rings over the algebraic ones.
- Proposition 2.6.10, printed p.54/PDF p.51: the local finite tensor-product
  decomposition used above.
- Lemma 3.3.5 and Proposition 3.3.7, printed p.63/PDF p.60: for finite
  morphisms, unramifiedness at a point is the vanishing of the module of
  differentials at that point. The Library's `IsUnramifiedAtPoint` encodes this
  as "the annihilator of `Ω[S⁄R]` is not contained in the prime of the point".
- Proposition 3.3.11, printed p.64/PDF p.61: `φ` is unramified (resp. étale)
  if and only if `φᵃⁿ` is. The proof uses Corollary 3.3.7 and
  `Ω_{𝒳ᵃⁿ/𝒴ᵃⁿ} = (Ω_{𝒳/𝒴})ᵃⁿ`.

Berkovich 1990, *Spectral Theory and Analytic Geometry over Non-Archimedean
Fields*, registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:
Theorem 3.4.1(ii), printed p.63/PDF p.77, with the last paragraph of its
proof, printed p.64/PDF p.78. The map from the algebraic local ring to the
analytic local ring is flat, and the algebra of every affinoid domain of
`Spec(A)ᵃⁿ` is flat over `A`.

## Provenance

The formulation is derived. Berkovich states Propositions 3.2.10 and 3.3.11
globally, for morphisms that are flat quasifinite, unramified or étale
everywhere. Their proofs argue at a single point. This statement isolates that
pointwise comparison, under the hypothesis that `g` is finite at `y`. It is
stronger than the stated global equivalences, and a proof cannot simply cite
them. It must compare the actual finite affinoid pieces used by the Library's
`HasFinitePiecesAt` with the algebraic local rings at `q`.

The analytic predicates are the published ones:

- `StrongHom.IsFiniteAt` (`FullRecognitionFiniteMorphisms`): open
  neighborhoods `V` of `y` and `U` of `g y` with `g.IsFiniteOver V U`
  (Berkovich's Definition 3.1.1).
- `StrongHom.IsFlatAt` and `StrongHom.IsUnramifiedAt`
  (`FullRecognitionEtaleMorphisms`): `HasFinitePiecesAt` for the pointwise
  properties `IsFlatAtPoint` and `IsUnramifiedAtPoint` of
  `AffinoidPointwiseEtale`. This means open `V ∋ y` and `U ∋ g y` with
  `g.IsFiniteOver V U`, and finitely many recognized affinoid subsets of `U`
  containing `g y`, whose union is a neighborhood of `g y`, such that every
  finite affinoid piece over them has the property at every point over `y`.
  This is Berkovich's Definition 3.2.5 (printed p.59/PDF p.56) and
  Proposition 3.3.7(b) (printed p.63/PDF p.60).

The algebraic predicates are Mathlib's `Algebra.IsUnramifiedAt A q` (the
localization `B_q` is formally unramified over `A`) and `RingHom.Flat` of
`Localization.localRingHom`.

## Hypotheses

- `K : Type u` is a `NontriviallyNormedField` with `IsUltrametricDist K` and
  `CompleteSpace K`.
- `A : Type v` and `B : Type w` are commutative `K`-algebras in independent
  universes, with `P : FinitePolynomialPresentation K A` and
  `Q : FinitePolynomialPresentation K B`.
- `f : A →ₐ[K] B`, `m : ℕ` and `s : BanachSpectrum (algebra K Q m)` are
  arbitrary.
- The only hypothesis on the point is `g.IsFiniteAt y`. Both analytic
  predicates already contain finiteness at `y`, so without this hypothesis the
  forward implications would fail at points where `g` is not finite.

Zero algebras are allowed. If `B = 0`, there are no chart points and the
statement is vacuous.

## Why the claim is expected to hold

This is a truth check, not the proof. The analytic local ring of `Spec(B)ᵃⁿ`
at `y` is faithfully flat over `B_q`, and similarly for `A` at `g y`
(Berkovich 1990, Theorem 3.4.1(ii)).

- *Flatness.* Suppose `A_{f⁻¹(q)} → B_q` is flat. Shrink to affine
  neighborhoods and apply Zariski's Main Theorem, as in the proof of
  Proposition 3.2.10. Proposition 2.6.10 then gives flatness of the finite
  affinoid pieces at the points over `y`. Conversely, flatness of the pieces
  at `y` gives flatness of the analytic local rings, and faithfully flat
  descent along the analytic local rings gives flatness of
  `A_{f⁻¹(q)} → B_q`.
- *Unramifiedness.* The finite pieces have module of differentials obtained
  from `Ω[B⁄A]` by base change, as in the proof of Proposition 3.3.11. Its
  vanishing at the points over `y` is then equivalent, by faithful flatness,
  to `(Ω[B⁄A])_q = 0`. Since `B` is of finite type over `A`, this is
  unramifiedness at `q`.

## Scope

The statement concerns single points where `g` is finite. It does not assert
global faithful flatness of any one chart algebra over `A`, and it does not
treat points where `g` is not finite. Ground field extension and non-affine
schemes are not covered.
