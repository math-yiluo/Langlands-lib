# Uniform-region recurrence for powers of a bounded coordinate dilation (statement)

Authors: Worker 941 (draft), Worker 1121 (check and submission). This unit states one derived step used inside the proof of
JPS (1979), Lemma (2.2.1), printed pp.181–182. The powers of one bounded
coordinate dilation satisfy one scalar linear recurrence, pointwise on a whole
small-coordinate region. It uses the actual function spaces, coordinate
actions and coordinate-germ quotients published in
`Langlands.Representation.Whittaker.JPSFunctionSpace`. It is a proposition
definition only. Nothing here proves the assertion.

## Declaration

`Langlands.Whittaker.JPSBoundedDilationRecurrenceStatement.{uF} : Prop`, in
module `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`.
The module imports only `Langlands.Representation.Whittaker.JPSFunctionSpace`
and opens the namespace `Langlands.Whittaker.JPSFunctionSpace`. Its only
universe parameter is the unrestricted field universe `uF`. The proposition
is, in this exact order:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
  HasFiniteCoordinateOperatorSpan W T i →
  ∀ c : F.Carrierˣ, T.normalizedAbs (c : F.Carrier) ≤ 1 →
    ∃ (D : ℕ) (d : ℕ → Fin D → ℂ),
      ∀ f : W.toSubmodule,
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (m : ℕ) (a : Torus F n),
            T.normalizedAbs (a i : F.Carrier) < δ →
              (coordinateRepresentation W i (c ^ m) f).val a =
                ∑ j : Fin D, d m j * (coordinateRepresentation W i (c ^ (j : ℕ)) f).val a
```

## Quantifiers

The prime `p`, the field `F`, the topological data `T`, the rank `n : ℕ` (zero
included), the space `W` and the coordinate `i : Fin n` are universally
quantified. At `n = 0` the type `Fin 0` is empty, so the statement holds
vacuously at rank zero.

The only hypothesis on `W` is the published
`HasFiniteCoordinateOperatorSpan W T i`. Local constancy, smoothness of `σ_i`
and finite-dimensionality of `W` or of its quotient are not assumed. Then a
unit `c` with `T.normalizedAbs (c : F.Carrier) ≤ 1` is quantified. Its powers
`c ^ m`, `m : ℕ`, are the nonnegative powers in the unit group.

The conclusion has the exact order `∃ D d, ∀ f, ∃ δ > 0, ∀ m a, |a_i| < δ → …`:

- The length `D` and the coefficients `d m j` (for `m : ℕ` and `j < D`) are
  chosen before every `f`. They depend only on `W`, `i` and `c`. So one scalar
  coefficient family serves every function in `W`.
- The threshold `δ` may depend on `f`. It comes before every power `m` and
  the whole torus tuple `a`, including all coordinates other than `i`.
- For all these `m` and `a` with `|a_i| < δ`, the value of `ρ_i(c ^ m) f` at `a`
  is `∑_{j < D} d m j · (ρ_i(c ^ j) f)(a)`. By `coordinateRepresentation_apply`,
  the left side is `f (a · e_i(c ^ m))` and the summands are
  `f (a · e_i(c ^ j))`, where `e_i` is `coordinateEmbedding i`.

So on the one region `|a_i| < δ`, each function `m ↦ f (a · e_i(c ^ m))` is a
fixed linear combination, with coefficients independent of `a` and `f`, of its
first `D` values. A threshold chosen separately for each `m` or for each tuple
of other coordinates does not meet the statement.

The statement does not require `d` to be given by a linear recurrence of
order `D`, nor `d m j` to be the Kronecker delta for `m < D`. Any coefficient
choice that meets the pointwise identity on a uniform region suffices. The
expected proof obtains such a recurrence anyway; see Source provenance.

## Actual spaces, actions and quotients

Every object is the published one from `Langlands.Whittaker.JPSFunctionSpace`,
used without change.

- `Torus F n` is `H = Fin n → F.Carrierˣ` under pointwise multiplication.
  `FunctionSpace F n` is an actual complex space `W` of functions `H → ℂ`,
  stable under translations. Elements are `f : W.toSubmodule` with underlying
  function `f.val`.
- `coordinateRepresentation W i` is the source's `ρ` on the `i`-th factor
  `H_i ≅ Fˣ`. By `coordinateRepresentation_apply`,
  `(coordinateRepresentation W i b f).val a = f.val (a * coordinateEmbedding i b)`.
  It is a group representation, so `ρ_i(c ^ m) = ρ_i(c) ^ m`.
- `HasFiniteCoordinateOperatorSpan W T i`: the complex span of the range of
  `sigma W T i` in `Module.End ℂ (CoordinateGerm W T i)` is
  finite-dimensional. Here `CoordinateGerm W T i` is the quotient of `W` by
  `coordinateVanishing W T i` (functions vanishing on a uniform region
  `|a_i| < ε`), and `sigma W T i` is the action of `F.Carrierˣ` induced by `ρ_i`.
  This span is the source's finite algebra `𝒜_i`.

The quotient and `sigma` occur only through this hypothesis. The conclusion
is a pointwise identity of actual functions on `H`.

## Normalized absolute value and topology

`|x|` is `T.normalizedAbs x`, the residue-cardinality normalization of `T`: `0`
at `0` and `q ^ (-T.ord x)` at `x ≠ 0`, with `q = T.residueCardinality`. For a
unit `c`, `|c| ≤ 1` says that `c` is integral. The main case is the uniformizer
unit `Langlands.LocalFactor.PadicAbelian.uniformizerUnit T` of the published
module `Langlands.LocalField.Uniformizer`, with `|ϖ| = q⁻¹`; norm-one units are
allowed too. Another normalization would rescale `δ` by a
positive power and leave the statement unchanged.

The restriction `|c| ≤ 1` is what makes the region uniform: for `|c| ≤ 1` and
`|a_i| < δ`, the point `a · e_i(c ^ s)` again has `i`-th coordinate of
absolute value below `δ`. The statement makes no claim for `|c| > 1`.

No topology occurs in the statement. `HasFiniteCoordinateOperatorSpan` and
`coordinateVanishing` use only `T.normalizedAbs`, so the body does not install
`T.topology`.

## Source provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212. Registered source
`jps-1979-gl3-i`, file SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`. Printed
pp.181–182 are one-based PDF pp.14–15.

This is a derived intermediate statement, not a displayed statement of the
source. Its sources are these:

- Printed p.181, the remarks opening the proof of Proposition (2.2): every
  element of the finite algebra `𝒜` spanned by the `σ(a)` satisfies a
  polynomial equation. Applied to `σ_i(c)`, the powers `σ_i(c ^ m)` lie in the
  span of finitely many lower powers. This gives `D` and `d`, uniform in `f`,
  as an identity of operators on the quotient.
- Printed p.182, proof of Lemma (2.2.1): for a given `φ` one finds a last
  coordinate value (the source's `c`, a small field element, not the unit `c`
  of this statement) so small that the expansion holds "for any `b` with
  `|b| ≤ 1`, any `a_i`'s". Getting
  one region for all `|b| ≤ 1` needs exactly this step: the operator identity
  on the quotient only gives, for each separate `m`, a threshold depending on
  `m`. The statement asserts one threshold for all `m`.

The task contract of
`Langlands.Whittaker.JPSUniformDilationStatement`'s proof task
(`16738e59-6235-4345-be5e-361e76c577ca`) names this "uniform-region
recurrence for powers of a uniformizer" as a separate prerequisite. The
statement is made for any bounded unit `c` rather than only a uniformizer. The
proof is the same, and the uniformizer case is an instance.

No source-specific erratum was found in the project literature index, the
Library notes or `/home/taskhub/central-library`.

## Status

Statement only. The expected proof: the ascending chain of spans of
`σ_i(c ^ j)`, `j < d`, in the finite-dimensional operator span stabilizes,
which gives `D` and `d`. For one `f`, the germ relation at `m = D` gives a
threshold below which the lifted relation vanishes. Bounded dilations
preserve vanishing below that threshold, so every `ρ_i(c ^ m) f` is in the
span of the first `D` powers plus functions vanishing below it. The span of
the first `D` powers meets `coordinateVanishing W T i` in a finite-dimensional
space, which has one common threshold.
