# Finite operator span of unnormalized Jacquet block scalars

Author: Worker 345. Worker 186 contributed the exact statement specification
and its dependency route.

`Langlands.Parabolic.JacquetCenterSpanStatement.{uF,uV}` is a single closed
Prop-valued definition. This pair states the result and contains no proof of it.

## Quantifiers and actual actions

For every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData`, every natural rank `m`, every actual
`B : GeneralLinear.BlockShape m`, and every complex module `V : Type uV`,
let `ρ : Representation ℂ (GeneralLinear m F.Carrier) V`. The supplied
`T.topology` is installed before admissibility is stated. The field universe
`uF` and carrier universe `uV` are independent. There is no topology on `V`.

The hypotheses are exactly `IsAdmissible ρ` and
`Module.Finite (MonoidAlgebra ℂ (GeneralLinear m F.Carrier)) ρ.asModule`.
Thus finite type means finite generation over the actual ambient complex
group algebra. Admissibility includes smoothness and finite-dimensional
fixed spaces for every open subgroup, following the Library's convention.
The representation may be reducible and its underlying space may be infinite
dimensional. There is no scalar central-character hypothesis.

Write `P = B.parabolic F.Carrier`, `N = B.unipotentRadical F.Carrier`,
`ρP = ρ.comp P.subtype`, and

```text
Q = LeviCoinvariants B ρP
σ = leviCoinvariants B ρP.
```

Here `Q` is the actual radical coinvariant quotient of `V` by the complex
span of `ρP(u)v - v` for `u ∈ N`. The published action `σ` is the descended
quotient action restricted along the actual section `B.leviInParabolic`.
The representative formula `leviCoinvariants_mk` is

```text
σ(l)[v] = [ρ(B.leviEmbedding F.Carrier l)v].
```

For every tuple `a : Fin B.length → F.Carrierˣ`, the actual product-Levi
homomorphism `B.blockScalarLevi F.Carrier` puts the scalar matrix `a j` in
block `j`. The conclusion is exactly

```text
FiniteDimensional ℂ
  (Submodule.span ℂ (Set.range (fun a => σ (B.blockScalarLevi F.Carrier a))))
```

inside `Module.End ℂ Q`. It concerns all block-scalar tuples simultaneously.
No finite expansion, supplied action, substitute quotient, or pre-existing
finite-dimensional center action is an input. Every shape is retained,
including the empty shape at rank zero and one-block shapes; no positivity,
nonempty-shape or nonzero-carrier hypothesis is added.

## Normalization and the two-block use

The action in the conclusion is **unnormalized**: it sends a class to the
class of its actual translate. By comparison, `T.normalizedJacquet B ρ`
acts on the same quotient by multiplying this operator by
`δ_P(l)^(-1/2)`, with `δ_P = T.leviModulus B`. The inverse half-character is
`Jacquet.inverseHalfCharacter (T.leviModulus B)`. Relating these two
representations is a proof obligation, not an assumption of this statement.

For a two-block shape of sizes `(i,m-i)` with both blocks positive,
restrict the tuple to `(b,1)`. Its ambient matrix is
`diag(b I_i, I_(m-i))`. The span of these operators is contained in the
all-tuples span in the conclusion, so the conclusion implies finite operator
span for this one-coordinate action. The unnormalized representative formula
is the action needed for right translation and Whittaker coordinate dilation.
Constructing the map to the coordinate-germ quotient, checking its dilation
compatibility, and deriving a finite-function or Schwartz expansion are
separate downstream obligations.

## Derived provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212,
registered as `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The retained PDF is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
Proposition (2.2), its proof, Lemma (2.2.1), and Remark (2.2.5) on printed
pp.181–183 (one-based PDF pages 14–16) were read directly and visually.
No source-specific errata file was present in the supplied project or
Library `notes/errata` locations.

On p.181 the proof starts from a finite-dimensional span of action operators
and obtains a uniform finite-function expansion. Lemma (2.2.1) uses this
condition on each coordinate quotient. The application on pp.182–183 obtains
it from the Jacquet quotient for the parabolic of type `(i,r-i)`, then passes
to a quotient of that action. Remark (2.2.5) explicitly extends the conclusion
to finitely generated admissible translation-stable Whittaker-function
spaces, so irreducibility is not required for this prerequisite.

The present all-block-scalar formulation is an internal derived prerequisite,
not a verbatim theorem from those pages. Its rationale is that an admissible
finite-type Jacquet representation has a finite-dimensional space of
self-intertwiners, and every block-scalar operator belongs to that space.
It states the operator-span conclusion only, before any Whittaker-image
construction, character decomposition, or support argument.

## Exact dependencies of the future proof

The focused proof must discharge these steps on the actual actions:

1. Use `Langlands.Parabolic.normalizedJacquetFiniteGeneration` in
   `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`, with
   smoothness from admissibility, to obtain finite generation of
   `T.normalizedJacquet B ρ`.
2. Identify that representation with the inverse-half-character twist of
   the actual `σ`. Check the quotient and action identities using
   `GeneralLinear.BlockShape.normalizedJacquetOf_mk` or
   `PadicField.TopologicalData.normalizedJacquet_mk_eq_inv_halfModulus`,
   `leviCoinvariants_mk`, and surjectivity of the actual quotient map.
   Use `Langlands.finite_asModule_twist_iff` in
   `Langlands.Representation.RankinSelberg.WhittakerTypeTwist` to recover
   finite generation of the unnormalized `σ`.
3. Apply `Langlands.Parabolic.isAdmissible_leviCoinvariants` in
   `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`
   to this same `σ`. If the ambient-subgroup quotient presentation is used,
   `jacquetModuleEquiv_leviCoinvariants` in that module identifies its action
   with the actual product-Levi action; every such transport must be proved.
4. Lift `B.blockScalarLevi F.Carrier` to a homomorphism into
   `Subgroup.center (B.Levi F.Carrier)`, using
   `GeneralLinear.BlockShape.blockScalarLevi_commute`, and apply
   `Langlands.centralActionSpan_finite` from
   `Langlands.Representation.Smooth.CentralOperatorExpansionProof`.
   This helper requires admissibility and finite type of the actual Levi
   representation and gives exactly the operator span after the lift is
   unfolded. It needs no continuity hypothesis on the center-valued map.
   The full `Langlands.centralOperatorExpansion` theorem is available for
   a later uniform expansion, with its additional continuity premise.

These are dependencies and remaining proof obligations, not extra hypotheses
or claims proved by this pair. No new abstract action or mathematical
assumption may replace the normalization, quotient-action, or product-Levi
comparisons. Substantial new definitions or statements, if needed by that
proof, must be split into separately reviewed units first.
