# Waldspurger's density `μ` of V.2 on actual data

Worker 5. This module defines the Plancherel density `μ` of J.-L.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082 (registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
In V.2, printed p.292 / PDF p.58, Waldspurger sets, for `ω` in the orbit
`O`,

`μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`,

where `α` runs over the reduced roots of `A_M` up to sign. Here `j` is the
function of IV.3, printed p.285 / PDF p.51. For `π'` in a nonempty Zariski
open subset of `O_C` where `I_P^G π'` is irreducible, the operator
`J_{P|P̄}(π') J_{P̄|P}(π')` is a homothety, and `j_P` is the rational
function on `O_C` whose value at `π'` is its ratio. IV.3(1) shows that
`j_P` does not depend on `P ∈ P(M)`, and `j = j_P`.

The definition is derived. It assembles two existing objects: the
constant `∏_α γ(M_α|M)` of `RationalPlancherelConstant`, and the
conditional rational scalar `conditionalCanonicalRationalScalar` of
`DynamicOppositeCanonicalScalar`. Both use the Haar measures normalized by
the same compact open subgroup `K`. This module proves elementary
properties of `μ`. It does not prove Lemma V.2.1 or the properties (1)–(6)
of `j` in IV.3 (see "Not proved here").

## Setting

The setting is that of `DynamicOppositeCanonicalScalar`. `F` is a
nonarchimedean local field. `G` is an affine group scheme over `F`,
locally of finite type, with `IsConnectedReductive G` as an explicit
hypothesis `hG` wherever the scalar is used. `T` is a commutative group
scheme with a homomorphism `i : T → G` (in the intended application, a
maximal split torus), `ζ` is a cocharacter of `T`, and `χ = ζ ≫ i`. The
parabolic is `P = P_G(χ)`, the opposite parabolic is `P̄ = P_G(χ⁻¹)`, and
both have the Levi subgroup `M = Z_G(χ)`. `K` is a compact open subgroup
of `G(F)`. The module re-enables, with `attribute [local instance]`, the
local instances of `DynamicOppositeCanonicalScalar`: the point topology on
`G(F)` and on the points of the centralizer scheme, the Hausdorff, locally
compact, nonarchimedean and second-countable structures, and the affine
and finite-type instances for the centralizer scheme. These are the
instances used in that module's statements.

The scalar depends on the explicit inputs of that module, which this module
passes through unchanged:

- the structural premises `hRefl : RelativeRootReflectionExistenceStatement`
  and `hCST : CentralSplitTorusCharacterStatement`;
- the factorizations `G(F) = P K` (`hPK`) and `G(F) = P̄ K` (`hOppK`);
- a smooth complex representation `A` of `M(F)`;
- whole-operator rational continuations `p : ForwardContinuation …` and
  `q : ReverseContinuation …` of the forward and reverse standard
  intertwining integrals in the compact picture;
- nonempty open sets `DForward` and `DReverse` inside the two full
  convergence domains;
- a nonempty open set `D` of unramified characters `z` of `M` at which the
  normalized induction from `P` of `A` twisted by `z` is irreducible
  (`hi`).

None of these inputs is constructed here.

## The constant `∏_α γ(M_α|M)²`

- `plancherelDensityConstant i ζ K hK` is the real number
  `(rankOneGammaProduct i ζ K hK).toReal ^ 2`. Here `rankOneGammaProduct`
  is the product `∏ᶠ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N`
  in `ℝ≥0∞` of `RationalPlancherelConstant`. It has one factor for each
  submodule `X_*(A_α)` with `α ∈ Σ_red(P)`. Each pair `±α` of reduced roots
  of `A_M` contains exactly one element of `Σ_red(P)`, so this set also
  indexes Waldspurger's product over the reduced roots up to sign.
- `plancherelDensityConstant_nonneg`: the constant is a square, so it is
  `≥ 0`.
- `one_le_plancherelDensityConstant` and `plancherelDensityConstant_pos`:
  if `rankOneGammaProduct i ζ K hK ≠ ⊤`, the constant is `≥ 1`, hence
  `> 0`. This uses `one_le_rankOneGammaProduct` (every factor is `≥ 1`).

The value `toReal ⊤ = 0` is a junk value. The finiteness hypothesis is
therefore stated explicitly in the last two results.

## The density

- `DensityField i ζ hG` abbreviates the Library's
  `rationalUnramifiedFunctionField` of the centralizer scheme
  `parameterScheme χ`: the fraction field of the regular functions on the
  unramified characters of `M(F)`. It is the field in which
  `conditionalCanonicalRationalScalar` takes its values.
- `fieldConstant i ζ hG c` is the complex number `c` as a constant
  element of this field, through `ℂ → regular functions → fractions`.
  `fieldConstant_ne_zero`: a nonzero constant is a nonzero element. The
  proof uses injectivity of the Library's map from regular functions to
  fractions and evaluates at the trivial character.
- **`plancherelDensity`** (arguments `i ζ hRefl hCST hG K hK hPK hOppK A p
  q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi`) is

  `fieldConstant (plancherelDensityConstant i ζ K hK) * j_P⁻¹`,

  with `j_P = conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK
  hOppK A p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi`. In a
  field `0⁻¹ = 0`, so `j_P = 0` gives `μ = 0`.
  `plancherelDensity_def` is the unfolding equation.

## Proved properties

- `plancherelDensity_mul_scalar`: if `j_P ≠ 0`, then
  `μ · j_P = ∏_α γ(M_α|M)²` (as a constant).
- `plancherelDensity_eq_zero_iff`: if the product is finite, then `μ = 0`
  exactly when `j_P = 0`.
- `plancherelDensity_continuation_independent`: `μ` is unchanged when the
  continuations `p`, `q` are replaced by any `p'`, `q'`. This is the
  Library's `conditionalCanonicalRationalScalar_continuation_independent`.
  It needs `DForward` and `DReverse` open.
- `plancherelDensity_irreducibility_locus_independent`: `μ` is unchanged
  when `D` is replaced by any nonempty set `D'` of the same irreducibility.
  This is `conditionalCanonicalRationalScalar_irreducibility_locus_independent`.
- `plancherelDensity_stabilizer_fixed`: translation by any element `τ` of
  the stabilizer of `π = SmoothRep.pullback (parameterHomeomorph χ) A`
  under unramified self-twists fixes `μ`. Translation fixes constants
  (`rationalUnramifiedFunctionFieldTranslation_constant`) and fixes `j_P`
  (`conditionalCanonicalRationalScalar_stabilizer_fixed`). So `μ`, a
  function on unramified characters, descends to the orbit of `π`, as
  Waldspurger's `μ` is a function on `O`.
- `plancherelDensity_spec`: there are regular functions `a`, `b` with
  `b ≠ 0`, `b(z) ≠ 0` for every `z` in the common regular region
  `R = p.regularRegion ∩ q.regularRegion`, such that
  `μ = ∏_α γ(M_α|M)² · (b / a)`, and for every `z ∈ R` the continued
  composite `conditionalContinuedComposite … z` (the reverse continued
  intertwiner `J_{P|P̄}` after the forward one `J_{P̄|P}`, on the
  normalized induction from `P` at `z`) is `(a(z) / b(z))` times the
  identity. This follows from the Library's
  `conditionalCanonicalRationalScalar_spec` (`j_P = a / b`) and
  `(a / b)⁻¹ = b / a`.
- **`conditionalContinuedComposite_eq_plancherelDensity_value`**: let
  `μ = m / n` with regular `m`, `n`, and let `z ∈ R` with `m(z) ≠ 0` and
  `n(z) ≠ 0`. Then the continued composite at `z` is
  `(∏_α γ(M_α|M)² · n(z) / m(z))` times the identity. This is the
  pointwise form `j_P(z) · μ(z) = ∏_α γ(M_α|M)²` of the definition, valid
  for any presentation of `μ` that is regular and nonzero at `z`.

  Proof: take `a`, `b` from `plancherelDensity_spec`. In the fraction
  field, `C · (b / a) = m / n` with `C = ∏_α γ(M_α|M)²`. Here `a ≠ 0`,
  since otherwise `m / n = 0`, which is impossible because `m` and `n` are
  nonzero (they do not vanish at `z`). Clearing denominators gives
  `m a = C b n` in the regular functions, by injectivity of the map to
  fractions. Evaluating at `z` gives `m(z) a(z) = C b(z) n(z)`. Hence
  `a(z) / b(z) = C n(z) / m(z)`.

The private lemmas `mul_eq_of_div_presentations`, `subalgebra_val_mul_eq`,
`ne_zero_of_val_ne_zero`, `div_eq_of_mul_eq` and `eq_smul_of_eq_smul` are
the steps of this proof, stated for an arbitrary ring with an injective
map to a field, for an arbitrary subalgebra of `ℂ`-valued functions, and
for complex numbers. They keep tactic steps off goals that contain the
large type of the induced representation.

## Not proved here

- Identification with Waldspurger's objects. Under the standard
  identifications (`T` the maximal split torus `A_0`, `K` the special
  maximal compact subgroup of I.1, `A` a square-integrable irreducible `ω`
  of `M(F)`, and `z ↦ A ⊗ z` the parameterization of `O_C`), the
  intended reading is that `conditionalCanonicalRationalScalar` is
  Waldspurger's `j_P` and `rankOneGamma … X_*(A_α)` is `γ(M_α|M)`. Then
  `plancherelDensity` is `μ`, pulled back from `O_C` to the unramified
  characters of `M`. Neither identification is proved in Lean; the
  Library's `DynamicOppositeCanonicalScalar.md` and
  `RationalPlancherelConstant.md` state the corresponding caveats.
- The properties of `j` in IV.3, printed pp.285–287 / PDF pp.51–53:
  independence of `P` (1), `j(π) = j(π̌)` (2), invariance under `W^G` (3),
  the product formula `j = ∏_α j_α` (5), and `j(π) ≠ 0` for
  square-integrable `π` (6). Waldspurger deduces Lemma V.2.1 from (2), (3),
  (5) and (6). Since (6) is not proved, the results above that need
  `j_P ≠ 0` take it, or a presentation of `μ` that is regular and nonzero
  at the point, as a hypothesis.
- Lemma V.2.1 (p.292): regularity of `μ` on `O`, `μ(ω) ≥ 0`, the product
  formula `μ^G = ∏_α μ_α`, `W^G`-invariance and `μ(ω̌) = μ(ω)`.
- Existence of the continuation data `p`, `q`, of the convergence sets and
  of the irreducibility locus `D`. These are explicit inputs.
- Finiteness of `∏_α γ(M_α|M)`. It is neither proved nor used here; the
  three results that need it take `rankOneGammaProduct i ζ K hK ≠ ⊤` as a
  hypothesis.
