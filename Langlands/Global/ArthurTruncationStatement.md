# Statements on Arthur's truncation operator

Module `Langlands.Global.ArthurTruncationStatement`, namespace
`Langlands.Global.ArthurTruncation`. The objects are those of
`Langlands.Global.ArthurTruncation` (see its Markdown). The module defines one predicate,
`IsTruncationIdempotent`, states four propositions and their conjunction
`ArthurTruncationStatement`. It proves none of them.

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):
  §4, p.24 (the choice of `K`), §13, p.68 (finiteness of the inner sum), Proposition 13.1
  (pp.68–69) and Proposition 13.3 with (13.10) (pp.73–74).
- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I`, §5, Lemma 5.1: for a parabolic `P` there
  are `c`, `N` with `∑_{δ ∈ P(ℚ)\G(ℚ)} τ̂_P(H(δx) − X) ≤ c (‖x‖ e^{‖X‖})^N`; "in particular, the
  sum is finite".
- J. Arthur, *The trace formula in invariant form* (1981), registered as
  `arthur-1981-trace-formula-invariant-form` (Arthur 2005's [A5]), §1, pp.9–10: maximal compact
  subgroups admissible relative to `M_0` and their properties (i)–(iii).
- E. Lapid (2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2,
  p.312, for the setting `G(F) \ G(𝔸)` over a number field.

## Common hypotheses

Each statement quantifies over a universe `u`, a number field `F : Type u`, a group scheme `G`
over `Spec F` with `hG : IsConnectedReductive G`, a maximal split torus `i : T ⟶ G` (`hi`), a
generic cocharacter `ν` (`IsGenericCocharacter i ν`, fixing `P_0`) and reflection data `D`. The
instance arguments `IsAffineHom`, `LocallyOfFiniteType` and `Mono` are propositions implied by
`hG` and `hi`. Standard parabolic subgroups are indexed by the finite sets
`S ∈ (simpleFinset ν hG hi).powerset`, `S = Δ_0^P`. The bijectivity `hρ` of
`ArthurParabolicSpaces.restrictToTorus F i ν ∅` is an argument because the height of the
definitions uses it (see Qualifications).

## The compact subgroup

Arthur (2005, p.24) fixes "a suitable maximal compact subgroup `K = ∏ K_v` of `G(𝔸)`, with
`G(𝔸) = P_0(𝔸)K`", citing [Ti] and [A5, p.9]. In Arthur 1981 (pp.9–10) `K` is admissible
relative to `M_0`: at an Archimedean place the Lie algebras of `K_v` and `A_{M_0}` are orthogonal
for the Killing form; at a finite place the vertex of `K_v` in the Bruhat–Tits building is
special and lies in the apartment of a maximal split torus of `M_0`; and `K_v` is the standard
integral subgroup for almost all `v`. This condition cannot be stated with the Library's present
objects: there is no Killing form for a general reductive `G`, and the apartments of the
Library's building constructions are not known to be unique in general. The statements therefore
take two forms.

**Statements for every compact `K` with `P_0(𝔸)K = G(𝔸)`.** `TruncationFinitenessStatement`,
`TruncationSelfAdjointStatement` and `TruncationCancellationStatement` quantify over every
subgroup `K` with `hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` (compact and
`P_0(𝔸)K = G(𝔸)`), without maximality or any further condition. This class contains Arthur's
admissible `K`. The statements are Arthur's results for admissible `K`, and they hold for every
`K` of the class by the following transfer, which is not formalized. Write `H^K` for the height
`H_0` defined with `K` and fix an admissible `K_0`.

- *Bounded difference.* For `x = pk` with `p ∈ P_0(𝔸)`, `k ∈ K`, factor `k = p'k_0` with
  `k_0 ∈ K_0`; then `H^{K_0}(x) = H_0(p) + H_0(p') = H^K(x) + H^{K_0}(k)`. So
  `H^K(x) − H^{K_0}(x) = −H^{K_0}(k)` lies in `−H^{K_0}(K)` for every `x`. This set is bounded:
  `P_0(𝔸) × K_0` acts transitively on `G(𝔸)` by `(p, k_0)·g = p g k_0⁻¹`, both groups are
  σ-compact, so the orbit maps are open and the compact set `K` is covered by finitely many sets
  `C K_0` with `C ⊆ P_0(𝔸)` compact; `H_0` is bounded on `C`. In the same way, `H^K(xy) − H^K(x)`
  is bounded for `y` in a compact set, and `H^K` is continuous.
- *Finiteness.* `τ̂_P(H^K(δx) − T) ≠ 0` means `ϖ(H^K(δx) − T) > 0` for the finitely many
  linearly independent `ϖ ∈ Δ̂_P`. Choose `X` with `ϖ(X) ≥ sup |ϖ(H^{K_0}(K))|` for all of them.
  Then the cosets counted for `K` and `T` are among those counted for `K_0` and `T − X`, a finite
  set by Arthur 1978, Lemma 5.1. The same argument gives the relative finiteness over
  `P_1(F)\P(F)` with `τ̂_{P_1}^P`, from the relative form of Lemma 5.1 for `K_0`, and the finiteness
  uniformly for `x` in a compact set.
- *Formal properties.* For every `K` of the class, `H_P^K(nγx) = H_P^K(x)` for `n ∈ N_P(𝔸)` and
  `γ ∈ P(F)`, where `H_P^K` is the projection of `H^K` to `𝔞_P`: `H_0` vanishes on `N_0(𝔸) ⊇
  N_P(𝔸)`, and `|χ(γ)| = 1` for rational characters `χ` of `P` by the product formula. Arthur's
  proof of 13.1(c) (p.69) unfolds the sum over `P(F)\G(F)` against the integral over
  `G(F)\G(𝔸)` and uses only these invariances. The integrals converge absolutely: by Tonelli and
  the same unfolding, `∫ |φ₁| |Λ^Tφ₂|` and `∫ |Λ^Tφ₁| |φ₂|` are bounded by the finite sums over
  `P` of `∫_{G(F)\G(𝔸)} ∑_δ |φ₁|_P(δx) τ̂_P(H_P(δx) − T) |φ₂(x)| dx`, which are finite because
  `φ₂` has compact support modulo `G(F)` and the inner sums are finite uniformly on compact sets.
  The same invariances and local finiteness give `Λ^T(B_loc) ⊆ B_loc`. Arthur's proof of 13.3 and
  (13.10) (pp.73–74) substitutes the definition of `Λ^{T,P_1}`, combines the sums over
  `Q(F)\P_1(F)` and `P_1(F)\P(F)`, and applies Langlands' combinatorial lemma
  `∑_{Q ⊆ P_1 ⊆ P} (−1)^{dim(A_Q/A_{P_1})} τ̂_Q^{P_1} τ_{P_1}^P = δ_{QP}`; again only the
  invariances and the finiteness are used.

**Proposition 13.1(a),(b) for a chosen `K`.** Parts (a) and (b) depend on the position of `K`:
Arthur's proof (p.69) applies the Bruhat decomposition and Identity 6.2, which involve the
heights of Weyl group representatives (Arthur 1981, Lemma 1.1). The module therefore states them
as the predicate `IsTruncationIdempotent` of one `K`. `TruncationProjectionStatement` asserts that
some `K` satisfies it, together with the conditions under which the published L1 results apply to
that `K`. This follows Arthur's text: "We choose a suitable maximal compact subgroup" (p.24),
with the propositions then proved for that `K`. An admissible `K` is a witness:

- it is compact with `P_0(𝔸)K = G(𝔸)` (property (i));
- it is maximal compact in `G(𝔸)` (`IsMaximalCompactSubgroup F G K`): each `K_v` is maximal
  compact in `G(F_v)`, and a compact subgroup of `G(𝔸)` containing `K` projects into each `K_v`;
- for every actual Siegel setup (`AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j`) it
  satisfies the L1 compatibility `AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K`,
  that is, the elements of `K ∩ P_0(𝔸)` commute with `A_{T₀}`: the positive torus lives at the
  Archimedean places, where `K_v ∩ P_0(F_v) = (K_v ∩ N_0(F_v))(K_v ∩ M_0(F_v))` (property (iii)),
  `K_v ∩ N_0(F_v) = 1` (a compact subgroup of a real unipotent group is trivial), and
  `M_0 = Z_G(A_0)` commutes with the image of `T₀` in `A_0`;
- it satisfies `IsTruncationIdempotent` for every `D` and `hρ`, by Proposition 13.1(a),(b).

The existential statement is weaker than Arthur's result for every admissible `K` (at a finite
place there may be several conjugacy classes of special vertices). The predicate is stable under
conjugation by `p ∈ P_0(𝔸)`. Write `R(p)φ(x) = φ(xp)` for right translation (Arthur 2005, p.7).
If `x = q(pkp⁻¹)` with `q ∈ P_0(𝔸)` and `k ∈ K`, then `xp = qpk`, so
`H^{pKp⁻¹}(x) = H^K(xp) − H_0(p)`. In the defining sum of `Λ^T_{pKp⁻¹}φ(x)` the summand for `P`
and `δ` is therefore `φ_P(δx) τ̂_P(H^K(δxp) − (T + H_0(p)))`: the constant term is evaluated at
`δx` and the cutoff at `δxp`. Since `(R(p)⁻¹φ)_P(δxp) = φ_P(δx)`, this gives
`Λ^T_{pKp⁻¹} = R(p) Λ_K^{T + H_0(p)} R(p)⁻¹`. Constant terms commute with `R(p)`, and
`ϖ(H^{pKp⁻¹}(x) − T) = ϖ(H^K(xp) − (T + H_0(p)))`, so (a) for `pKp⁻¹` at `x` with parameter `T`
is (a) for `K` at `xp` with parameter `T + H_0(p)`, applied to `R(p)⁻¹φ ∈ B_loc`; (b) for `pKp⁻¹`
follows from (b) for `K` by the conjugation formula. The constant `C` changes by
`max_β |β(H_0(p))|`. For example, for `SL₂` over `ℚ` the compact subgroup with
factor `u·SL₂(ℤ₅)·u⁻¹` at `5` (`u` upper unipotent with entry `1/5`) and standard factors
elsewhere is not admissible, but it is the conjugate of the standard admissible subgroup by
`u ∈ N_0(𝔸) ⊆ P_0(𝔸)`, with `H_0(u) = 0`, so it satisfies the predicate with the same `C`.

## Statements

### `TruncationFinitenessStatement`

For every `K` of the class, every `S`, every `T ∈ 𝔞_0` and every `x ∈ G(𝔸)`, the set of
`δ ∈ P(F)\G(F)` with `τ̂_P(H_0(δx) − T) ≠ 0` is finite. This is the qualitative form of Arthur
1978, Lemma 5.1, and of Arthur's remark after (13.1) that the inner sum is finite. The
quantitative bound is not stated.

### `TruncationSelfAdjointStatement` (`B_loc` and Proposition 13.1(c))

For every `K` of the class there is `C` such that for every `T ∈ 𝔞_0` with `β(T) > C` for all
`β ∈ Δ_0` ("suitably regular"):

- for `φ ∈ B_loc(G(F)\G(𝔸))` (`IsLocallyBoundedInvariant (rationalSubgroup F G) φ`),
  `Λ^T φ ∈ B_loc(G(F)\G(𝔸))` (Arthur's (13.1) defines `Λ^T φ` as a function of `B_loc`), and for
  every `P_1 = P_{S₁}` and every `x` the constant term of `Λ^T φ` along `P_1` at `x` is a
  convergent integral (`HasConstantTerm`);
- (c) for `φ₁ ∈ B_loc(G(F)\G(𝔸))` and `φ₂` continuous, left `G(F)`-invariant and supported in
  `G(F)·C_s` for a compact `C_s` (that is, `φ₂ ∈ C_c(G(F)\G(𝔸))`), both products
  `Λ^Tφ₁ · conj(φ₂)` and `φ₁ · conj(Λ^Tφ₂)` are integrable on `G(F)\G(𝔸)` for the published
  quotient Haar measure `AdelicGroupPoints.rationalQuotientHaarMeasure F G`, and their integrals
  agree: `(Λ^Tφ₁, φ₂) = (φ₁, Λ^Tφ₂)`. The functions are evaluated at chosen representatives. (The
  integrability conclusions make the identity one of convergent integrals, as in Arthur; without
  them the equality would hold vacuously for non-integrable products, since Lean's integral of a
  non-integrable function is `0`.)

Arthur needs no regularity for these parts; the statement keeps the threshold `C` of
Proposition 13.1 and is implied by the version without it.

### `IsTruncationIdempotent hG hi D hK hρ` (Proposition 13.1(a),(b) for one `K`)

There is `C` such that for every `T ∈ 𝔞_0` with `β(T) > C` for all `β ∈ Δ_0` and every
`φ ∈ B_loc(G(F)\G(𝔸))`:

- (a) for every `P_1 = P_{S₁}` and every `x`, if `ϖ_β(H_0(x) − T) > 0` for some
  `β ∈ Δ_0 ∖ S₁`, then `constantTerm … S₁ (Λ^T φ) x = 0`. Here
  `ϖ_β = ArthurRelative.weight … Δ_0 β` is the weight of `Δ̂_{P_1}` attached to `β`, and
  `ϖ_β(H_0(x) − T) = ϖ_β(H_{P_1}(x) − T)`. This is Arthur's (a): the constant term vanishes
  unless `ϖ(H_{P_1}(x) − T) ≤ 0` for every `ϖ ∈ Δ̂_{P_1}`, with Arthur's correction of `<` to
  `≤` in [A4, Lemma 1.1];
- (b) `Λ^T (Λ^T φ) = Λ^T φ`, pointwise.

### `TruncationProjectionStatement` (Proposition 13.1(a),(b))

There is a subgroup `K` with `hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` that is
maximal compact, satisfies `IsPositiveTorusCompatible F G T i ν T₀ j K` for every `T₀`, `j` with
`IsSiegelAlgebraicSetup F G T i ν T₀ j`, and satisfies `IsTruncationIdempotent hG hi D hK hρ` for
every `D` and every `hρ`. See "The compact subgroup" for the relation to Arthur's `K`.

Arthur's remark that `Λ^T` extends to an orthogonal projection of `L²` (p.69) is a consequence
drawn from (b) and (c); the Hilbert-space extension is not stated here.

### `TruncationCancellationStatement` (Proposition 13.3)

For every `K` of the class and every `T ∈ 𝔞_0` (Arthur imposes no regularity here):

- for `φ ∈ B_loc(G(F)\G(𝔸))` and every `x`: for each `S₁ ⊆ Δ_0` only finitely many
  `δ ∈ P_1(F)\G(F)` give a nonzero term, and
  `∑_{S₁ ⊆ Δ_0} ∑_{δ ∈ P_1(F)\G(F)} Λ^{T,P_1} φ(δx) τ_{P_1}(H_{P_1}(δx) − T) = φ(x)`,
  with `τ_{P_1} = ArthurRelative.tau … S₁ Δ_0` evaluated at `H_0(δx) − T`;
- (13.10): for `P = P_{SP}` and `φ ∈ B_loc(P(F)\G(𝔸))` (left invariant under the image of
  `P(F)`), the constant term `∫_{N_P(F)\N_P(𝔸)} φ(nx) dn` is a convergent integral
  (`HasConstantTerm`), for each `S₁ ⊆ SP` only finitely many `δ ∈ P_1(F)\P(F)` give a nonzero term,
  and `∑_{S₁ ⊆ SP} ∑_{δ ∈ P_1(F)\P(F)} Λ^{T,P_1} φ(δx) τ_{P_1}^P(H_{P_1}(δx) − T)` equals that
  constant term.

The finite-support conclusions make the unconditional sums `∑'` ordinary finite sums (Lean's
`∑'` is `0` for a non-summable family). They hold because `τ_{P_1}^P ≤ τ̂_{P_1}^P` and the
relative form of the finiteness above.

### Common remarks

`C` may depend on all the data, including `K`. Arthur works over `ℚ` on `G(ℚ)\G(𝔸)^1`, with
`x₁ ∈ G(𝔸)^1` in (a) and the inner product of `L²(G(ℚ)\G(𝔸)^1)` in (c). The statements here use
a number field `F`, all of `G(𝔸)` and `L²(G(F)\G(𝔸))`, as in Lapid's §2: the operator commutes
with translation by `A_G(ℝ)^0` and its formula involves only the points `nδx` of the coset
`G(𝔸)^1 x`, so the two settings are equivalent by `G(𝔸) = G(𝔸)^1 × A_G(ℝ)^0` and Fubini; this
equivalence is not formalized.

## Qualifications

- `hρ` is a hypothesis of every statement, because the height of the definitions uses it; it is
  the identification `X(P_0) ⊗ ℝ ≅ X(A_0) ⊗ ℝ`, which follows from the comparison statement
  `ArthurParabolicSpaces.ParabolicSpacesComparisonStatement` by
  `ArthurParabolicSpaces.bijective_restrictToTorus_empty`. Once that statement is proved, the
  statements here hold without the hypothesis being an assumption.
- The class of `K` and the existential form of Proposition 13.1(a),(b) are explained under "The
  compact subgroup". The transfer arguments given there are sketches, not formal proofs.
- Proposition 13.2 and Lemma 8.2 are not stated here (see the Markdown of `ArthurTruncation`).
- The constant terms are the published L1 constant terms (`subgroupConstantTerm` with
  `normalizedRationalQuotientHaarMeasure`), and the pairing uses the published
  `rationalQuotientHaarMeasure`.

## Provenance

Source: Arthur 2005, §13, Propositions 13.1 and 13.3, and Arthur 1978, Lemma 5.1; the choice of
`K` from Arthur 2005, p.24, and Arthur 1981, §1. The setting on `G(F)\G(𝔸)` follows Lapid 2011,
§2. Derived formulations: the finiteness statement is the qualitative part of Lemma 5.1; the
formal parts are stated for every compact `K` with `P_0(𝔸)K = G(𝔸)` (justified by the transfer
above); parts (a) and (b) of Proposition 13.1 are stated as a predicate together with the
existence of a `K` satisfying it.
