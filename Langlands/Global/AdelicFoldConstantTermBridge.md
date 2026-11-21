# Folded and quotient constant terms agree on invariant functions

Module `Langlands.Global.AdelicFoldConstantTermBridge`. Main result:
`Langlands.Global.StandardParabolicFamily.constantTerm_eq_foldConstantTerm`. Its statement form is
`Langlands.Global.FoldConstantTermBridgeStatement`, proved by
`Langlands.Global.foldConstantTermBridge`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family of a connected
reductive group over a number field `F`, in an arbitrary universe `u`. Let `Q` be a standard index.
Let `Λ₀ = StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν` be the image of `P₀(F)` in
`G(𝔸)`. Let `φ : G(𝔸) → ℂ` be measurable with `φ(l x) = φ(x)` for all `l ∈ Λ₀`. Then, for every
`g`,

`𝓕.constantTerm Q φ g = foldConstantTerm Λ₀ D hD (U_Q(𝔸) ↪ G(𝔸)) haar C φ g`.

- The left side is the Library constant term: the integral of `φ(u g)` over `U_Q(F)\U_Q(𝔸)` at
  chosen representatives, for the normalized quotient measure.
- On the right, `D` is the Library's Borel fundamental domain of `Λ₀` in `G(𝔸)` and `hD` its
  uniqueness property. `U_Q` is the standard unipotent subgroup `standardUnipotent 𝓕.i 𝓕.ν Q`.
  `haar` is Haar measure on `U_Q(𝔸)`, and `C` is the Borel fundamental domain of `U_Q(F)` in
  `U_Q(𝔸)`.
- `foldConstantTerm` (module `Langlands.Analysis.FundamentalDomainConstantTermL2`) is
  `haar(C)⁻¹ ∫_C φ(fold(v g)) dv`. It is the constant term computed by the weighted `L²` operators
  of `Langlands.Analysis.FundamentalDomainConstantTermOperator` and
  `Langlands.Global.AdelicStandardConstantTermOperator`.

The identity holds at every point, with no integrability hypothesis. When the integrand is not
integrable, both sides are `0` by the convention of the Bochner integral. The theorem lets the
pointwise results proved for the Library constant term be transferred to the `L²` operators. Those
pointwise results are the composition rule (`Langlands.Global.AdelicConstantTermComposition`) and
the cuspidality of Harish-Chandra components (`Langlands.Global.AdelicHarishChandraDecomposition`).

## Proof

- `Langlands.Global.RankinSelbergGlobal.Unfolding.integral_out_eq`: for a quotient measure built from a set of
  representatives `s` and a measurable left `Γ`-invariant `f`, the integral of `f` at quotient
  representatives equals `∫_s f`. This is the complex analogue of the Library's
  `EisensteinConstantTerm.lintegral_out_eq`, with the same proof (`out_eq_lift` and
  `integral_map`).
- `average_eq_setIntegral`: the representative average along a subgroup functor `U` with closed
  adelic points, of a measurable `U(F)`-invariant function, equals
  `haar(C)⁻¹ ∫_C φ(v g) dv`. The normalizing constant of the quotient measure is
  `haar(C)⁻¹` (`Langlands.Global.EisensteinConstantTerm.haar_fundamentalDomain_eq`).
- `foldConstantTerm_of_invariant`: on a left `Λ`-invariant function, `φ ∘ fold = φ`, so the folded
  constant term is the plain normalized average over `C`.
- `average_congr`: equal subgroup functors give equal averages. It is applied to the Library
  identification `range_radical_eq_standardUnipotent`.
- `constantTerm_eq_foldConstantTerm` combines these. It uses `U_Q(F) ⊆ Λ₀`
  (`StandardConstantTerm.rationalSubgroup_standardUnipotent_le`), so `Λ₀`-invariance implies
  `U_Q(F)`-invariance.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3 (p. 214). There `CT_P` is one
operator on functions on `P₀(F)\G(𝔸)`. The Library formalizes it pointwise, and this project
formalizes it as an operator on weighted `L²` of a fundamental domain. This derived module shows
that the two formalizations agree on invariant measurable functions. It does not prove commutation
with convolution or any statement about `L²` classes beyond this pointwise identity.
