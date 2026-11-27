# Uniform moderate growth of Eisenstein series on compact sets of unitary parameters

Module `Langlands.Global.AdelicEisensteinUnitaryGrowthStatement`, namespace `Langlands.Global`.
It defines one predicate, `IsUniformGrowthFamily`, states one proposition,
`EisensteinUnitaryUniformGrowthStatement`, and proves nothing.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), 187–234, registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`: §7.1, pp.210–211 (the Fréchet
  spaces `𝔉^R_smth(X)` of smooth right `K`-invariant functions all of whose derivatives are
  majorized by `e^{R‖H_0‖}`, and `𝔉_umg`, with footnote 6 on the equivalence with a height
  function on `G(𝔸)`); the Corollary at the end of §8.6, p.226 (meromorphic continuation of
  `λ ↦ E(φ, λ)` in these Fréchet spaces, with `R` and the level chosen locally in `λ`).
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*,
  Clay Math. Proc. 13 (2011), 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`: Proposition 6, printed pp.329–330
  (holomorphy of `E(φ, λ)` on `i𝔞_P^*` for `φ ∈ A^2_P`).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering): proof of
  Proposition 4.1, p.17, which uses this uniform moderate growth (cited there as
  Bernstein–Lapid, Corollary 8.6).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.2 (iv) and (vii), printed
  pp.20–21, for the comparison of growth scales below.

Provenance: derived. The statement is the consequence of the two cited results for parameters
in a compact subset of `i𝔞_P^*`, in the Library's notation for smooth functions of uniform
moderate growth (module `Langlands.Automorphic.GroupSchemeUniformGrowthFrechet`).

## `IsUniformGrowthFamily rho hsmooth hcalc L R f S`

For a family `f : Idx → FinitePlotSmoothRationalFunctions F G` (continuous left
`G(F)`-invariant functions on `G(𝔸)` with smooth archimedean slices and an open finite
stabilizer) and a set `S ⊆ Idx`:

1. every `f x`, `x ∈ S`, is fixed by right translation by every element of
   `L ≤ G(𝔸_f)` (`IsFixedByFiniteSubgroup`);
2. for every `u` in the complex enveloping algebra `AdelicEnvelopingAlgebra F G hsmooth` there
   is one `M` with `|(u · f x)(g)| ≤ M ‖g‖^R` for all `x ∈ S` and all `g ∈ G(𝔸)`. Here
   `u · f x` is `adelicEnvelopingAction F G hsmooth hcalc u (f x)` and `‖g‖` is
   `RepresentationGrowth.adelicSourceNorm F G rho g`.

For one function (`S` a singleton) this is membership in `uniformGrowthLevelSubmodule F G rho
hsmooth hcalc R L`. `IsUniformGrowthFamily` accepts any matrix representation `rho`. The
statement below assumes that `rho` is a closed embedding (`IsClosedSubgroup rho`, a closed
immersion `G → GL_N`) of some size `N`, and `N = 0` is allowed there. For a closed embedding of
positive size `N`, `UniformGrowthFrechetSpace` has the submodule above as its carrier, and the
family is bounded in each seminorm `sup_g |(u φ)(g)| ‖g‖^{-R}`.

## The statement

The data and hypotheses are those of `EisensteinUniformTemperednessStatement`
(`Langlands/Global/AdelicEisensteinUniformTemperednessStatement.lean`): a number field
`F : Type`, a connected reductive `G`, a parabolic `p : P → G` with presentation `r` and
geometric unipotent radical, a maximal compact `K` with `hK : IsIwasawaCompact p K`, a closed
matrix embedding `rho`, `hsmooth`, `hcalc`, `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`), and
`(E, D)` with

- `D ⊇ i𝔞_P^*` (`Set.range (imaginaryParameter F P) ⊆ D`);
- every `λ ↦ E λ g` meromorphic in linear coordinates with domain of holomorphy `D`;
- `E λ = hK.eisensteinSeries φ λ` for `Re λ` sufficiently regular.

For real linear coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and compact `C ⊆ ℝⁿ` the conclusion is:
there are an open subgroup `L ≤ G(𝔸_f)`, a real `R` and
`f : ℝⁿ → FinitePlotSmoothRationalFunctions F G` such that

- `f x` has underlying function `E(i e(x))` for every `x ∈ C`;
- `IsUniformGrowthFamily rho hsmooth hcalc L R f C`.

The values of `f` outside `C` play no role.

## Correspondence with the source

- The values `E(i e(x))` are those of the continued Eisenstein series: any two continuations
  agree on the intersection of their domains by uniqueness of meromorphic continuation from the
  nonempty open regular region (`ParabolicRootPresentation.eqOn_of_regularParameter`). At a
  point of `i𝔞_P^*` the value of `E` is the value of the continuation there.
- Bernstein–Lapid's Corollary gives, near every `λ₀`, an exponent `R`, a level and a meromorphic
  map into `𝔉^R_smth`. Its use here needs holomorphy of that map, not only of the scalar
  functions `λ ↦ E λ g`, at the points of `i𝔞_P^*`. Lapid's Proposition 6 gives holomorphy of
  the continued series on `i𝔞_P^*`; the passage to the Fréchet-valued map is part of the proof
  obligation of the statement.
- Bernstein–Lapid's spaces bound derivatives by `e^{R‖H_0‖}` on a Siegel domain, while
  `IsUniformGrowthFamily` bounds them by a power `‖g‖^R` of the adelic norm of `rho`. For a
  closed embedding `rho` of positive size the two scales are compared after a change of
  exponent, not identified at the same `R`, as in the section "Correspondence with the source"
  of `GroupSchemeUniformGrowthFrechet.md`. Mœglin–Waldspurger 1995, I.2.2 (iv) and (vii),
  compare the logarithm of their fixed height on the split component of the minimal Levi with
  the torus coordinate `‖H_0‖`, and bound the height of a Siegel representative by a multiple
  of the height of its rational translates. Comparing that fixed height with the Library's
  height of `rho` (both are heights of closed embeddings of positive size) then turns a bound
  with exponent `R` in Bernstein–Lapid's space into a bound here with exponent `R/c`, for a
  positive `c` depending on `rho`. Both comparisons are part of the proof obligation.
- The statement quantifies over every size `N`, including `N = 0`. A closed embedding into
  `GL_0`, the trivial group, forces `G` to be trivial, so `G(𝔸)` is a single point. The
  adelic norm of `rho` is then zero: the empty matrix has norm zero, so every archimedean local
  factor vanishes. The conversion to an exponent `R/c > 0` is not available, since a bound
  `M ‖g‖^{R/c}` would force the functions to vanish. In this case the family bound is obtained
  with exponent `R = 0`, where `‖g‖^0 = 1`, from a bound on the values of `E(i e(x))` at the
  single point of `G(𝔸)` for `x ∈ C`.
- A holomorphic map into a Fréchet space is bounded on compact sets. Covering `i e(C)` by
  finitely many neighbourhoods and taking the largest exponent and the intersection of the
  levels gives one `R`, one `L` and one bound for each seminorm.
- The family is indexed by the real coordinates `x ∈ C` of `λ = i e(x)`, as in
  `EisensteinUniformTemperednessStatement`. Every compact subset of `i𝔞_P^*` is of this form.

## Use

This bound supplies the common moderate-growth input in the proof of uniform temperedness in
Delorme 2023, Proposition 4.1: Mœglin–Waldspurger's Lemma I.4.1 is applied uniformly to a family
of automorphic forms bounded in a space of functions of fixed moderate growth.

## Scope

The statement does not assert meromorphic continuation in the Fréchet spaces, holomorphy on
`i𝔞_P^*` or any constant-term property. Nothing is proved here.
