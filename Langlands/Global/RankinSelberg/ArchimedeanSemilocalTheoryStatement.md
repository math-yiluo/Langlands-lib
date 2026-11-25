# The archimedean Rankin–Selberg theory behind the semi-local functional equations

Module `Langlands.Global.RankinSelberg.ArchimedeanSemilocalTheoryStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. This is the entry module of the archimedean statements. It collects the
three results that the two open premises

* `UnequalSemilocalFactorizationStatement` (module
  `Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement`, `t < r`) and
* `EqualSemilocalFactorizationStatement` (module
  `Langlands.Global.RankinSelberg.EqualSemilocalReduction`, equal ranks)

need about the infinite places, the factorization over `S` and the central sign.

## Statements

* `ArchimedeanSemilocalTheoryStatement.{u, uQ}` is the conjunction of
  1. `ArchimedeanFunctionalEquationStatement.{u}` (result 1, the archimedean local functional
     equation, at the complex and at the real places, both ranks; module
     `ArchimedeanFunctionalEquationStatement`);
  2. `ArchimedeanFactorizationStatement.{u, uQ}` (result 2, the factorization over `S` and the
     infinite places, both ranks; module `ArchimedeanFactorizationStatement`);
  3. `ArchimedeanCentralSignStatement.{u, uQ}` (result 3, the central sign; module
     `ArchimedeanCentralSignStatement`).
* `ComplexSemilocalTheoryStatement.{u, uQ}` is the same with only the complex-place part
  `ComplexPlaceFunctionalEquationStatement.{u}` of result 1. It is the input of the totally
  complex derivation below.

Both are `Prop`-valued, with the universes `u` and `uQ` free, as in the premises. Results 2
and 3 do not assume result 1. The helper modules are `ArchimedeanPlaces` (place inclusions,
archimedean restrictions, minus-one scalars) and `ArchimedeanIntegrals` (local integrals).

Neither premise is proved here; the derivations below are sketches for proofs of the two
premises.

## Derivation of `UnequalSemilocalFactorizationStatement`

Fix the premise's data: `F`, `ψ`, `t < r`, `T`, `Td`, `T'`, `Td'`, `P`, `P'`, `hI`, `hI'`, `S`,
`aR`, `aC`, the parameters, and canonical components `ψv` with self-dual measures `νv`.

**Step 1 (result 2).** `UnequalArchimedeanFactorizationStatement` has the same binders. It
gives `x`, `x'` spherical outside `S`, `c ≠ 0`, `WR`, `WR'`, `DR`, `WC`, `WC'`, `DC`, `σ₂`, test
data `D v` (`v ∈ S`), the `Is…PlaceWhittaker` conditions, the two factorizations on
`σ₂ < Re s` with the same `c`, and the four nonvanishing clauses.

**Step 2 (result 1).** For each real place `v`, apply `RealUnequalFunctionalEquationStatement`
to `aR v`, `dR v`, `dR' v`, `dRd v`, `dRd' v` with their hypotheses, `DR v`, `WR v`, `WR' v`.
This gives `σ_v`, `M_v`, `Md_v`. For each complex place `w`, apply
`ComplexUnequalFunctionalEquationStatement` likewise, giving `σ_w`, `M_w`, `Md_w`.

**Step 3 (the functions).** Let `σ` be at least `σ₂` and all `σ_v`, `σ_w` (finitely many
places), and

* `Ainf(s) = c · (∏_(v real) M_v(s)) · ∏_(w complex) M_w(s)`,
* `Binf(s) = c · (∏_(v real) Md_v(s)) · ∏_(w complex) Md_w(s)`.

On `{σ < Re s}` these are `c Ψ_∞(s)` and `c Ψ̃_∞(s)`, since each `M_v`, `Md_v` agrees there with
its integral.

The clauses of the premise, in order:

1. **`x`, `x'`, `IsSphericalOutside`**: from Step 1.
2. **`σ`, `Ainf`, `Binf`, `D`**: as above, with `D` from Step 1.
3. **`MeromorphicOn Ainf`, `MeromorphicOn Binf`**: finite products of meromorphic functions
   and a constant (`MeromorphicOn.fun_prod`, `MeromorphicOn.mul`).
4. **`Ainf`, `Binf` nonzero off a discrete set**: result 2 gives `s₀` with `σ < Re s₀` and
   `Ψ_∞(s₀) ≠ 0`. On the open half-plane each local integral is holomorphic (result 1, clause
   2), hence analytic at `s₀` (`DifferentiableOn.analyticAt`), and `M_v` agrees with it near
   `s₀`, so `M_v` is analytic at `s₀` (`AnalyticAt.congr`). Hence `Ainf` is analytic at `s₀`
   with `Ainf(s₀) = c Ψ_∞(s₀) ≠ 0`, and `EqualSemilocalReduction.eventually_ne_zero_of_analyticAt`
   gives the claim. `Binf` is the same with the nonvanishing of `Ψ̃_∞`.
5. **Nonzero rational continuations of `(D v).integral`** (finite places): for `v ∈ S`,
   `Automorphic.CuspidalPairPartialGamma.localGenericity` makes the local components of `P`
   and `P'` generic for `ψv v`, `RankinSelberg.genericPairGammaFactor_isPadic` gives a local
   gamma factor `G` with `IsPadicPairGammaFactor` for `ψv v`, `νv v`, and
   `PadicUnequalTestData.exists_gammaEquation` (module `UnequalSemilocalEquationReduction`)
   gives a rational continuation `R` of `(D v).integral h (νv v)`. If `R = 0`, the integral
   vanishes on a right half-plane, against the nonvanishing clause of result 2; so `R ≠ 0`.
6. **Factorization of `Ψ_(S∪∞)`**: for `σ < Re s`, result 2 gives
   `partialUnequalWhittakerIntegral … = c Ψ_∞(s) ∏_(v ∈ S) (D v).integral h (νv v) s`, and
   `c Ψ_∞(s) = Ainf(s)`.
7. **Factorization of `Ψ̃_(S∪∞)`**: the same, with the same `c`, `c Ψ̃_∞(s) = Binf(s)`.
8. **Sign clause.** Let `ζ` satisfy `(D v).HasMinusOneScalar (ζ v)` for `v ∈ S`, i.e.
   `HasModelMinusOneScalar` for `(D v).inverseFunctional`, which is nonzero
   (`inverseFunctional_ne_zero`). Result 3, applied to `T'`, `P'`, `hI'`, `S`, `ψv` and `ζ`,
   gives `(∏ ω'_v(−1)) (∏ ω'_w(−1)) ∏ ζ_v = 1`; raising to the power `r`,
   `(∏_(v ∈ S) ζ_v^r) · ω = 1` with `ω = (∏_(v real) ω'_v(−1)^r) (∏_(w complex) ω'_w(−1)^r)`.
   The functional equations of Step 2 hold simultaneously off a discrete set (finitely many
   codiscrete conditions, `Filter.eventually_all`). Multiplying them over all infinite places
   gives `∏ L_v(s) · ∏ Md_v(1 − s) = ω · ∏ ε_v(s) · ∏ L∨_v(1 − s) · ∏ M_v(s)`. The products of
   `L_v`, `L∨_v`, `ε_v` are by definition the premise's `infiniteL`, `dualInfiniteL`,
   `infiniteEpsilon` (real factors times complex factors). Multiplying by `c` gives
   `infiniteL s · Binf(1 − s) = ω · infiniteEpsilon s · dualInfiniteL (1 − s) · Ainf s`, and
   multiplying by `∏ ζ_v^r` gives the clause, since `(∏ ζ_v^r) ω = 1`.

## Derivation of `EqualSemilocalFactorizationStatement`

Fix the premise's data as above, with `r` the common rank minus one.

**Step 1 (result 2).** `EqualArchimedeanFactorizationStatement` gives `x`, `x'`, `Φ`
(spherical, Schwartz–Bruhat, standard outside `S`), `c ≠ 0`, `WR`, `WR'`, `ΦR`, `DR`, `WC`,
`WC'`, `ΦC`, `DC`, `σ₂`, `D v : EqualLocalTestData` (`v ∈ S`) and its clauses: `c ≠ 0`, the
`Is…PlaceWhittaker` conditions, the pointwise factorizations
`Φ = Φ_∞ ⊗ ⊗_(v ∈ S) (D v).Φ ⊗ 1` and `Φ̂ = Φ̂_∞ ⊗ ⊗_(v ∈ S) (D v).Φhat ⊗ 1` (constant exactly
one), the two integral factorizations on `σ₂ < Re s` with the same `c`, and the four
nonvanishing clauses (numbered 1–7 in the Markdown of `ArchimedeanFactorizationStatement`).

**Step 2 (result 1).** Apply `RealEqualFunctionalEquationStatement` at each real `v` with
`DR v`, `WR v`, `WR' v`, `ΦR v`, and `ComplexEqualFunctionalEquationStatement` at each complex
`w` with `DC w`, `WC w`, `WC' w`, `ΦC w`. The dual integrals of result 1 use the Fourier
transforms of `ΦR v`, `ΦC w` for `aR v`, `aC w` and the self-dual measures, which are the
transforms of result 2's `Ψ̃_∞`.

**Step 3.** Take `σ` as before, `Z = c ∏ M_v ∏ M_w`, `Zd = c ∏ Md_v ∏ Md_w` and
`κ = (∏_(v real) ω'_v(−1)^r) (∏_(w complex) ω'_w(−1)^r)`, which does not depend on `D`.

The clauses of the premise, in order:

1. **`x`, `x'`, `Φ`, sphericity, `Φ ∈ schwartzBruhat`, `IsStandardOutside`**: Step 1.
2. **`σ`, `Z`, `Zd`, `κ`**: Step 3.
3. **Meromorphy of `Z`, `Zd`**: as in the unequal case.
4. **`Z`, `Zd` nonzero off a discrete set**: as in the unequal case, from the nonvanishing
   of `Ψ_∞`, `Ψ̃_∞`.
5. **`infiniteL s · Zd(1 − s) = κ · infiniteEpsilon s · dualInfiniteL (1 − s) · Z s` off a
   discrete set**: the product of the equations of Step 2, times `c`; the sign product is `κ`.
6. **`D`**: from Step 1.
7. **`(D v).integral`, `(D v).dualIntegral` not identically zero on right half-planes**:
   result 2, clause 7.
8. **`κ ∏_(v ∈ S) ζ_v^r = 1` for `ζ` with `(D v).HasMinusOneScalar (ζ v)`**: this is
   `HasModelMinusOneScalar` for `(D v).ℓ'`, which is nonzero (`ℓ'_ne_zero`). Result 3 raised to
   the power `r`.
9. **Factorization of `Ψ_(S∪∞)(s; W, W', Φ)`** for `σ < Re s`: result 2 and `c Ψ_∞(s) = Z(s)`.
10. **Factorization of `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)`**: result 2 (clause 6) with the same `c`, and
    `c Ψ̃_∞(s) = Zd(s)`. The function `Φ̂ = fourierTransform F (r + 1) ψ Φ` in this integral is
    the premise's `Φhat`. By clause 4 of result 2 it factors pointwise with constant exactly
    one into the archimedean transforms of `ΦR v`, `ΦC w` (those entering `Ψ̃_∞` and result 1)
    and the Fourier partners `(D v).Φhat` (those entering `(D v).dualIntegral`). So no
    constant enters the dual side besides `c`, and `κ` is exactly the product of the
    archimedean signs, as clause 8 requires. (The derivation uses the integral identity
    of clause 6 directly; clauses 3 and 4 of result 2 record that its local data are those
    of `Φ` and `Φ̂`.)

The case `r = 0` (Tate's `GL_1 × GL_1`, trivial `N_1`) is covered: all statements are uniform
in `r`, and the signs are then `1`.

## Library results at the finite places

* **Rational continuation and local gamma factors.** In the unequal derivation, clause 5:
  `Automorphic.CuspidalPairPartialGamma.localGenericity`,
  `RankinSelberg.genericPairGammaFactor_isPadic` and
  `PadicUnequalTestData.exists_gammaEquation`. The equal premise does not ask for
  continuations; its reduction `equalSemilocalReduction` obtains them from
  `EqualLocalTestData.exists_continuations` (JPSS Theorem 2.7, `equalRankAnalytic`) and
  `EqualLocalTestData.exists_gammaEquation`, which also supply the scalars `ζ_v`.
* **`HasModelMinusOneScalar.unique`.** The sign clauses of both premises and result 3 are
  universal in `ζ`, so the derivations do not need uniqueness. By
  `HasModelMinusOneScalar.unique` the scalar of a nonzero functional is unique, so this
  universality is no restriction, and the `ζ_v` supplied by the local gamma factors in the
  two reductions is the scalar `ω'_v(−1)` of result 3.

## Totally complex fields

Let `F` be totally complex, `[NumberField.IsTotallyComplex F]`. Every infinite place is
complex (`IsTotallyComplex.isComplex`), so `{v : InfinitePlace F // v.IsReal}` is empty
(`InfinitePlace.not_isReal_iff_isComplex`). In both derivations, result 1 is applied only at
the places indexing the products. Over the empty real index type there is nothing to apply:
the real families of result 2 are functions on an empty type, every real product is `1`
(`Finset.univ_eq_empty`, `Finset.prod_empty`), and `σ` is taken over `σ₂` and the complex
places only. The derivations then use

* `ComplexUnequalFunctionalEquationStatement` and `ComplexEqualFunctionalEquationStatement`
  (the complex-place part of result 1),
* results 2 and 3 at this `F`,
* and the Library results named above,

and give the bodies of both premises at `F`. They do not use
`RealPlaceFunctionalEquationStatement`. In Lean terms, `ComplexSemilocalTheoryStatement`
implies, for every totally complex `F`, the instance of each premise at `F`; these are the
totally complex forms of the premises (the premise with `[NumberField.IsTotallyComplex F]`
inserted after `[NumberField F]`).

## Conventions and the sign

The normalizations are those of the premises: the normalized absolute value (the square of
the usual one at a complex place), the measures self-dual for `aR v`, `aC w` and `ψv v`, the
positive Fourier sign of `fourierTransform`, `w_n = weylLong` in `dualFunction`, `ρ(w_(n,m))` by
`unfoldingWeyl`, and the Library's archimedean pair factors with the standard `ε`. In these
conventions the archimedean sign is `ω'_v(−1)^r = ω'_v(−1)^(n−1)` in both ranks, as in Cogdell
(Theorem 3.6, p.217). Jacquet's signs (p.6), `ω_π(−1)^(n′) ω_π′(−1)` for `n > n′` and
`ω_π(−1)^(n−1)` for `n = n′`, are for his `ε` and his Fourier transform
`∫ Φ(Y) ψ(−Tr(ᵗX Y)) dY` (p.3); the conversion is in the Markdown of
`ArchimedeanFunctionalEquationStatement`. With this sign both premises follow as above. No
inconsistency between the premises and the Library's conventions was found.

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3): §3.2, Theorems 3.5–3.6,
  pp.216–217; proof of Theorem 4.1, pp.219–220.
* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg` (PDF page = printed page): pp.3–6, Theorem 2.1 and
  (2.4)–(2.6); pp.8–10, Theorems 2.3, 2.6, 2.7.

## Provenance

The three results are source statements (Jacquet 2009, Theorem 2.1; Cogdell 2004,
pp.216–220) in the Library's conventions. The two conjunctions and the split into results 1–3
are internal, chosen for what the two premises need.
