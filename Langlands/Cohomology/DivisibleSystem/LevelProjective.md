# The levels of an `ℓ`-divisible system of modules are free over `R ⧸ (ℓ ^ m)`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.InvariantTotalProjective`
(the definition `UnderlyingPowTorsionProjectiveBelow` and its lemmas for
`groupStandardTotalSystem`, `quotientInvariantsTotalSystem`,
`smoothGodementInvariantTotalSystem` and `proPSmoothGodementInvariantTotalSystem`), and
through it on the DivisibleSystem module (`DivisibleSystem`, `powSMul`,
`DivisibleSystem.map`), the HomSurjective module (`PowTorsionProjective`) and the
PowTorsionProjective module (`TermwisePowTorsionProjective`). From Mathlib it uses
`Module.Basis.ofVectorSpace` over the residue field `R ⧸ (π)`, `Finsupp.linearCombination`,
`LinearMap.quotKerEquivOfSurjective`, `Submodule.liftQ`,
`ShortComplex.moduleCat_exact_iff`, `PadicInt.maximalIdeal_eq_span_p` and
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`.

The first part is ring theory in the namespace `Langlands.Cohomology`; the declarations named
`DivisibleSystem.…` are in `Langlands.Cohomology.DivisibleSystem`.

## Modules with flat powers of `π`

`R` is a commutative ring, `π : R`, `N : ℕ` and `M` an `R`-module.

- `PowQuotientFlat π N M` (a structure, `Prop`-valued): `π ^ N • x = 0` for every `x : M`
  (`smul_eq_zero`), and for `a + b = N`, every `x` with `π ^ b • x = 0` is `π ^ a • y` for some
  `y` (`exists_smul_eq`). For `π = ℓ` this is the shape of the axioms `powSMul_eq_zero` and
  `flat` of a `DivisibleSystem` at one level.
- `exists_eq_smul_of_forall_dvd_finsupp`: a finitely supported `d : ι →₀ R` whose values are
  all divisible by `r` is `r • d'` for a finitely supported `d'`.
- `exists_eq_linearCombination_add_pow_smul`: if every `x : M` is a linear combination of a
  family `v` plus an element of `π • M`, then for every `j` every `x` is a linear combination of
  `v` plus `π ^ j • z`. Induction on `j`.
- `PowQuotientFlat.pow_dvd_of_linearCombination_eq_zero`: let `v` be a family such that
  `∑ d i • v i ∈ π • M` forces `π ∣ d i` for all `i` (the reductions of the `v i` modulo `π` are
  linearly independent). Under `PowQuotientFlat π N M`, every relation
  `∑ c i • v i = 0` has `π ^ N ∣ c i` for all `i`. Proof: if `c = π ^ j • d` with `j < N`, then
  `π ^ j • ∑ d i • v i = 0`, so `∑ d i • v i = π ^ (N - j) • y` by `exists_smul_eq`, which lies
  in `π • M`; hence `d = π • d'` and `c = π ^ (j + 1) • d'`.

Now `(π)` is a maximal ideal (an instance argument `(Ideal.span {π}).IsMaximal`).

- `PowQuotientFlat.exists_presentation`: there are `ι : Type v` and `v : ι → M` such that
  `Finsupp.linearCombination R v` is surjective and every relation `∑ c i • v i = 0` has all
  `c i` divisible by `π ^ N`. Here `v` lifts a basis `b` of `M ⧸ π • M` over the field
  `R ⧸ (π)`. The reductions span, so `M = span v + π • M`, and iterating
  (`exists_eq_linearCombination_add_pow_smul` with `j = N`) and `π ^ N • M = 0` give
  surjectivity. The reductions are linearly independent, so the previous lemma bounds the
  relations.
- `PowQuotientFlat.exists_free_generators`: the same `v` satisfies
  `∑ c i • v i = 0 ↔ ∀ i, π ^ N ∣ c i`. The reverse direction holds because `π ^ N` kills `M`.
  So `c ↦ ∑ c i • v i` induces an isomorphism `(R ⧸ (π ^ N))^(ι) ≅ M`, and `M` is free over
  `R ⧸ (π ^ N)`. Lean states only the two properties of `v`, not a `Module.Free` instance over
  the quotient ring.
- `moduleCat_powSMul_hom_apply`: on `L : ModuleCat R`, the DivisibleSystem module's
  `powSMul ℓ m L` acts as scalar multiplication by `(ℓ : R) ^ m`.
- `PowQuotientFlat.powTorsionProjective`: for `M : ModuleCat R` with `PowQuotientFlat π N M`
  and `(ℓ : R) ^ m ∣ π ^ N`, `PowTorsionProjective ℓ m M` holds: every morphism `g : M ⟶ Y` lifts
  along every epimorphism `p : X ⟶ Y` with `X` killed by `ℓ ^ m`. Proof: choose `x i` with
  `p (x i) = g (v i)`. `X` is killed by `π ^ N`, and the relations of `v` have coefficients
  divisible by `π ^ N`, so `c ↦ ∑ c i • x i` vanishes on the kernel of `c ↦ ∑ c i • v i`. It
  factors through `M` (`Submodule.liftQ` and `LinearMap.quotKerEquivOfSurjective`), and the
  factorization lifts `g`.

## Uniformizers

- `IsUnitMulUniformizerPow ℓ π e` (a structure, `Prop`-valued), for `ℓ e : ℕ` and `π : R`:
  `(π)` is a maximal ideal (`isMaximal`), `0 < e` (`pos`), and `(ℓ : R) = u * π ^ e` for a unit
  `u` (`exists_unit`). So `π` is a uniformizer at `ℓ`, `e` is the ramification index of `ℓ`, and
  the ideals `(ℓ ^ m)` and `(π ^ (e * m))` of `R` agree.
- `IsUnitMulUniformizerPow.pow_dvd`: `(ℓ : R) ^ m ∣ π ^ (e * m)`.
- `IsUnitMulUniformizerPow.natCast`: if `(ℓ : R)` generates a maximal ideal,
  `IsUnitMulUniformizerPow ℓ ℓ 1`.
- `IsUnitMulUniformizerPow.int`: `IsUnitMulUniformizerPow p (p : ℤ) 1` for a prime `p`.
- `IsUnitMulUniformizerPow.padicInt`: `IsUnitMulUniformizerPow p (p : ℤ_[p]) 1` for a prime `p`,
  because the maximal ideal of `ℤ_[p]` is `(p)`.
- `IsUnitMulUniformizerPow.exists_of_isDiscreteValuationRing`: in a discrete valuation ring with
  an irreducible element `ϖ`, if `(ℓ : R)` is nonzero and not a unit, then
  `IsUnitMulUniformizerPow ℓ ϖ e` for some `e`.

## The levels of an `ℓ`-divisible system of modules

`T` is an `ℓ`-divisible system in `ModuleCat.{v} R` and `h : IsUnitMulUniformizerPow ℓ π e`.

- `DivisibleSystem.powQuotientFlat_obj`: `PowQuotientFlat π (e * m) (T.obj m)`. The first
  condition holds because `ℓ ^ m` kills `T m` and divides `π ^ (e * m)`. For the second let
  `a + b = e * m`, `a > 0` (the case `a = 0` is trivial), and `π ^ b • x = 0`, and let
  `ι : T m ⟶ T (a + m)` be the inclusion. `ℓ ^ m` kills `ι x`, so `flat a m` gives
  `ι x = ℓ ^ a • z`, which equals `π ^ a • w` with `w = (u ^ a * π ^ (e * a - a)) • z`. Then
  `ℓ ^ m • w = u ^ m • π ^ b • ι x = 0`, so `w = ι y` by `torsion_exact`. Since `ι` is
  injective and `ι (π ^ a • y) = π ^ a • w = ι x`, `π ^ a • y = x`.
- `DivisibleSystem.powTorsionProjective_obj`: `PowTorsionProjective ℓ m (T.obj m)`, from the
  previous lemma, `PowQuotientFlat.powTorsionProjective` and `pow_dvd`.
- `DivisibleSystem.exists_free_generators_obj`: there are `ι : Type v` and `v : ι → T.obj m`
  with `Finsupp.linearCombination R v` surjective and `∑ c i • v i = 0 ↔ ∀ i, (ℓ : R) ^ m ∣ c i`.
  So `T m` is free over `R ⧸ (ℓ ^ m)`. Proof: `exists_free_generators`, and `ℓ ^ m ∣ r` if and
  only if `π ^ (e * m) ∣ r`, because `ℓ ^ m = u ^ m * π ^ (e * m)`.

## Removing the hypothesis of the InvariantTotalProjective module

- `DivisibleSystem.underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow`: for `k` a
  commutative ring with `h : IsUnitMulUniformizerPow ℓ π e`, `π : k`, every group `Γ`, every
  `N`, and every `ℓ`-divisible system `K` of `ℕ`-graded cochain complexes in `Rep.{w} k Γ`,
  `UnderlyingPowTorsionProjectiveBelow N K` holds. For each degree `q`, the degree-`q` terms
  form an `ℓ`-divisible system `K.degree q` of representations. The forgetful functor to
  `ModuleCat k` is exact, so `(K.degree q).map (forget₂ _ _)` is an `ℓ`-divisible system of
  modules, and `powTorsionProjective_obj` applies to it. The bound `q < N` is not used.

For each of the four families of the InvariantTotalProjective module, the module states the
following four results, with the same variables as there and the hypothesis
`hℓ : IsUnitMulUniformizerPow ℓ π e` (coefficients `k` or `R`) in place of `hK` or `hfree`.
`W` is an `ℓ`-divisible system of representations (for the `homSystem` lemmas) or of
`ℤ`-graded cochain complexes of representations (for the `homComplexSystem` lemma) of `Γ`, or
of `G ⧸ H`. Each proof applies the InvariantTotalProjective lemma to
`underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ`.

- `TermwisePowTorsionProjective` of the total complexes `C_m^•`:
  `termwisePowTorsionProjective_groupStandardTotalSystem_of_isUnitMulUniformizerPow`,
  `termwisePowTorsionProjective_quotientInvariantsTotalSystem_of_isUnitMulUniformizerPow`,
  `termwisePowTorsionProjective_smoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow`,
  `termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow`.
- The transitions of `T_m(j) = Hom(C_m^j, W_m)` are surjective (Harris's (4.10.3)):
  `groupStandardTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow`,
  `quotientInvariantsTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow`,
  `smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow`,
  `proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow`.
- The inverse system of the `T_m(j)` satisfies the Mittag-Leffler condition:
  `isMittagLeffler_groupStandardTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_quotientInvariantsTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow`.
- The inverse system of Hom complexes `Hom^•(C_m^•, W_m)` satisfies the Mittag-Leffler
  condition in every degree:
  `isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_quotientInvariantsTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow`,
  `isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow`.

The families keep their other hypotheses: a finite group `Γ` for `groupStandardTotalSystem`;
for `quotientInvariantsTotalSystem` a normal subgroup `H` of finite index and the
surjectivity hypothesis `hK` of the Invariants module; for the truncated smooth Godement
resolutions `h` (a proof of Worker 3's unproved proposition
`SmoothGodementZeroExactStatement R G X`), `T`, `D`, `H`, `hterm` and `hres`; and in the
pro-`p` case also `hP` (the unproved proposition `ProPInvariantsExactStatement`), `hH` and
`hR`. The `towerHomEval` and limit-projection lemmas of the InvariantTotalProjective module
follow in the same way from the `TermwisePowTorsionProjective` results here and are not
restated.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed pp.304 and 312 (one-based PDF pages 6 and 14).

1. Harris's definition. On p.304, "By an ℓ-divisible system of `S(ẽ)`-modules over `U(ẽ)` we
   mean a collection `{T_m}` of étale sheaves in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules over `U(ẽ)`,
   `m ≥ 1`, with morphisms `i = i_{m',m} : T_{m'} → T_m` and
   `j = j_{m,m-m'} : T_m → T_{m-m'}` for all `m > m' ≥ 1` such that `T_m` is free over
   `ℤ/ℓ^mℤ`, `i` identifies `T_{m'}` with the `p^{m'}`-torsion in `T_m`, and (2.1)
   `0 → T_{m'} → T_m → T_{m-m'} → 0` is exact." The printed `p^{m'}` must be read as `ℓ^{m'}`,
   since `T_m` is a `ℤ/ℓ^mℤ`-module; the Library's axiom `torsion_exact` uses `ℓ`. The
   Library's `DivisibleSystem` renders the freeness by the axiom `flat`.
   `DivisibleSystem.exists_free_generators_obj` shows that for modules over `ℤ`, `ℤ_[p]` or a
   discrete valuation ring the axioms give Harris's freeness, with `R ⧸ (ℓ ^ m)` in place of
   `ℤ/ℓ^mℤ`. The module treats levels in `ModuleCat R`. For representations and complexes of
   representations it treats the underlying modules of the terms, not sheaves.
2. Harris's use. On p.312 (proof of Proposition 4.10) Harris deduces the surjectivity of
   (4.10.3) from the freeness of `C^j_m(ẽ)^{H_p}` and of the target over
   `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`; the InvariantTotalProjective module records the quotation. That module
   replaced the freeness by relative projectivity of the source and kept the projectivity of the
   underlying modules of the `H`-invariant terms as the hypothesis
   `UnderlyingPowTorsionProjectiveBelow`. Here the hypothesis is proved for every `ℓ`-divisible
   system when `ℓ = u π ^ e`. The results then depend only on the remaining hypotheses listed
   above.
3. The route. The relative projectivity is proved directly from the presentation by lifts of
   a basis of `M ⧸ π M`, without passing through freeness and the projectivity of free modules.
   The freeness statement `exists_free_generators_obj` is a corollary of the same presentation.
   The condition `PowQuotientFlat` and the hypothesis format `IsUnitMulUniformizerPow` are ours.
   For `ℤ` or `ℤ_[p]` with `ℓ = p` they cover Harris's coefficients `ℤ/ℓ^mℤ`. For Harris's `𝒪`,
   the ring of integers of a finite extension of `ℚ_ℓ`, the module constructs neither the ring
   nor its `IsDiscreteValuationRing` instance. Given such an instance and an irreducible `ϖ`,
   `exists_of_isDiscreteValuationRing` gives `IsUnitMulUniformizerPow ℓ ϖ e` for some `e`, since
   `ℓ` is then nonzero and not a unit; those two facts must be supplied.
4. Not shown. The freeness of the terms of `C_m^{•,H}` over `(R ⧸ (ℓ ^ m))[G ⧸ H]` (Harris
   p.306) is not proved. Only the underlying modules are treated, which is what the
   InvariantTotalProjective lemmas need.

## Scope

The module proves no freeness over group algebras and no `Module.Free` instance over
`R ⧸ (ℓ ^ m)`. It proves nothing about rings in which `ℓ` is not a unit times a power of a
generator of a maximal ideal. The surjectivity hypotheses on `H`-invariants and the unproved
propositions of the parent modules stay explicit.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.
