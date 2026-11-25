# Finiteness of the cohomology of a local field in degrees `≤ 2`

`Langlands/GaloisCohomology/Local/Finiteness.lean`, namespaces `Langlands.GaloisCohomology` (fields)
and `Langlands.GaloisCohomology.Local` (local fields).

For a nonarchimedean local field `K`, a separable closure `Ksep`, an open subgroup `U` of
`Gal(Ksep/K)` and a finite smooth module `M` of `U` killed by an integer `n` invertible in `K`, the
groups `Hʳ(U, M)` are finite for `r ≤ 2`. First for `μ_n` (Kummer sequence: `H¹` is a quotient of
`Eˣ/Eˣⁿ` for the fixed field `E` of `U`, and `H²` injects into the `n`-torsion of
`H²(U, Ksepˣ) ≅ ℚ/ℤ`); then for modules on which an open subgroup fixing `μ_n` acts trivially, by
induction on the order through submodules `ℤ/p ≅ μ_p`; then for all modules by dévissage through
coinduced modules and Shapiro's lemma (`finite_cohomology_of_forall_trivial` of the module
`Langlands.Cohomology.Profinite.Finiteness`, which also has the other dévissage lemmas used here:
`finite_cohomology_X₁_succ`, `cokerShortComplex`, `finite_cohomology_zero`).

## Declarations

Fields:

- Instance `isSmoothRep_res_rootsOfUnityModule`: `μ_n` restricted to a subgroup is smooth.
- `kummerSequenceRes n V` (the Kummer sequence restricted to `V`), its smoothness instances,
  `kummerSequenceRes_shortExact`, `cohomologyMap_kummerSequenceRes_g_apply` (the last map is
  multiplication by `n` on cohomology).
- `zmod_lift_zmultiplesHom_injective`: `ℤ/p → X`, `1 ↦ c`, is injective for `c ≠ 0`, `p • c = 0`.
- `rootsOfUnityFixing F E n`: for any integral extension of fields `E/F` (here `Ksep/K`), the open
  subgroup of `Gal(E/F)` fixing the `n`-th roots of unity of `E`; `apply_eq_of_mem_rootsOfUnityFixing`.
- `natCard_rootsOfUnity_of_ne_zero`: for `p` invertible in `K`, `Ksep` has exactly `p` roots of
  unity of order dividing `p`.

Local fields:

- `subsingleton_cohomology_one_res_unitsModule V`: `H¹(V, Ksepˣ) = 0`.
- `finite_cohomology_one_res_rootsOfUnityModule`, `finite_cohomology_two_res_rootsOfUnityModule`,
  `finite_cohomology_res_rootsOfUnityModule`: `Hʳ(V, μ_n)` is finite for `r ≤ 2`;
  `subsingleton_cohomology_three_res_rootsOfUnityModule`: `H³(V, μ_n) = 0`.
- `finite_cohomology_of_trivial`: finiteness in degrees `≤ 2` for finite `n`-torsion modules with
  trivial action of an open subgroup that fixes `μ_n`.
- `finite_cohomology_res_of_le_two hn U M hM r hr`: `Hʳ(U, M)` is finite for `r ≤ 2`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/{Devissage, KummerOpen,
Trivial}.lean`, with `finite_cohomology_galois` (the case `r ≤ 2`) from
`LocalClassFormation/FiniteVanishing.lean`.
Renamed: `galRootsOfUnity` → `rootsOfUnityModule`, `finite_cohomology_one_rootsOfUnity_open` →
`finite_cohomology_one_res_rootsOfUnityModule` (and likewise for degrees 2, 3 and all `r ≤ 2`),
`subsingleton_cohomology_one_galUnits_open` → `subsingleton_cohomology_one_res_unitsModule`. The
repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Replaced notions: the source's class formation and invariant by `classFormation` (Library's
invariant); the source's finiteness of `Eˣ/Eˣⁿ` (`finite_quotient_range_pow`, from its own unit
filtrations, on its valuation of the separable closure) by `finite_quotient_range_powMonoidHom`
(`Arithmetic/Powers.lean`) applied to the fixed field with the Library's spectral local-field
structure; the source's stabilizer by `vectorStabilizer`. `rootsOfUnityFixing` and
`apply_eq_of_mem_rootsOfUnityFixing` are stated for any integral extension `E/F` in place of a
separable closure.

The source's dévissage lemmas (`finite_cohomology_X₁_succ` … `finite_cohomology_of_forall_trivial`)
are ported in the module `Langlands.Cohomology.Profinite.Finiteness`.

## References

- J.-P. Serre, *Galois Cohomology*, chapter II, §5.2, Proposition 14 (finiteness, for `p`-adic
  fields), p. 91.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §1, Theorem
  (7.1.8), p. 376, and §2, Theorem (7.2.9), p. 383.
