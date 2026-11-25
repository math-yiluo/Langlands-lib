# The local Euler characteristic formula

`Langlands/GaloisCohomology/Local/EulerCharacteristic/Main.lean`, namespace `Langlands.GaloisCohomology.Local`.

**Theorem (Tate).** For a nonarchimedean local field `K` with separable closure `Ksep`
(`K Ksep : Type u`, any universe `u`) and a finite smooth `Gal(Ksep/K)`-module `M` of order invertible in `K`,
`χ(M) = |H⁰(M)| · |H²(M)| / |H¹(M)| = |𝒪[K] / |M|·𝒪[K]|⁻¹` (`eulerCharacteristic_eq`), equivalently
`|H¹(M)| = |H⁰(M)| · |H²(M)| · |𝒪[K]/|M|𝒪[K]|` (`card_cohomology_one`).

By dévissage it suffices to treat simple modules, which are `l`-torsion for a prime `l`. For `l = p`
the residue characteristic, the wild inertia group of a finite Galois extension `L/K` trivializing
`M` and `μ_p` is a `p`-group and acts trivially on `M`; the coprime case (`Coprime.lean`) applies to
the subgroup of `Gal(L/K)` above the prime-to-`p` part of `G/G₁`, and `χ` changes by a power under
restriction to a subgroup of `p`-power index with cyclic quotient (`Coinduced.lean`). For `l ≠ p`
the formula says `χ(M) = 1`: either tame inertia acts without fixed points and all cohomology
vanishes (`Vanishing.lean`), or the coprime case applies to the subgroup above the `l`-primary part
of `G/G₀`. The fixed fields are local fields for the spectral valuation of `Ksep`
(`Arithmetic/SeparableClosure.lean`).

## Declarations

- Fixed fields of open normal subgroups: `restrictFixed V`, `ker_restrictFixed`, `preimageOpen V S`,
  `index_preimageOpen`, `relIndex_preimageOpen`, `quotientPreimageOpenEquiv`,
  `isCyclic_quotient_preimageOpen`, `card_quotient_preimageOpen`,
  `pow_eq_one_mem_fixedField_preimageOpen`, `valuation_sub_lt_one_of_mem_preimageOpen`.
- Counting in rings of integers: `card_quotient_span_eq_one_of_isUnit`, `card_quotient_span_mul`,
  `card_quotient_span_natCast_mul`, `card_quotient_span_natCast_pow`,
  `card_quotient_span_natCast_eq_one`, `card_quotient_span_natCast_finiteExtension`
  (`|𝒪[L]/m| = |𝒪[K]/m|^{[L:K]}`).
- `exists_card_eq_prime_pow_of_nsmul`, `exists_ne_zero_forall_mem_eq` (a `p`-group has a fixed
  vector in a nonzero `𝔽_p`-module), `fixedSubmodule`.
- `eulerCharacteristic_of_forall_eq_bot_or_eq_top` (simple modules),
  `eulerCharacteristic_galois_of_card_eq`, `eulerCharacteristic_galois`,
  `card_cohomology_mul_div_eq`.
- Public: `eulerCharacteristic_eq K Ksep M hM`, `card_cohomology_one K Ksep M hM`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/MainGalois.lean`, `MainCount.lean`, `MainSimple.lean` and
`EulerCharGaloisOfCardEq.lean`. Mechanical renames (as in the foundations, `Langlands/Cohomology/Profinite/`): `IsDiscreteRep` → `IsSmoothRep`, `cohomologyMap` → `coeffMap`, `cohomologyMapAlong φ hφ` → `map ⟨φ, hφ⟩`, `cochainsComplex` → `cochains`, `cohomologyRes/Cores/ResLE` → `res/cores/resOfLE`, `H0Iso` → `zeroIso`, `eulerChar` → `eulerCharacteristic` (also inside names), `galUnits`/`galRootsOfUnity` → `unitsModule`/`rootsOfUnityModule` (lemma names keep `galUnits`/`galRootsOfUnity`), `unitsIncl` → `integerUnitsMap`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the source's valuative relation on `Ksep` (`algebraicValuativeRel`) and its fixed-field
instances are those of `Arithmetic/SeparableClosure.lean`; `FormalGroup.card_quotient_span_pow`
and `finrank_integer` are in `Arithmetic/Integers.lean`; `hasFiniteCohomology_galois_top` is
`hasFiniteCohomology` of `Dimension.lean`. `eulerCharacteristic_eq` and `card_cohomology_one` are
new public forms of the source's `eulerChar_galois` and
`card_cohomology_mul_div_eq`.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr.
  Mathematicians (Stockholm, 1962), 288–295, §2, Theorem 2.2 and the sketch of its proof, p. 289
  (the local Euler characteristic formula, for `k` complete under a discrete valuation with finite
  residue field and `|M|` invertible in `k`, §1, p. 288).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, Theorem
  (7.3.1) and its proof, pp. 392–396.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, Theorem 5 and its proof (for `p`-adic fields),
  pp. 99–101.
