# Ramification groups of a finite Galois extension of local fields

`Langlands/GaloisCohomology/Local/Arithmetic/Ramification.lean`, namespace `Langlands.GaloisCohomology.Local`.

For a finite extension `L/K` of nonarchimedean local fields, `Gal(L/K)` acts on `𝒪[L]`; the lower
ramification groups are the Library's `Langlands.Ramification.lowerGroup` for this action. The
file proves what the local Euler characteristic needs: `G₀` is the kernel of the action on the
residue field; `G/G₀` is cyclic; `G₀/G₁` embeds into `𝓀[L]ˣ` through `σ ↦ σ(ϖ)/ϖ mod 𝓂`, hence is
cyclic of order prime to the residue characteristic `p`; `G₁` is a `p`-group; the filtration
terminates.

## Declarations

- `integerAction K L`: the action of `L ≃ₐ[K] L` on `𝒪[L]` (a definition, used as a local instance).
- `lowerRamificationGroup K L i := Ramification.lowerGroup 𝒪[L] (L ≃ₐ[K] L) i`;
  `mem_lowerRamificationGroup_iff : σ ∈ G_i ↔ ∀ x ∈ 𝒪[L], σ x − x ∈ 𝓂^(i+1)`;
  `lowerRamificationGroup_antitone`; instance `lowerRamificationGroup_normal`.
- `lowerRamificationGroup_zero : G₀ = ker (Gal(L/K) → Aut 𝓀[L])`;
  `residue_integerAlgEquiv_of_mem_zero`.
- `algEquiv_eq_of_forall_integer`, `faithfulSMul_integerAction`,
  `exists_lowerRamificationGroup_eq_bot` (from the Library's `exists_lowerGroup_eq_bot`).
- `uniformizerRatio hϖ σ` (`σ(ϖ) = ϖ · u`), `mul_uniformizerRatio`, `uniformizerRatio_eq_iff`,
  `uniformizerRatio_one`, `uniformizerRatio_mul`, `irreducible_integerAlgEquiv`.
- `mem_lowerRamificationGroup_one_iff hϖ hσ`: `σ ∈ G₀` is in `G₁` iff `σ(ϖ)/ϖ ≡ 1 mod 𝓂` (the
  residue field is perfect: the Library's `mem_lowerGroup_one_of_frobenius`).
- `inertiaToResidueUnits hϖ : G₀ →* 𝓀[L]ˣ`, `ker_inertiaToResidueUnits` (`= G₁`),
  `inertiaQuotientToResidueUnits`, `inertiaQuotientToResidueUnits_injective`.
- `isCyclic_lowerRamificationGroup_zero_quotient`, `card_lowerRamificationGroup_zero_quotient_dvd`,
  `coprime_card_residueField_sub_one`, `coprime_card_lowerRamificationGroup_zero_quotient`.
- `isPGroup_lowerRamificationGroup_one K L : IsPGroup (ringChar 𝓀[K]) G₁` (the Library's
  `isPGroup_lowerGroup_one_of_terminates`); instance `isCyclic_quotient_lowerRamificationGroup_zero`.

## Source and licence

The statements are those of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/LocalFields/Ramification.lean`
(`lowerRamificationGroup_zero`, `residue_integerAlgEquiv_of_mem_zero`,
`algEquiv_eq_one_of_forall_integer`, here generalized to `algEquiv_eq_of_forall_integer`,
`exists_lowerRamificationGroup_eq_bot`), `RamificationUnits.lean` (`uniformizerRatio` and its
lemmas, `irreducible_integerAlgEquiv`), `RamificationStructure.lean` (`inertiaToResidueUnits`,
`ker_inertiaToResidueUnits`, `inertiaQuotientToResidueUnits`, `isCyclic_…`, `card_…_dvd`,
`coprime_…`, `isPGroup_lowerRamificationGroup_one`), and
`src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean`
(`isCyclic_quotient_lowerRamificationGroup_zero`); their proofs are ported where unchanged.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Changes: the source defines `lowerRamificationGroup K L (i : ℤ)` itself; here it is the Library's
`lowerGroup` (natural-number index) for `integerAction`. The source proves that `G₁` is a
`p`-group and that `G₀/G₁ → 𝓀ˣ` has kernel `G₁` through the graded pieces of the unit filtration
(`ramificationToUnits`) and Teichmüller lifts; here these are the Library's
`isPGroup_lowerGroup_one_of_terminates` and `mem_lowerGroup_one_of_frobenius`, and the source's
`ramificationToUnits`, `sub_mem_of_uniformizer` and Teichmüller section are not taken.

## References

- J.-P. Serre, *Local Fields*, chapter IV, §1 (the lower ramification groups), pp. 61–62, and §2,
  Proposition 7 and Corollaries 1–4 (`G₀/G₁` embeds into the multiplicative group of the residue
  field, `G₁` is a `p`-group), pp. 66–67.
