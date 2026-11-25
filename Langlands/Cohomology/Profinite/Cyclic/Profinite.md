# Cup products with a character of a profinite group

`Langlands/Cohomology/Profinite/Cyclic/Profinite.lean`, namespace `Langlands.ProfiniteCohomology`.

For a profinite group `G` and a continuous character `χ : G → ℚ/ℤ`: the class `δχ ∈ H²(G, ℤ)` and the
map `A^G → H²(G, A)`, `a ↦ a ∪ δχ`, its explicit cocycle, and its compatibility with inflation from the
finite cyclic quotient `G/ker χ`.

## Declarations

- `cupRightProf`, `cupRightProf_apply`; `charClassProf χ` (`δχ`), `cupCharClassProf A χ`;
  `cupCharClassProf_zero` (the cup product with the zero character vanishes; from the source's
  `LocalClassFormation/CupSymbol.lean`, section "Zero").
- `charAdd`, `charAdd_apply`, `isLocallyConstant_charAdd`; `exists_cocycle_zeroIso_inv`,
  `exists_cocycle_charH1`, `exists_cocycle_charClassProf`, `exists_cocycle_cupCharClassProf`: explicit
  cocycles.
- `cupCharClassProf_eq_inflation`: the profinite class is inflated from the finite quotient.
- `inhomogeneousCochains_d_one_apply`, `inflation_H2π_eq_zero_iff`: when an inflated `2`-class is zero.
- Cochain criteria in low degrees, for a smooth representation `A` of a topological group `G`
  over a commutative ring `k`:
  - `inhomogeneousCochains_d_one_apply_vec (A : Rep k G) (w : (Fin 1 → G) → A) (g h : G) :
    (inhomogeneousCochains.d A 1).hom w ![g, h] = A.ρ g (w ![h]) - w ![g * h] + w ![g]` (any
    group), and `cochainOf_d_one_apply`, the same for a locally constant `1`-cochain;
  - `cohomologyπ_two_eq_zero_iff (A) [IsSmoothRep A] (z : cocycles A 2) : cohomologyπ A 2 z = 0 ↔
    ∃ f : G → A, IsLocallyConstant f ∧ ∀ g h : G, cochainOf A (cocycleι A 2 z) ![g, h] =
    A.ρ g (f h) - f (g * h) + f g`;
  - for a trivial action (`hA : ∀ g a, A.ρ g a = a`): `cochains_d_zero_one_eq_zero_of_trivial`
    (`(cochains A).d 0 1 = 0`), `cohomologyπ_one_eq_zero_iff_of_trivial` (`cohomologyπ A 1 z = 0 ↔
    ∀ g, cochainOf A (cocycleι A 1 z) ![g] = 0`), `cochainOf_cocycleι_one_mul_of_trivial`
    (a `1`-cocycle is additive), and `cocyclesOneOfHom A hA f hf hmul : cocycles A 1`, the
    `1`-cocycle of a locally constant homomorphism `f : G → A`, with its values
    `cochainOf_cocyclesOneOfHom`.
- `charKerOpen χ`: the kernel of `χ` as an open normal subgroup.
- `toGroupCohomology_cupCharClassProf`, `cupCharClassProf_surjective`: for a finite discrete cyclic
  group and injective `χ` the map is surjective.
- `eq_of_ne_one_of_card_eq_two`, `char_eq_half_of_card_eq_two`: groups of order two.

## Source and licence

Ported from the group-theoretic parts of `src/GroundTheory/ProfiniteCohomology/CyclicCupGaloisDefs.lean`,
`CyclicCupProf.lean`, `CyclicCupBrauer.lean` and `LocalClassFormation/CupSymbolReal.lean` (the
sections before their sections on Galois groups of fields) of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The field parts of these files
(`unitsInvariant`, `galCupClass`, the norm criterion, quadratic characters) belong to the field layer.
Names are the source's, with `H0Iso` → `zeroIso` (`exists_cocycle_H0Iso_inv` → `exists_cocycle_zeroIso_inv`).
The cochain criteria in low degrees are ported, from the same repository and commit, from
`src/GroundTheory/ProfiniteCohomology/LocalTateDuality/KummerCup.lean`, with
`cochainsComplex_d_zero_one_eq_zero_of_trivial` → `cochains_d_zero_one_eq_zero_of_trivial`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter I, §7; page reference
  to be added.
