# Uniform conjugation height bounds on the actual minimal parabolic

This unit states and proves an actual-point form of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Lemma II.3.3, printed p.256 (PDF p.22), registered as
`waldspurger-2003-plancherel`, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The chamber is the full `rationalMinimalChamber i ν`, with the published
positive-sign root-order convention. No norm-kernel restriction is
imposed here.

The closed Prop-valued declaration
`RationalMinimalParabolicConjugationHeightStatement` says that for every
nonarchimedean local field, connected reductive affine group scheme
locally of finite type, actual maximal split torus and generic
cocharacter, and every finite nonempty matrix realization indexed by
`Fin N`, there is `C ≥ 1` such that

```text
1 + rationalHeight ρ (a * p * a⁻¹)
  ≤ C * (1 + rationalHeight ρ p)
```

for every actual point `a` of the full minimal chamber and every actual
point `p` of the minimal standard parabolic.
`rationalMinimalParabolicConjugationHeight` proves this statement.
The supporting theorems allow any nonempty finite matrix index type.
They need no closedness of the representation, adapted height, supplied
compact subgroup, Cartan decomposition, or Iwasawa decomposition.

The implemented proof uses simultaneous torus diagonalization rather
than the source's `τ₀` representation. Its steps are:

1. `glNorm_conj_le_of_mem_blockParabolic` proves that conjugation by
   `diag(t ^ e)` with `‖t‖ ≤ 1` does not increase the matrix norm on
   its block parabolic. Entries with the wrong weight order vanish;
   each remaining entry is multiplied by a scalar of norm at most
   one. The inverse matrix belongs to the same block parabolic,
   giving the inverse-entry half of the norm bound.
2. `standardParabolic_empty_le_of_simpleRootPairings_nonneg` puts each
   cocharacter `c` with nonnegative simple-root pairings on the face
   of simple roots on which its pairing is zero. The published
   `standardCocharacter` equality and `standardParabolicOrder`
   inclusion show that its dynamic parabolic contains the minimal
   standard parabolic.
3. The supporting `TorusCharacterDiagonalization` module chooses a
   single rational change of coordinates diagonalizing the entire
   supplied split torus. Every cocharacter composite in those same
   coordinates is exactly the diagonal cocharacter of its actual
   character pairings. Hence
   `rationalMatrixNorm_conj_latticeSection_le` applies the first two
   steps to every dominant intrinsic uniformizer-section point.
4. For any actual torus point, the published
   `CocharacterUniformizer.isUniformizerLatticeSection` factors it
   as a torus norm-kernel point times its section representative.
   `mem_normKernel_mul_section_inv_iff` identifies the root orders
   of the original point with the representative's pairings.
   The actual image of the torus norm kernel is compact by
   `SplitTorus.isCompact_commonNormKernel`. Its matrix heights
   therefore have a common upper bound. Subadditivity and inversion
   invariance of height extend the section contraction to every
   actual chamber point.
5. `exists_rationalHeight_conjugate_compare` proves that one fixed
   rational coordinate change alters the height by a bounded
   additive amount, in both directions. Returning to the original
   coordinates gives the stronger intermediate conclusion
   `σ(a*p*a⁻¹) ≤ B + σ(p)`, with `B ≥ 0` uniform in both `a` and
   `p`. Increasing the coefficient to `1 + B` yields II.3.3.

The exported forms include the additive estimate
`exists_rationalHeight_conj_le_on_minimalParabolic`, the positive
multiplicative estimate
`exists_one_add_rationalHeight_conj_le_on_minimalParabolic` with
arbitrary actual torus parameters, and the ambient-chamber estimate
`exists_one_add_rationalHeight_conj_le_on_chamber`.

The field universe is arbitrary, both local-field characteristics and
nonsplit connected reductive groups are retained, and the simple-root
set may be empty. This proves the minimal-parabolic contraction input
needed in II.3.5. The maximal-parabolic open-cell estimate and its
opposite-radical tail cutoff remain separate obligations.
