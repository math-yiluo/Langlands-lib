# Finiteness of the supercuspidal unramified-orbit strata (proof)

Module `Langlands.Correspondence.HenniartOrbitStratumFinitenessProof`. Main theorem
`Langlands.Henniart.supercuspidalOrbitStratumFiniteness`; helper lemmas are in namespace
`Langlands.Henniart.OrbitStratumFiniteness`. Authors: Worker 5733 (draft), Worker 408.

Universes: `uK` (p-adic fields) and `uV` (supercuspidal carriers), independent.

## Statement

`supercuspidalOrbitStratumFiniteness : SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}`
proves the proposition of module
`Langlands.Correspondence.HenniartOrbitStratumFinitenessStatement`: for every prime `p`,
p-adic field `K : PadicField.{uK} p`, rank `k + 1` and conductor exponent `a`, the set
`Numerical.supercuspidalOrbitStratum.{uK, uV} K k a` is finite. That set consists of the
unramified-twist orbits of supercuspidal classes of `GL_(k+1)(K)` that contain a class of
conductor `a`. The theorem has no hypotheses.

All lemmas below use the canonical topology, valuative relation and local-field structure
of `K.canonicalTopologicalData`, installed as local instances. These are the instances
used by `Numerical.conductor`. Write `T := K.canonicalTopologicalData`,
`G := GL_(k+1)(K)`, `Z` for its centre, `ϖ := T.uniformizerUnit`, and
`L_b := Conductor.levelSubgroup K.Carrier k b` for the newvector subgroup of level `b`.

## Proof

The idea: twist every orbit to a representative whose central character is normalized,
then cover the stratum by finitely many finite central-level strata.

### Auxiliary lemmas

- `ord_det_eq_zero_of_mem_level`: every `g ∈ L_a` has `ord(det g) = 0`. Since
  `L_a ≤ L_0 = GL_(k+1)(O)` (`levelSubgroup_antitone`, `levelSubgroup_zero`), the
  published `RankinSelberg.normalizedAbs_det_of_mem_integralSubgroup` gives
  `|det g| = 1`. Then `q ^ (-ord(det g)) = q ^ 0` with `q > 1`, so `ord(det g) = 0`.
- `levelSubgroup_le_ker`: hence `L_a` lies in the kernel of every unramified
  determinant character `T.determinantUnramifiedCharacter (k + 1) z`,
  `g ↦ z ^ ord(det g)`.
- `exists_hasCentralCharacter` (Schur's lemma): a supercuspidal representation `A` of `G`
  has a central character `ω : Z →* ℂˣ`. The published lemmas of
  `Whittaker.MirabolicRigidity` give countable dimension of an irreducible smooth
  representation (`rank_le_aleph0`), so each central element acts by a scalar
  (`exists_scalar_of_commute`). Evaluating on a nonzero vector
  (`exists_ne_zero_of_isIrreducible`) shows that these scalars are nonzero and
  multiplicative.

### Finitely many normalized central characters

- `mem_integers_of_ord_eq_zero` and `scalar_mem_levelSubgroup_zero`: a scalar matrix
  with an entry of order zero lies in `L_0`, because both the entry and its inverse are
  integers.
- `integralCenter k := Z ∩ L_0` and `levelCenter k a := Z ∩ L_a`, the latter taken as a
  subgroup of `integralCenter k`. Both are defined by `Subgroup.comap` along subgroup
  inclusions.
- `exists_uniformizer_zpow_mul`: every `y ∈ Z` equals `scalar(ϖ) ^ m * y₀` with
  `y₀ ∈ integralCenter k`. By Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`,
  `y` is the scalar `x`. Take `m = ord x` and `y₀ = scalar(x ϖ^(-m))`; the entry
  `x ϖ^(-m)` has order zero.
- `finite_quotient_levelCenter`: `integralCenter k ⧸ levelCenter k a` is finite. The
  group `L_0` is compact (`Conductor.isCompact_levelOpenSubgroup`) and `L_a` is open in
  it, so `L_a ∩ L_0` has finite index in `L_0` (Mathlib's
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.finiteIndex_of_finite_quotient`).
  `levelCenter k a` is the preimage of that subgroup under the inclusion
  `integralCenter k → L_0` (built with `MonoidHom.codRestrict`). A preimage of a
  finite-index subgroup has finite index.
- `normalizedCentral k a` is the set of characters `χ : Z →* ℂˣ` with
  `χ(scalar ϖ) = 1` and `χ y = 1` for every central `y ∈ L_a`.
- `normalizedCentral_finite`: this set is finite. Each such `χ` restricted to
  `integralCenter k` factors through the finite quotient above (`QuotientGroup.lift`).
  The published `CompactOpenFiniteness.finite_monoidHom_units` gives finitely many
  characters of a finite group. The map is injective by `exists_uniformizer_zpow_mul`:
  `χ` is determined by its values on `integralCenter k` and at `scalar ϖ`, where it is 1.

### Covering the stratum

`supercuspidalOrbitStratum_subset`: the stratum is contained in
`⋃ χ ∈ normalizedCentral k a, orbitClass '' centralLevelStratum χ a`. Here
`centralLevelStratum χ a` is the published set of supercuspidal classes with central
character `χ` and `firstFixedLevel ≤ a`.

Let the orbit contain the class of `A` with conductor `a`, and let `ω` be the central
character of `A`. Let `c = ω(scalar ϖ)`.
1. Choose `z : ℂˣ` with `z ^ (k + 1) = c⁻¹` (`IsAlgClosed.exists_pow_nat_eq`; `z ≠ 0`
   since `c⁻¹ ≠ 0`). Let `χz := T.determinantUnramifiedCharacter (k + 1) z` and `A'` the
   twist `SupercuspidalRep.twist χz … A`.
2. `A'` has central character `ω' := (χz restricted to Z) * ω`. Its value at `scalar ϖ`
   is `z ^ (k + 1) * c = 1` (`determinantUnramifiedCharacter_scalar`,
   `unramifiedCharacter_uniformizer`).
3. `A` has a nonzero `L_a`-fixed vector (`firstFixedLevel_le_iff` with conductor `a`).
   Since `χz` is trivial on `L_a` (`levelSubgroup_le_ker`), the published
   `fixedVectors_twist_eq_of_le_ker` shows that `A'` has the same nonzero `L_a`-fixed
   space. So the class of `A'` has `firstFixedLevel ≤ a`.
4. A central `y ∈ L_a` fixes a nonzero `L_a`-fixed vector `v` of `A'` and acts on it by
   `ω' y`. So `(ω' y - 1) • v = 0` and `ω' y = 1`. Hence `ω' ∈ normalizedCentral k a`.
5. The class of `A'` lies in `centralLevelStratum ω' a`. It has the same orbit as `A`
   (`PadicSupercuspidal.unramifiedOrbitClass_twist`).

`supercuspidalOrbitStratum_finite`: the right-hand side of the covering is a finite union
(`normalizedCentral_finite`) of images of finite sets. Each `centralLevelStratum χ a` is
finite by the published
`Langlands.Henniart.CompactOpenFiniteness.centralLevelStratum_finite`. So the stratum is
finite (`Set.Finite.subset`, `Set.Finite.biUnion`, `Set.Finite.image`).
`supercuspidalOrbitStratumFiniteness` applies this to every `p`, `K`, `k`, `a`.

Lean check (environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lake build, diagnostic
`96076307-bca6-4d11-a32d-82a06deb42ea`):
- 0 errors and 0 warnings.
- `supercuspidalOrbitStratumFiniteness` is a theorem with level parameters `uK, uV`.
- Its axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The proof is internal. Its single deep input is the Library's p-adic form of
Bernstein–Zelevinsky (1976), Corollary 4.15 (printed p. 41), proved by Worker 4803 as
`CompactOpenFiniteness.centralLevelStratum_finite` (see
`PadicSupercuspidalFinitenessProof.md`). That result says that finitely many supercuspidal
classes have a fixed central character and a nonzero vector fixed by a fixed compact open
subgroup. The rest of the proof is the standard reduction from a fixed central character
to unramified-twist orbits. It plays the role of Henniart's normalization
`ω_π(ϖ_K) = 1` in his sets `𝒜²_K(n, j, ϖ_K)` of essentially square-integrable
representations (Henniart 1988, §2.6, printed p. 505; registered source
`henniart-1988-numerical`, printed page `p` is PDF page `p − 495`). Henniart works with
these normalized sets and a Swan-exponent bound; the Lean proof instead normalizes only
the representative used to cover each orbit and fixes the newvector level. The
statement is the supercuspidal finiteness conjunct of
`NumericalOrbitCountStatement`, used by the counting reduction
`numericalOrbitReduction` for Henniart's Théorème 1.2.

## Imported results

- `Langlands.Correspondence.HenniartOrbitStratumFinitenessStatement` (the target).
- `Langlands.Correspondence.PadicSupercuspidalFinitenessProof`:
  `CompactOpenFiniteness.centralLevelStratum_finite`, `finite_monoidHom_units`.
- `Langlands.Representation.RankinSelberg.IntegralDeterminant`:
  `RankinSelberg.normalizedAbs_det_of_mem_integralSubgroup`.
- `Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary`:
  `Whittaker.MirabolicRigidity.rank_le_aleph0`, `exists_scalar_of_commute`,
  `exists_ne_zero_of_isIrreducible`.
- `Langlands.Representation.Twist.AdmissibilityProof`: `fixedVectors_twist_eq_of_le_ker`.
- Through these imports: `Conductor.levelSubgroup`, `levelSubgroup_zero`,
  `levelSubgroup_antitone`, `levelOpenSubgroup`, `isCompact_levelOpenSubgroup`,
  `GeneralLinear.SupercuspidalClass.centralLevelStratum`, `firstFixedLevel_le_iff`,
  `GeneralLinear.SupercuspidalRep.twist`, `GeneralLinear.scalarToCenter`,
  `PadicField.TopologicalData.determinantUnramifiedCharacter` (with `_apply`, `_scalar`),
  `unramifiedCharacter_uniformizer`, `PadicSupercuspidal.unramifiedOrbitClass_twist`.
- Basic Library facts about `PadicField.TopologicalData` and `GL_n` used in the
  auxiliary lemmas: `ord_mul`, `ord_inv`, `ord_zpow`, `ord_uniformizer`,
  `uniformizerUnit_val`, `normalizedAbs_of_ne_zero`,
  `normalizedAbs_le_one_iff_mem_integers`, `residueCardinality_gt_one`,
  `isOpen_ker_determinantUnramifiedCharacter`,
  `ker_determinant_le_ker_determinantUnramifiedCharacter`,
  `generalLinearTopologicalGroup`, `generalLinearSecondCountableTopology`, and
  `Conductor.mem_integralSubgroup`.
- Mathlib: `Matrix.GeneralLinearGroup.center_eq_range_scalar`,
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.subgroupOf_isOpen`,
  `Subgroup.finiteIndex_of_finite_quotient`, `Subgroup.finite_quotient_of_finiteIndex`,
  `MonoidHom.codRestrict`, `QuotientGroup.lift`, `IsAlgClosed.exists_pow_nat_eq`,
  `Submodule.exists_mem_ne_zero_of_ne_bot`, `Finite.of_injective`, `Set.Finite.subset`,
  `Set.Finite.biUnion`, `Set.Finite.image`.
