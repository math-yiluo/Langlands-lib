# The global reciprocity law from `H¹(C_E) = 0`

This module proves the global reciprocity law of Artin–Tate, *Class Field Theory*, Chapter VII
§3, Theorem 6 (printed p.45, PDF p.54). It proves it in the form of the Library proposition
`Langlands.ClassField.Global.GlobalReciprocity` from the statement module
`Langlands.ClassField.Global.ReciprocityStatement`, which is unchanged. The proof assumes the
Library proposition `IdeleClassH1Vanishing` of `Langlands.ClassField.Global.FundamentalClassStatement`:
`H¹(Gal(E/F), C_E) = 0` for every finite Galois extension of number fields. The main results
are:

- `Langlands.ClassField.Global.globalReciprocity_of (hH1 : IdeleClassH1Vanishing.{u}) :
  GlobalReciprocity.{u}`;
- `Langlands.ClassField.Global.cyclicCyclotomicReciprocity : CyclicCyclotomicReciprocity.{u}`,
  which holds unconditionally.

This is a theorem module, not the proof of a Library proposition by itself: the hypothesis
`hH1` is discharged later, when it is combined with a proof of `IdeleClassH1Vanishing` in the
final assembly of global class field theory (task fb66219f). Its only definition is the
subgroup `Reciprocity.reciprocitySubgroup` of classes satisfying the reciprocity law; every other
declaration is a theorem.

## Statement of the main theorem

`GlobalReciprocity` says: for every family `I` of local invariant maps (one
`InvariantFamily p` for each prime `p`) that forms a class formation
(`RelativeClassFormation`) with the arithmetic normalization (`ArithmeticNormalization`), and for
every finite Galois extension `E / F` of number fields, every class
`x ∈ H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes I x`. That is, for every choice of
places of `E` above the places of `F`, only finitely many finite local invariants of `x` are
nonzero, and the sum of all finite and archimedean local invariants is `0` in `ℚ/ℤ`.

## Route of the proof and comparison with Artin–Tate

Artin–Tate first reduce to the base field `ℚ` with the transfer (Verlagerung, Lemma 3). They
then prove the cyclic cyclotomic case (Case 1). For an arbitrary class `c` they choose one
cyclic cyclotomic `K' / k` whose local degrees are divisible by the denominators of all local
invariants of `c` (the Proposition, printed p.46, PDF p.55). The restriction of the inflation of
`c` to `L = KK'` is then locally trivial. By the Hasse principle (VI §1 Theorem 2) it is trivial,
so the inflation comes from `H²(K'ˣ)`.

The Lean proof differs from this in two ways.

1. *No reduction to `ℚ`.* The Library already proves cyclic cyclotomic reciprocity over an
   arbitrary number field `F` (`CyclicReciprocity.cyclicCyclotomicReciprocity_of` in
   `CyclicReciprocityProof`). So the argument runs over `F` directly, and no transfer is needed.
2. *Prime-power decomposition instead of one `K'` for all primes.* The class `x` is first written
   as a sum of classes killed by prime powers `ℓ ^ a` (this uses that `H²` is killed by the group
   order). For a class killed by `ℓ ^ a`, a cyclic cyclotomic `K / F` of `ℓ`-power type is enough.
   It comes from the Library theorem `Langlands.Global.CyclotomicSplitting.exists_cyclic_splitting`.
   This replaces the compositum of the fields `K'_ℓ` in the proof of Artin–Tate's Proposition.

Provenance: derived from Artin–Tate VII §3 Theorem 6, with the internal changes 1 and 2 above.
The helper results `sumOfInvariantsVanishes_iff`, the closure lemmas,
the subgroup `reciprocitySubgroup`, `isGalois_cyclotomicField` and
`nonempty_algHom_cyclotomicField` are standard facts and constructions made here for use in the
main argument. The group-order annihilation result `Langlands.ClassField.Global.card_nsmul_H2_eq_zero`
is reused from `IdeleInvariantDenominator`.

## Declarations

All declarations except `cyclicCyclotomicReciprocity` and `globalReciprocity_of` are in the
namespace `Langlands.ClassField.Global.Reciprocity`.

### `cyclicCyclotomicReciprocity`

`cyclicCyclotomicReciprocity : CyclicCyclotomicReciprocity.{u}`. This is the Library theorem
`CyclicReciprocity.cyclicCyclotomicReciprocity_of` applied to the Library theorem
`UnramifiedCyclotomic.unramifiedCyclotomicFrobenius`. It is Case 1 of Artin–Tate's proof, over
an arbitrary base field.

### Imported torsion lemma

- `Langlands.ClassField.Global.card_nsmul_H2_eq_zero (A : Rep k G) (c : groupCohomology A 2) :
  Nat.card G • c = 0`, for a finite group `G`, from `IdeleInvariantDenominator`.
  Proof: the Library identity "corestriction after restriction is
  multiplication by the index" (`Langlands.Continuous.ordinaryCorestriction_index_pos`) is
  applied to the trivial subgroup. Its `H²` vanishes, so the composite is zero.

### Section `Subgroup`

Variables: a family `I` with the local image laws `hI : ∀ p, (I p).RelativeImages`, and a
finite Galois extension `E / F` of number fields.

- `sumOfInvariantsVanishes_iff`: `SumOfInvariantsVanishes I x` holds iff, for all place choices,
  the total idele invariant `totalIdeleInvariant I hI wf wi` vanishes on the principal image
  `principalIdeleCohomologyMap F E 2 x`. The finiteness part of `SumOfInvariantsVanishes` is
  automatic, because the finite idele invariants of a class have finite support. This uses the
  Library modules `IdeleTotalInvariant` and `IdeleFiniteInvariant`.
- `sumOfInvariantsVanishes_zero`, `sumOfInvariantsVanishes_add`,
  `sumOfInvariantsVanishes_zsmul`: the classes satisfying the reciprocity law form a subgroup.
  This follows from the previous item, because the total invariant is additive.
- `reciprocitySubgroup I hI F E : AddSubgroup (relativeCohomology F E 2)` (definition): the
  classes `x` with `SumOfInvariantsVanishes I x`. Membership is this property by definition
  (`mem_reciprocitySubgroup`). Zero, sums and negatives (`(-1) • x`) stay in it by the closure
  lemmas.
- `sumOfInvariantsVanishes_of_primary`: suppose every class killed by some prime power `ℓ ^ a`
  satisfies the law. Then every class does. Proof: induction on `n` over prime powers and
  coprime products (`Nat.recOnPrimeCoprime`), for classes with `n • x = 0`. If `n = ab` with
  `a`, `b` coprime, then `x = s • (a • x) + t • (b • x)` with `sa + tb = 1`, which lies in
  `reciprocitySubgroup` because `a • x` and `b • x` do. Apply this with
  `n = |Gal(E/F)|`, using `card_nsmul_H2_eq_zero`.

### Section `LocalRestriction`

- `relativeRestriction_eq_zero_of_dvd`: take a tower `F ⊆ K ⊆ M` of `p`-adic fields with `M / F`
  and `M / K` Galois, and local invariant maps `I` forming a class formation. Let
  `t ∈ H²(Gal(M/F), Mˣ)` with `n • I(t) = 0` and `n ∣ [K : F]`. Then the restriction of `t` to
  `H²(Gal(M/K), Mˣ)` is zero. Proof: by the axiom `RelativeRestriction`, the invariant of the
  restriction is `[K : F] • I(t) = 0`, and invariants are injective (`RelativeImages`). This is
  the local form of Artin–Tate VII §3 Lemma 2 (printed p.43, PDF p.52).

### Section `Compositum`

- `isGalois_cyclotomicField F E m`: if `E / F` is Galois, so is `E(μ_m) / F`
  (`CyclotomicField m E`). It is the splitting field over `F` of `p · Φ_m`, where `E` is the
  splitting field of the separable polynomial `p`.
- `nonempty_algHom_cyclotomicField F E m`: `F(μ_m)` embeds over `F` into `E(μ_m)`, by the
  universal property of splitting fields.

### Section `Main`

`sumOfInvariantsVanishes_of_pow_nsmul_eq_zero (hH1 : IdeleClassH1Vanishing.{u}) I hI ℓ a x hx`.
Assume `I` forms a class formation with the arithmetic normalization, `ℓ` is prime and
`ℓ ^ a • x = 0` for `x ∈ H²(Gal(E/F), Eˣ)`. Then `SumOfInvariantsVanishes I x`. Proof (Artin–Tate
VII §3, printed p.46, PDF p.55):

1. Let `S` be the finite set (`finite_ideleLocalSupport`) of finite places `v` of `F` at which
   `x` has a nonzero local component. `exists_cyclic_splitting F ℓ a S` gives a cyclic Galois
   `K / F` that embeds into some `F(μ_m)`. Its local degrees at places above `S` are divisible by
   `ℓ ^ a`, and all its infinite places are complex.
2. Put `L = E(μ_m)`. It is Galois over `F` and contains `K` through `F(μ_m) → E(μ_m)`. Let
   `y ∈ H²(Gal(L/F), Lˣ)` be the inflation of `x`, and `z` the restriction of `y` to
   `Gal(L/K)`.
3. `z` is zero, by the Hasse principle `eq_zero_of_local_eq_zero`, which uses `hH1`:
   - The archimedean invariants of `z` vanish, because the infinite places of `K` are complex
     (`CyclicReciprocity.archimedeanInvariant_eq_zero_of_isComplex`).
   - At a finite place `u | w' | v` of `L ⊇ K ⊇ F`, with `w` the place of `E` below `u`, the
     local component of `z` is the local restriction of the component of `y` at `u`
     (`unitsLocalMap_relativeRestriction`).
     - If `v ∈ S`, the local invariant of `y` at `u` equals that of `x` at `w`
       (`finiteLocalInvariant_relativeInflation`), so it is killed by `ℓ ^ a`. Also
       `ℓ ^ a ∣ [K_{w'} : F_v]`, so `relativeRestriction_eq_zero_of_dvd` applies.
     - If `v ∉ S`, the component of `x` at `w` is zero, hence so is the component of `y` at `u`
       (`unitsLocalMap_relativeInflation`).
4. By inflation–restriction exactness (`finiteRelativeH2InflationExactness`), `y` is the
   inflation of some `c ∈ H²(Gal(K/F), Kˣ)`. The reciprocity law is unchanged by inflation
   (`sumOfInvariantsVanishes_relativeInflation_iff`, used twice: for `E ⊆ L` and for `K ⊆ L`).
   So it holds for `x` because it holds for `c`, by `cyclicCyclotomicReciprocity`.

### `globalReciprocity_of`

`globalReciprocity_of (hH1 : IdeleClassH1Vanishing.{u}) : GlobalReciprocity.{u}`. Apply
`sumOfInvariantsVanishes_of_primary` and then `sumOfInvariantsVanishes_of_pow_nsmul_eq_zero`
for each prime power.

## Imports

- `Langlands.ClassField.Global.ReciprocityTower`: tower formulas for local components and
  invariants, and the Hasse principle.
- `Langlands.ClassField.Global.CyclicReciprocityProof` and
  `Langlands.ClassField.Global.UnramifiedCyclotomicProof`: cyclic cyclotomic reciprocity.
- `Langlands.ClassField.Global.IdeleInvariantDenominator`: total idele invariants and
  group-order annihilation of degree-two cohomology.
- `Langlands.ClassFieldTheory.Local.RelativeH2InflationProof`: inflation–restriction exactness.
- `Langlands.Global.Arithmetic.CyclotomicSplitting`: the cyclic cyclotomic splitting field.

## Sources

- E. Artin, J. Tate, *Class Field Theory*, AMS Chelsea 2009 (source
  `artin-tate-2009-class-field-theory`). Chapter VII §3: Lemmas 1–2, printed p.43 (PDF p.52);
  Theorem 6 with Case 1, printed p.45 (PDF p.54); the argument for arbitrary normal extensions
  and the Proposition, printed p.46 (PDF p.55). Chapter VI §1 Theorem 2 (Hasse principle),
  printed p.19 (PDF p.28).
