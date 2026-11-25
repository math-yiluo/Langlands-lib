# Proof of the inertia and Frobenius restriction statement

Module `Langlands.Galois.FiniteUnramifiedGaloisRestrictionProof`, name space
`Langlands.GaloisRepresentation`. It proves the published
`FiniteUnramifiedGaloisRestrictionStatement` of
[`FiniteUnramifiedGaloisRestriction`](FiniteUnramifiedGaloisRestriction.lean), the third premise
of `FiniteHeckeAvatarLiftStatement`. It uses no class field theory and nothing of the NYLL copy:
it imports `FiniteUnramifiedGaloisRestriction`, [`FrobeniusDensity`](FrobeniusDensity.md) (the
comparison of a subextension of `AlgebraicClosure K` with the completion at `v`) and
`Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness` (for the uniqueness of an arithmetic
Frobenius at an unramified prime; that file uses only Mathlib and the Library).

## Main declarations

Throughout, `K : Type uK` with `[Field K] [NumberField K]`; `FinitePlace` is
`Langlands.Global.FinitePlace`, `𝓞` is `NumberField.RingOfIntegers`, and `LocalGroup v`,
`localInertia v`, `localResidueAction v`, `IsGeometricFrobeniusLift` are those of
`Langlands/Galois/CompatibleFamily.lean`. In the second and third theorem
`E : IntermediateField K (AlgebraicClosure K)` with `[FiniteDimensional K E] [IsGalois K E]`.

```lean
theorem isGeometricFrobeniusLift_mul_of_mem_localInertia {v : FinitePlace K}
    {g i : LocalGroup v} (hg : IsGeometricFrobeniusLift v g) (hi : i ∈ localInertia v) :
    IsGeometricFrobeniusLift v (g * i)

theorem finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt [NumberField E]
    (hcomm : ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) (v : FinitePlace K) (w : FinitePlace E)
    (hw : w.asIdeal.LiesOver v.asIdeal) {g : LocalGroup v} (hg : IsGeometricFrobeniusLift v g) :
    (NumberField.RingOfIntegers.mapAlgHom
      (finiteGaloisRestriction E (localToGlobalGalois v g⁻¹))).IsArithFrobAt w.asIdeal

theorem finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia [NumberField E]
    (hcomm : ∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) (v : FinitePlace K) (w : FinitePlace E)
    (hw : w.asIdeal.LiesOver v.asIdeal) (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    {i : LocalGroup v} (hi : i ∈ localInertia v) :
    finiteGaloisRestriction E (localToGlobalGalois v i) = 1

theorem finiteUnramifiedGaloisRestriction : FiniteUnramifiedGaloisRestrictionStatement.{uK}
```

The statement, as published (not changed):

```lean
def FiniteUnramifiedGaloisRestrictionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [IsGalois K E],
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : NumberField E := NumberField.of_module_finite K E
    ∀ (v : FinitePlace K) (w : FinitePlace E),
      w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal →
      (∀ i : localInertia v, finiteGaloisRestriction E (localToGlobalGalois v i.val) = 1) ∧
      ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
        (NumberField.RingOfIntegers.mapAlgHom
          (finiteGaloisRestriction E (localToGlobalGalois v g⁻¹))).IsArithFrobAt w.asIdeal
```

In words: let `E` be a finite abelian subextension of `AlgebraicClosure K` and `w` a prime of `E`
above the finite place `v` of `K`. `localToGlobalGalois v` maps the absolute Galois group of the
completion `K_v` to that of `K` (through the chosen extension of the completion embedding to the
algebraic closures), and `finiteGaloisRestriction E` restricts to `E`.

* `isGeometricFrobeniusLift_mul_of_mem_localInertia`: a geometric Frobenius lift times an element
  of local inertia (the kernel of the residue action) is a geometric Frobenius lift.
* `finiteGaloisRestriction_localToGlobalGalois_inv_isArithFrobAt`: the inverse of every geometric
  Frobenius lift restricts to an arithmetic Frobenius (Mathlib's `AlgHom.IsArithFrobAt` on `𝓞 E`)
  at `w`. No unramifiedness is assumed: in an abelian extension the restriction does not depend
  on the prime above `v`.
* `finiteGaloisRestriction_localToGlobalGalois_of_mem_localInertia`: if `E / K` is unramified at
  `w`, local inertia restricts to `1`.
* `finiteUnramifiedGaloisRestriction` is the conjunction of the last two; its type is the
  statement, with the statement's universe parameter `uK`. The `NumberField E` instance of the
  statement and the one of the two theorems are propositions, hence equal.

Lean reports that each of the four theorems depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## Proofs

1. **Frobenius at the induced prime.** `FrobeniusDensity` maps the integers of `E` into the
   spectral valuation ring of the algebraic closure of `K_v` by the chosen closure embedding; the
   kernel of the reduction is a prime `inducedPrime v E` above `v`
   (`inducedPrime_isPrime`, `inducedPrime_liesOver`), and for every geometric Frobenius lift `g`
   the restriction to `E` of the inverse of the image of `g` is an arithmetic Frobenius at it
   (`arithmeticFrobeniusAt_inducedPrime`).
2. **Transport to `w`.** The group `E ≃ₐ[K] E` is a Galois group of `𝓞 E` over `𝓞 K` (a Mathlib
   instance, from `IsGaloisGroup.of_isFractionRing`), so it acts transitively on the primes above
   `v` (Mathlib's `Ideal.exists_smul_eq_of_isGaloisGroup`): `a • inducedPrime v E = w` for some
   `a`. Conjugation moves arithmetic Frobenius elements (`IsArithFrobAt.conj`): `a σ a⁻¹` is one
   at `w`, and `a σ a⁻¹ = σ` by the commutativity hypothesis. With `map_inv` for
   `localToGlobalGalois v` this is the second theorem.
3. **Inertia.** For `i` in local inertia the residue action of `i⁻¹` is trivial, so for a
   geometric Frobenius lift `g` (`exists_geometricFrobeniusLift`) the inverse of `g * i` acts on
   residues as the inverse of `g` does: `g * i` is a geometric Frobenius lift (first theorem). By
   step 2 the restrictions of the images of `(g * i)⁻¹` and `g⁻¹` are both arithmetic Frobenius
   elements at `w`; at the unramified prime `w` they are equal
   (`eq_of_isArithFrobAt_mapAlgHom`, from Mathlib's `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`),
   and cancelling the image of `g⁻¹` leaves that the image of `i` restricts to `1`.
4. **Forms.** `finiteGaloisRestriction E` is `AlgEquiv.restrictNormalHom E` with the Krull
   topology and `localToGlobalGalois v` is `Field.absoluteGaloisGroup.map
   (NumberField.FinitePlace.embedding v)`, both by definition, so the statements of
   `FrobeniusDensity` apply as they stand.

Unramifiedness is needed only at `w`, where it is the hypothesis: inertia is treated at `w`
after the transport of step 2, not at the induced prime.

## Declarations used

- From the Library: `inducedPrime`, `inducedPrime_isPrime`, `inducedPrime_liesOver`,
  `arithmeticFrobeniusAt_inducedPrime` (`FrobeniusDensity`); `exists_geometricFrobeniusLift`
  (`FrobeniusLift`); `localResidueAction`, `localInertia`, `IsGeometricFrobeniusLift`, `LocalGroup`
  (`CompatibleFamily`); `finiteGaloisRestriction`, `localToGlobalGalois`
  (`FiniteUnramifiedGaloisRestriction`); `ClassFieldTheory.Global.Artin.eq_of_isArithFrobAt_mapAlgHom`
  (`ArtinUniqueness`).
- From Mathlib: `Ideal.exists_smul_eq_of_isGaloisGroup`, `IsArithFrobAt.conj`,
  `IsGaloisGroup.of_isFractionRing` (through an instance), `MonoidHom.mem_ker`, `map_inv`,
  `map_mul`.

## Sources

- Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter I, §9: Proposition (9.1), p. 54
  (the Galois group acts transitively on the primes above `p`) and, on the same page, the
  decomposition group of a conjugate prime is the conjugate subgroup; Proposition (9.4), p. 56,
  Definition (9.5) and Proposition (9.6), p. 57 (decomposition group onto the Galois group of the
  residue extension, inertia group the kernel), p. 58 (`I_𝔓 = 1` exactly when `𝔭` is unramified)
  and Exercise 2, p. 58 (at an unramified prime there is exactly one `φ_𝔓` with
  `φ_𝔓 a ≡ a^q mod 𝔓`, the Frobenius automorphism). Chapter II, §9, Proposition (9.6), p. 170:
  restriction identifies the Galois group of the completion `L_w / K_v` with the decomposition
  group and its inertia group with the inertia group.
- Milne, *Class Field Theory* (v4.03, 2020), Chapter V, §5, p. 177 (`D(w) ≃ Gal(L_w/K_v)`) and
  Lemma 5.1, pp. 177–178 (for abelian `L / K` the decomposition group does not depend on the
  prime above `v`, since `D(σw) = σ D(w) σ⁻¹`).

The Lean statement is phrased with the Library's local Galois group of the completion, its
residue action and Mathlib's `IsArithFrobAt`; the decomposition group itself does not appear.
