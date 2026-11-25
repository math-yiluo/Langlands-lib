# Density of actual geometric Frobenius conjugates

The global geometric Frobenius at a finite place is the image of the Library's chosen geometric lift under the same map of absolute Galois groups used for local restriction. The theorem shows that conjugates of these elements at places of prime residue cardinality outside a finite set are dense in the Krull topology.

For a subextension `E` of the absolute algebraic closure, the chosen extension of the completion embedding sends the global integers of `E` into the spectral valuation ring of the algebraic closure of the local completion. The kernel of their reduction is a prime of `E` above the given place, the induced prime. For normal `E`, the inverse of every geometric Frobenius lift acts on this reduction by the residue cardinality power, so its restricted global action is an arithmetic Frobenius at the induced prime. The proof of `FiniteUnramifiedGaloisRestrictionStatement` ([`FiniteUnramifiedGaloisRestrictionProof`](FiniteUnramifiedGaloisRestrictionProof.md)) uses these comparisons.

For density, take an unramified prime supplied by finite Chebotarev in degree one. Transitivity on primes and uniqueness of arithmetic Frobenius there give the desired conjugacy. The conjugating automorphism extends to the full algebraic closure. Every nonempty open set contains a coset of the fixing subgroup of a finite normal subextension, so the finite degree-one realization meets every such open set.

## Declarations

Module `Langlands.Galois.FrobeniusDensity`, name space `Langlands.GaloisRepresentation`. Throughout, `K : Type u` with `[Field K] [NumberField K]`, `v : Global.FinitePlace K` and `E : IntermediateField K (AlgebraicClosure K)`. The file's local notations are `Kv = Global.FiniteCompletion K v`, `Cv = AlgebraicClosure Kv`, `Ov = LocalGalois.baseIntegers Kv` (the valuation ring of `Kv`) and `Ic = LocalGalois.extensionIntegers Kv Cv` (the spectral valuation ring of `Cv`). `𝓞` is `NumberField.RingOfIntegers`, and `RingOfIntegers.mapAlgHom` is `NumberField.RingOfIntegers.mapAlgHom`. `LocalGroup v`, `LocalResidueClosure v`, `IsGeometricFrobeniusLift` and `residueCardinality` are those of `CompatibleFamily`. `geometricFrobeniusLift v` is the chosen lift of `FrobeniusLift`, and `chosenClosureEmbedding` is the extension to the algebraic closures through which `Field.absoluteGaloisGroup.map` is defined (`ClosureRestriction`).

```lean
def globalGeometricFrobenius (v : Global.FinitePlace K) : Field.absoluteGaloisGroup K :=
  Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) (geometricFrobeniusLift v)

def finiteClosureEmbedding (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) : E →+* Cv

def finiteIntegersMap (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) : (𝓞 E) →+* Ic

theorem finiteIntegersMap_base (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) (x : 𝓞 K) :
    finiteIntegersMap v E (algebraMap (𝓞 K) (𝓞 E) x) =
      algebraMap Ov Ic (Global.CompletionResidue.integersMap K v x)

def finiteResidueMap (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) : (𝓞 E) →+* LocalResidueClosure v

def inducedPrime (v : Global.FinitePlace K) (E : IntermediateField K (AlgebraicClosure K)) :
    Ideal (𝓞 E)

theorem inducedPrime_isPrime (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) : (inducedPrime v E).IsPrime

theorem inducedPrime_liesOver (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) : (inducedPrime v E).LiesOver v.asIdeal

theorem finiteClosureEmbedding_restrict (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] (g : LocalGroup v) (x : E) :
    finiteClosureEmbedding v E (AlgEquiv.restrictNormalHom E
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g) x) =
      AlgEquiv.toRingEquiv g (finiteClosureEmbedding v E x)

theorem arithmeticFrobeniusAt_inducedPrime (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) :
    (RingOfIntegers.mapAlgHom (AlgEquiv.restrictNormalHom E
      ((Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g)⁻¹))).IsArithFrobAt
        (inducedPrime v E)

theorem arithmeticFrobeniusAt_inducedPrime_globalGeometricFrobenius (v : Global.FinitePlace K)
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    (RingOfIntegers.mapAlgHom (AlgEquiv.restrictNormalHom E
      ((globalGeometricFrobenius v)⁻¹))).IsArithFrobAt (inducedPrime v E)

theorem dense_conjugates_globalGeometricFrobenius_degreeOne
    (S : Finset (Global.FinitePlace K)) :
    Dense {g : Field.absoluteGaloisGroup K | ∃ v : Global.FinitePlace K,
      v ∉ S ∧ (residueCardinality v).Prime ∧
        ∃ t : Field.absoluteGaloisGroup K, t * globalGeometricFrobenius v * t⁻¹ = g}
```

What the declarations are:

* `finiteClosureEmbedding v E` is the inclusion of `E` into `AlgebraicClosure K` followed by `chosenClosureEmbedding (NumberField.FinitePlace.embedding v)`.
* `finiteIntegersMap v E` is the same map on `𝓞 E`, with values in `Ic`; integral elements lie in the spectral valuation ring. On `𝓞 K` it is the map to the integers of the completion (`finiteIntegersMap_base`).
* `finiteResidueMap v E` is `finiteIntegersMap v E` followed by reduction to the residue field `LocalResidueClosure v` of `Ic`.
* `inducedPrime v E` is the kernel of `finiteResidueMap v E`, a prime (`inducedPrime_isPrime`) lying over `v` (`inducedPrime_liesOver`, because reduction on `𝓞 K` vanishes exactly on `v.asIdeal`).
* `finiteClosureEmbedding_restrict` says that for normal `E` the embedding is equivariant: the global image of a local automorphism `g`, restricted to `E`, corresponds to `g` acting on `Cv`.
* `arithmeticFrobeniusAt_inducedPrime` holds for every geometric Frobenius lift `g` at `v`. `arithmeticFrobeniusAt_inducedPrime_globalGeometricFrobenius` is its case for the chosen lift; the density proof uses it.

`globalGeometricFrobenius`, `dense_conjugates_globalGeometricFrobenius_degreeOne` and a private lemma `exists_frobenius_conjugate_restrict` (each element of a finite Galois quotient is the restriction of a conjugate of some `globalGeometricFrobenius v` with `v` of prime residue cardinality outside `S`) complete the file.

## Proofs

`arithmeticFrobeniusAt_inducedPrime`: the residue cardinality of `v` is the cardinality of `𝓞 K / v.asIdeal`, the exponent in Mathlib's `IsArithFrobAt` (`Ideal.absNorm_apply`, `Submodule.cardQuot_apply`). By `finiteClosureEmbedding_restrict`, applying the restricted automorphism and then `finiteIntegersMap v E` is applying `g⁻¹` (as `LocalGalois.integerAut`) after `finiteIntegersMap v E`. On residues, `g⁻¹` acts as `localResidueAction v g⁻¹` (`LocalGalois.residueHom_apply`), which is the residue cardinality power because `g` is a geometric Frobenius lift. So the restricted automorphism is congruent to the power map modulo the kernel of the reduction.

`dense_conjugates_globalGeometricFrobenius_degreeOne`: a neighbourhood of `g` contains `g` times the fixing subgroup of a finite normal subextension `E`. Finite Chebotarev in degree one (`Global.chebotarevDegreeOne`) gives a place `v` outside `S` of prime residue cardinality and an unramified prime `q` above it with arithmetic Frobenius the inverse of the restriction of `g`. The induced prime and `q` are conjugate under `E ≃ₐ[K] E` (`Ideal.exists_smul_eq_of_isGaloisGroup`). Conjugating the Frobenius at the induced prime (`IsArithFrobAt.conj`) and using uniqueness at the unramified `q` (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`) identifies the restrictions. The conjugating element lifts to the absolute Galois group (`AlgEquiv.restrictNormalHom_surjective`).

## Sources

- Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VII, §13, Theorem (13.4), p. 545 (Čebotarev density theorem). Chapter I, §9: Proposition (9.1), p. 54 (transitivity on the primes above `p`) and Exercise 2, p. 58 (uniqueness of the Frobenius automorphism at an unramified prime). Chapter II, §9, Proposition (9.6), p. 170 (the Galois group of the completion is the decomposition group, by restriction).
