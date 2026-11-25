# Proof of the geometrically normalized lift of finite idèle-class characters

Module `Langlands.Galois.FiniteHeckeAvatarLiftProof`, name space
`Langlands.GaloisRepresentation`. It proves the published `FiniteHeckeAvatarLiftStatement` and,
unconditionally, `FiniteGeometricArtinLifting` of
[`FiniteHeckeAvatarLift`](FiniteHeckeAvatarLift.lean), and describes the lift through the
global Artin map `geometricArtinMap`
([`ArtinMap`](../ClassFieldTheory/Global/Artin/ArtinMap.md)). The three premises are proved in
[`ClassFieldProof`](../Global/Arithmetic/ClassFieldProof.md) (`finiteAbelianClassFieldExistence`),
[`FiniteArtinUnramifiedCriterionProof`](../Global/Arithmetic/FiniteArtinUnramifiedCriterionProof.md)
(`finiteArtinUnramifiedCriterion`) and
[`FiniteUnramifiedGaloisRestrictionProof`](FiniteUnramifiedGaloisRestrictionProof.md)
(`finiteUnramifiedGaloisRestriction`).

## Main declarations

Throughout, `K : Type uK` with `[Field K] [NumberField K]`, `A : Type uA` with
`[TopologicalSpace A]`; `FinitePlace`, `FiniteCompletion`, `IdeleClasses`,
`finiteClassInclusion` are those of `Langlands.Global`, and `IsTrivialOnLocalUnits`,
`MatchesGeometricArtinOutside` those of `FiniteHeckeAvatarLift`. The first theorem assumes
`[Group A]`, all the others `[CommGroup A]`.

```lean
theorem MatchesGeometricArtinOutside.isTrivialOnLocalUnits [Group A]
    {S : Finset (FinitePlace K)} {ξ : IdeleClasses K →ₜ* A}
    {ψ : Field.absoluteGaloisGroup K →ₜ* A} (h : MatchesGeometricArtinOutside S ξ ψ)
    {v : FinitePlace K} (hv : v ∉ S) : IsTrivialOnLocalUnits ξ v

theorem MatchesGeometricArtinOutside.unique [T2Space A] {S : Finset (FinitePlace K)}
    {ξ : IdeleClasses K →ₜ* A} {ψ₁ ψ₂ : Field.absoluteGaloisGroup K →ₜ* A}
    (h₁ : MatchesGeometricArtinOutside S ξ ψ₁) (h₂ : MatchesGeometricArtinOutside S ξ ψ₂) :
    ψ₁ = ψ₂

theorem exists_matchesGeometricArtinOutside
    (h1 : FiniteAbelianClassFieldExistenceStatement.{uK})
    (h2 : FiniteArtinUnramifiedCriterionStatement.{uK, uK})
    (h3 : FiniteUnramifiedGaloisRestrictionStatement.{uK})
    [Finite A] [DiscreteTopology A] (ξ : IdeleClasses K →ₜ* A) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, IsTrivialOnLocalUnits ξ v) :
    ∃ ψ : Field.absoluteGaloisGroup K →ₜ* A, MatchesGeometricArtinOutside S ξ ψ

theorem MatchesGeometricArtinOutside.apply_eq_of_geometricArtinMap [Finite A]
    [DiscreteTopology A] {S : Finset (FinitePlace K)} {ξ : IdeleClasses K →ₜ* A}
    {ψ : Field.absoluteGaloisGroup K →ₜ* A} (hψ : MatchesGeometricArtinOutside S ξ ψ)
    (x : IdeleClasses K) (σ : Field.absoluteGaloisGroup K)
    (hσ : LocalClassField.absoluteAbelianizationProjection K σ = geometricArtinMap K x) :
    ψ σ = ξ x

theorem finiteHeckeAvatarLift : FiniteHeckeAvatarLiftStatement.{uK, uA}

theorem finiteGeometricArtinLifting : FiniteGeometricArtinLifting.{uK, uA}
```

Here `LocalClassField.absoluteAbelianizationProjection K` is the projection of the absolute
Galois group onto its topological abelianization (`Langlands/ClassFieldTheory/Local/Galois.lean`)
and `geometricArtinMap K : IdeleClasses K →ₜ* Field.absoluteGaloisGroupAbelianization K` is the
Library's global Artin map in the geometric normalization (`ArtinMap`), opened from
`Langlands.ClassFieldTheory.Global.Artin`.

The statements, as published (not changed):

```lean
def FiniteGeometricArtinLifting : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K]
    (A : Type uA) [CommGroup A] [Finite A],
    letI : TopologicalSpace A := ⊥
    ∀ (ξ : IdeleClasses K →ₜ* A) (S : Finset (FinitePlace K)),
      (∀ v ∉ S, IsTrivialOnLocalUnits ξ v) →
      ∃! ψ : Field.absoluteGaloisGroup K →ₜ* A, MatchesGeometricArtinOutside S ξ ψ

def FiniteHeckeAvatarLiftStatement : Prop :=
  FiniteAbelianClassFieldExistenceStatement.{uK} →
  FiniteArtinUnramifiedCriterionStatement.{uK, uK} →
  FiniteUnramifiedGaloisRestrictionStatement.{uK} →
  FiniteGeometricArtinLifting.{uK, uA}
```

with `MatchesGeometricArtinOutside S ξ ψ` meaning: for every finite place `v ∉ S`, `ψ` is `1` on
the image of local inertia under `localToGlobalGalois v`, and for every uniformizer `π` of the
completion (`Valued.v π = WithZero.exp (-1)`) and every geometric Frobenius lift `g` at `v`,
`ψ (localToGlobalGalois v g) = ξ (finiteClassInclusion K v π)`.

In words:

* `isTrivialOnLocalUnits`: a character `ξ` that is matched outside `S` by some `ψ` is trivial on
  the local units at every `v ∉ S`. So the hypothesis of `FiniteGeometricArtinLifting` is
  necessary.
* `unique`: two continuous characters into a commutative Hausdorff group that match `ξ`
  outside `S` are equal.
* `exists_matchesGeometricArtinOutside`: existence from the three premises, for a finite discrete
  coefficient group.
* `apply_eq_of_geometricArtinMap`: the lift is `ξ` carried through the global Artin map. If `ψ`
  matches `ξ` outside some `S` and `σ` maps to `geometricArtinMap K x` in the abelianization, then
  `ψ σ = ξ x`. No triviality hypothesis on `ξ` is needed: it follows from the matching by the
  first theorem.
* `finiteHeckeAvatarLift` and `finiteGeometricArtinLifting` have the two statements as their
  types, with the statements' universe parameters `uK, uA` in this order.

Lean reports that each of the six theorems depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## Proofs

**Triviality on units.** Let `a` be a local unit at `v ∉ S`: `a` and `a⁻¹` lie in the valuation
ring, so `Valued.v a = 1`. For a uniformizer `π` (`exists_uniformizer`) the product `a π` is a
uniformizer, and for a geometric Frobenius lift `g` (`exists_geometricFrobeniusLift`) the matching
gives `ξ (a π) = ψ (localToGlobalGalois v g) = ξ π`; cancelling `ξ π` gives `ξ a = 1`.

**Uniqueness.** The set where `ψ₁` and `ψ₂` agree is closed (`A` is Hausdorff). It contains the
images `globalGeometricFrobenius v` of the chosen geometric Frobenius lifts at the places
`v ∉ S`, where both are `ξ π` for a uniformizer `π`, and hence their conjugates, since `A` is
commutative. These conjugates (at places of prime residue cardinality outside `S`) are dense
(`dense_conjugates_globalGeometricFrobenius_degreeOne`, `FrobeniusDensity`, from finite
Chebotarev in degree one), so the closed set is everything. Neither the premises nor class field
theory enter.

**Existence.** `ξ` is continuous into a discrete group, so its kernel `H` is open, and of finite
index because `A` is finite (`Subgroup.finiteIndex_ker`).

1. The first premise gives a finite Galois `L ⊆ AlgebraicClosure K` with commutative Galois group
   and a continuous surjective `ρ : IdeleClasses K → Gal(L/K)` (discrete topology) with
   `HasArithmeticArtinNormalization` and kernel `H`.
2. Since `ρ` is surjective with the kernel of `ξ`, `ξ = θ ∘ ρ` for an injective homomorphism
   `θ : Gal(L/K) → A` (Mathlib's `MonoidHom.liftOfRightInverse`, as in `ClassFieldProof`).
3. The lift is `ψ g = θ ((g|_L)⁻¹)`, with `g|_L = finiteGaloisRestriction L g`. It is a
   homomorphism because `A` is commutative, and continuous because the Krull topology on
   `Gal(L/K)` is discrete.
4. Let `v ∉ S`. `ρ` kills the local units at `v`, because `ξ` does and `θ` is injective. Take a
   prime `w` of `L` above `v` (`exists_liesOver`). The second premise makes `L / K` unramified at
   `w`. The third premise makes local inertia restrict to `1`, so `ψ` kills inertia. It also makes
   the restriction of `localToGlobalGalois v g⁻¹` an arithmetic Frobenius at `w`, for every
   geometric Frobenius lift `g`. So does `ρ π` for every uniformizer `π`, by the normalization of
   `ρ`. At the unramified `w` the two are equal (`eq_of_isArithFrobAt_mapAlgHom`), so
   `ψ (localToGlobalGalois v g) = θ (ρ π) = ξ π`.

`finiteHeckeAvatarLift` combines existence and uniqueness for the topology `⊥` on `A`;
`finiteGeometricArtinLifting` applies it to the three proved premises.

**The lift through `geometricArtinMap`.** Let `ψ` match `ξ` outside `S`, so `ξ` is trivial on the
local units outside `S`. Construct `L`, `ρ`, `θ` as above from the proved premises. By uniqueness
`ψ` is the lift `g ↦ θ ((g|_L)⁻¹)`. By the uniqueness of normalized maps
(`eq_of_hasArithmeticArtinNormalization`, `ArtinUniqueness`), `ρ` is the arithmetic Artin map
`arithmeticFiniteArtin K L` (`FiniteArtin`). By `restrictNormalHom_eq_inv_arithmeticFiniteArtin`
(`ArtinMap`), a lift `σ` of `geometricArtinMap K x` restricts on `L` to
`(arithmeticFiniteArtin K L x)⁻¹`. So `ψ σ = θ (arithmeticFiniteArtin K L x) = θ (ρ x) = ξ x`.

Three private declarations of the file carry the construction: the lift
`g ↦ θ ((g|_L)⁻¹)`, the factorization of step 2, and the matching of step 4. The last takes the
second and third premises as hypotheses; existence uses it with the premises given, the
description with the proved premises.

## Declarations used

- From the Library: `finiteAbelianClassFieldExistence` (`ClassFieldProof`),
  `finiteArtinUnramifiedCriterion` (`FiniteArtinUnramifiedCriterionProof`),
  `finiteUnramifiedGaloisRestriction` (`FiniteUnramifiedGaloisRestrictionProof`);
  `dense_conjugates_globalGeometricFrobenius_degreeOne`, `globalGeometricFrobenius`
  (`FrobeniusDensity`); `geometricFrobeniusLift`, `geometricFrobeniusLift_spec`,
  `exists_geometricFrobeniusLift` (`FrobeniusLift`); `finiteGaloisRestriction`,
  `localToGlobalGalois` (`FiniteUnramifiedGaloisRestriction`); `exists_uniformizer`,
  `exists_liesOver`, `eq_of_isArithFrobAt_mapAlgHom`, `eq_of_hasArithmeticArtinNormalization`
  (`ArtinUniqueness`); `geometricArtinMap`, `restrictNormalHom_eq_inv_arithmeticFiniteArtin`
  (`ArtinMap`); `arithmeticFiniteArtin`, `arithmeticFiniteArtinBot` (`FiniteArtin`);
  `arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization`);
  `HasArithmeticArtinNormalization` (`ClassFieldStatement`).
- From Mathlib: `Subgroup.finiteIndex_ker`, `MonoidHom.liftOfRightInverse`,
  `MonoidHom.liftOfRightInverse_comp_apply`, `injective_iff_map_eq_one`, `Submonoid.mem_units_iff`,
  `mul_le_of_le_one_right'`, `isClosed_eq`, `closure_minimal`, `Dense.closure_eq`,
  `continuous_of_discreteTopology`, `krullTopology_discreteTopology_of_finiteDimensional` (an
  instance), `IsMulCommutative.of_comm`.

## Sources

- Milne, *Class Field Theory* (v4.03, 2020), Chapter V, §5: Proposition 5.2, p. 178 (the global
  Artin map `φ_K : 𝕀_K → Gal(K^ab/K)`, compatible with the local Artin maps; by its proof a unit
  at a place where `L_w / K_v` is unramified maps to `1`); Theorem 5.3, pp. 178–179 (reciprocity
  law: `φ_{L/K} : C_K / Nm(C_L) ≅ Gal(L/K)`); Theorem 5.5, p. 179, with the paragraph after it
  (existence: every open subgroup `N` of finite index of `C_K` is `Nm(C_L) = Ker(φ_{L/K})` for a
  unique abelian `L ⊆ K^al`, its class field); Remark 5.7(a), p. 179 (`φ_K` is surjective). Milne's local Artin maps send a prime
  element to the arithmetic Frobenius: Chapter I, Theorem 1.1(a), p. 20. The finite maps
  `ρ` above have this arithmetic normalization. The lift is geometrically normalized: it takes
  geometric Frobenius lifts to the values at uniformizers, which is why it is built from
  `(g|_L)⁻¹`, and why `geometricArtinMap` is the inverse of Milne's `φ_K`.
- Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapter VII, §13, Theorem (13.4), p. 545
  (Čebotarev density theorem), behind the density of Frobenius conjugates used for uniqueness;
  Chapter I, §9, Exercise 2, p. 58 (uniqueness of the Frobenius automorphism at an unramified
  prime).
