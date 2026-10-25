# Same-base conjugacy as inflation along a degree-one tower

This pair is authored by Worker 272. It proves that, over a fixed base field,
the actual conjugacy transport of relative cohomology along an algebra
equivalence is the actual inflation map for the algebra structure that the
equivalence induces. That structure is the reusable definition
`algEquivAlgebra`. As a consequence, every local invariant family satisfying
`InflationCompatibility` is natural under algebra equivalences over the same
p-adic base. It makes no change-of-base claim and assumes no
`RelativeConjugacy` law.

Module: `Langlands.ClassFieldTheory.Local.SameBaseConjugacy`, namespace
`Langlands.ClassFieldTheory.Local`, universe `u`. It imports the published
modules `Langlands.ClassFieldTheory.Local.Conjugacy` and
`Langlands.ClassFieldTheory.Local.ClassFormation`. No Library file is edited.

## Declarations

In the section `SameBase`, the variables are
`{K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]`.

1. `@[instance_reducible] def algEquivAlgebra (e : L ≃ₐ[K] M) : Algebra L M :=
   e.toRingHom.toAlgebra`.
   This is the reusable construction of the unit: the `L`-algebra structure
   on `M` whose algebra map is the ring homomorphism underlying `e`. It is a
   plain definition, not an instance. Statements and proofs install it
   locally with `letI` or `let`. The attribute `@[instance_reducible]` follows
   Lean's advice for definitions of class type that are used as instances.

2. `algebraMap_algEquivAlgebra (e : L ≃ₐ[K] M) (x : L) :
   letI : Algebra L M := algEquivAlgebra e; algebraMap L M x = e x`.
   The algebra map of `algEquivAlgebra e` is `e`. The proof is `rfl`.

3. `compatibleFieldEquivalences_refl_algEquiv (e : L ≃ₐ[K] M) :
   CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv`.
   An algebra equivalence over `K` gives a commuting square over the identity
   of `K`. The proof is `e.commutes`.

4. `isScalarTower_algEquiv (e : L ≃ₐ[K] M) :
   letI : Algebra L M := algEquivAlgebra e; IsScalarTower K L M`.
   For the `L`-algebra structure `algEquivAlgebra e`, the tower `K → L → M`
   commutes. The proof is `IsScalarTower.of_algebraMap_eq` with `e.commutes`.

5. `finiteDimensional_algEquiv (e : L ≃ₐ[K] M) :
   letI : Algebra L M := algEquivAlgebra e; FiniteDimensional L M`.
   For the same structure, `M` is finite-dimensional over `L` (it is
   one-dimensional). The proof is `Module.Finite.of_surjective`: the
   `L`-linear map `Algebra.linearMap L M`, which is `e` as a function, is
   surjective.

6. `restrictNormalHom_eq_galoisConjugacy_symm (e : L ≃ₐ[K] M)
   [Algebra L M] [IsScalarTower K L M] [Normal K L]
   (he : ∀ x : L, algebraMap L M x = e x)
   (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) :
   (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)) =
     ((galoisConjugacy (RingEquiv.refl K) e.toRingEquiv h).symm :
       Gal(M/K) →* Gal(L/K))`.
   Let `M` carry any `L`-algebra structure whose algebra map is `e`. Then
   normal restriction `τ ↦ τ|L` equals the inverse of the actual Galois-group
   conjugacy `σ ↦ e ∘ σ ∘ e⁻¹`, that is, `τ ↦ e⁻¹ ∘ τ ∘ e`. The proof applies
   `e.injective` to both sides at `x`. It then uses
   `AlgEquiv.restrictNormal_commutes`, which says
   `algebraMap L M (τ|L x) = τ (algebraMap L M x)`, together with `he`.

7. `relativeConjugacy_refl_hom_eq_relativeInflation (e : L ≃ₐ[K] M)
   [Algebra L M] [IsScalarTower K L M] [Normal K L]
   (he : ∀ x : L, algebraMap L M x = e x)
   (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) (n : ℕ) :
   (relativeConjugacy (RingEquiv.refl K) e.toRingEquiv h n).hom =
     relativeInflation K L M n`.
   In every degree `n`, the forward map of the actual conjugacy isomorphism
   from `Conjugacy.lean` is the actual inflation map from `Cohomology.lean`.
   Both are `groupCohomology.map` applied to a group homomorphism
   `Gal(M/K) →* Gal(L/K)` and a coefficient morphism. After unfolding
   `relativeConjugacy` and `groupCohomology.mapIso`, the proof uses
   `groupCohomology.map_congr`. The group homomorphisms agree by declaration 6.
   The coefficient maps agree on each unit by `Units.ext` and `he`:
   `unitsConjugacy` applies `e`, and the inflation coefficient map
   `inflationCoefficients` applies `algebraMap L M`.

8. `relativeConjugacy_refl_hom_eq_relativeInflation_algEquivAlgebra
   (e : L ≃ₐ[K] M) [Normal K L]
   (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) (n : ℕ) :
   letI : Algebra L M := algEquivAlgebra e;
   letI : IsScalarTower K L M := isScalarTower_algEquiv e;
   (relativeConjugacy (RingEquiv.refl K) e.toRingEquiv h n).hom =
     relativeInflation K L M n`.
   This is declaration 7 for the algebra `algEquivAlgebra e`, with `he`
   given by declaration 2.

In the namespace `InvariantFamily`, the variables are
`{p : ℕ} [Fact p.Prime]`.

9. `InvariantFamily.relative_relativeConjugacy_refl_of_inflationCompatibility
   (I : InvariantFamily.{u,u} p) (hI : I.InflationCompatibility)
   (F : PadicField.{u} p) {L M : Type u} [Field L] [Field M]
   [Algebra F.Carrier L] [Algebra F.Carrier M]
   [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
   [IsGalois F.Carrier L] [IsGalois F.Carrier M]
   (e : L ≃ₐ[F.Carrier] M)
   (h : CompatibleFieldEquivalences (RingEquiv.refl F.Carrier) e.toRingEquiv)
   (x : relativeCohomology F.Carrier L 2) :
   I.relative F M ((relativeConjugacy (RingEquiv.refl F.Carrier) e.toRingEquiv h 2).hom x) =
     I.relative F L x`.
   This is the main result. Let `I` be a supplied invariant family whose
   relative invariants are unchanged by inflation. Then the relative invariant
   of `M/F` applied to the actual conjugacy transport of a degree-two class
   equals the relative invariant of `L/F` applied to that class. The
   compatibility certificate `h` is an arbitrary proof. One can always supply
   `compatibleFieldEquivalences_refl_algEquiv e`, and by proof irrelevance the
   transport does not depend on the choice. The proof installs
   `algEquivAlgebra e` as the `L`-algebra on `M`, together with
   declarations 4 and 5. It rewrites with declaration 7 (with `he` given by
   declaration 2) and applies `hI F L M x`. The only property of `I` used is
   `InflationCompatibility`. `RelativeConjugacy` and the other
   class-formation laws are not used.

The algebra structure `algEquivAlgebra e` is installed only inside these
statements and proofs, through `letI` or `let`, and is not a global instance.
A consumer's own `Algebra L M` instance is therefore unaffected. A consumer
with a different structure whose algebra map is `e` can use the general
declarations 6 and 7.

## Provenance

The content is derived. It is a formal rendering, in the intrinsic setting of
two abstract fields, of the following facts in Jean-Pierre Serre, *Local
Fields*, 1979, `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`:

- Chapter XI, §1(iv), printed page 166 (PDF page 172). For `s ∈ G`, the
  isomorphism `s* : Hⁿ(F/E) → Hⁿ(sF/sE)` is defined by transport of structure,
  using `t ↦ s⁻¹ t s` on groups and `a ↦ s·a` on coefficients. When `s` fixes
  `E`, `s*` is the identity map of `Hⁿ(F/E)`, by Chapter VII, §5,
  Proposition 3.
- Chapter XI, §2, printed page 167 (PDF page 173). The invariant
  `inv_E` is defined on the direct limit `H²( /E)`, taken along inflation
  maps, so it is compatible with inflation.
- Chapter XI, §2, Proposition 1(iii), printed pages 167-168 (PDF pages
  173-174). `inv_{sE} ∘ s* = inv_E`. The proof starts from the base-field
  case, where `s*` is the identity.

In Serre's notation, take the base `E = F` and `s ∈ G_F` with `sL = M`. Then
`s*` is the map `H²(L/F) → H²(M/F)` and Proposition 1(iii) gives
`inv_F ∘ s* = inv_F`. Serre works inside a common algebraic closure. There,
`s*` on `H²(L/F)` with `sL = L` is the identity because inner automorphisms
act trivially on cohomology. Here `L` and `M` are distinct abstract fields
related only by `e`, so the transport cannot literally be the identity. Its
intrinsic replacement is declaration 8: once `M` is an `L`-algebra through
`e` (declaration 1), the extension `M/L` has degree one and the transport is
exactly the inflation map `H²(L/F) → H²(M/F)`. The invariant statement then follows from
the inflation compatibility of the invariants, Serre's direct-limit
definition of `inv_F`, which the Library records as
`InvariantFamily.InflationCompatibility`.

The route in Lean differs from Serre's: it does not use Chapter VII, §5,
Proposition 3, and it does not need fields inside a common closure. It
identifies the two actual `groupCohomology.map` data directly, as described
under declaration 7. It does not prove the general change-of-base conjugacy
law `RelativeConjugacy`, nor triviality of inner conjugation on `H²`.

## Mathlib and Library correspondence

Pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`:
`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`,
`Module.Finite.of_surjective`, `Algebra.linearMap`,
`AlgEquiv.restrictNormalHom`, `AlgEquiv.restrictNormal_commutes`,
`groupCohomology.map`, `groupCohomology.mapIso`, and
`groupCohomology.map_congr`.

Published Library interface:
`CompatibleFieldEquivalences`, `galoisConjugacy`, `unitsConjugacy` and
`relativeConjugacy` (`Langlands.ClassFieldTheory.Local.Conjugacy`, Worker
49). `relativeCohomology`, `inflationCoefficients` and `relativeInflation`
(`Langlands.ClassFieldTheory.Local.Cohomology`, Worker 42).
`InvariantFamily` (`Langlands.ClassFieldTheory.Local.Invariants`) and
`InvariantFamily.InflationCompatibility`
(`Langlands.ClassFieldTheory.Local.ClassFormation`).
