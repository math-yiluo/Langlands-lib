import Langlands.ClassFieldTheory.Local.Conjugacy
import Langlands.ClassFieldTheory.Local.ClassFormation

/-!
# Same-base conjugacy as inflation along a degree-one tower

An algebra equivalence `e : L ≃ₐ[K] M` makes `M` an `L`-algebra through `e`
(`algEquivAlgebra e`, not an instance). For that algebra, the actual conjugacy
transport of relative cohomology along the identity of `K` and `e` is the
actual inflation map. Consequently every
invariant family satisfying `InflationCompatibility` is natural under
algebra equivalences over the same p-adic base.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

section SameBase

variable {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- The `L`-algebra structure on `M` induced by an algebra equivalence
`e : L ≃ₐ[K] M`: its algebra map is `e`. It is not an instance. -/
@[instance_reducible]
def algEquivAlgebra (e : L ≃ₐ[K] M) : Algebra L M :=
  e.toRingHom.toAlgebra

/-- The algebra map of `algEquivAlgebra e` is `e`. -/
theorem algebraMap_algEquivAlgebra (e : L ≃ₐ[K] M) (x : L) :
    letI : Algebra L M := algEquivAlgebra e
    algebraMap L M x = e x :=
  rfl

/-- An algebra equivalence over `K` forms a commuting square over the identity of `K`. -/
theorem compatibleFieldEquivalences_refl_algEquiv (e : L ≃ₐ[K] M) :
    CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv :=
  fun x => e.commutes x

/-- With the `L`-algebra structure on `M` induced by `e`, the scalar tower
`K → L → M` commutes. -/
theorem isScalarTower_algEquiv (e : L ≃ₐ[K] M) :
    letI : Algebra L M := algEquivAlgebra e
    IsScalarTower K L M :=
  letI : Algebra L M := algEquivAlgebra e
  IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm

/-- With the `L`-algebra structure on `M` induced by `e`, `M` is
one-dimensional, in particular finite-dimensional, over `L`. -/
theorem finiteDimensional_algEquiv (e : L ≃ₐ[K] M) :
    letI : Algebra L M := algEquivAlgebra e
    FiniteDimensional L M :=
  letI : Algebra L M := algEquivAlgebra e
  Module.Finite.of_surjective (Algebra.linearMap L M) e.surjective

/-- Normal restriction along an `L`-algebra structure given by `e` is conjugation
by `e`: it is the inverse of the actual Galois-group conjugacy. -/
theorem restrictNormalHom_eq_galoisConjugacy_symm (e : L ≃ₐ[K] M)
    [Algebra L M] [IsScalarTower K L M] [Normal K L]
    (he : ∀ x : L, algebraMap L M x = e x)
    (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) :
    (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)) =
      ((galoisConjugacy (RingEquiv.refl K) e.toRingEquiv h).symm :
        Gal(M/K) →* Gal(L/K)) := by
  ext τ x
  apply e.injective
  change e (τ.restrictNormal L x) = e (e.symm (τ (e x)))
  rw [← he, AlgEquiv.restrictNormal_commutes, he, e.apply_symm_apply]

/-- For any `L`-algebra structure on `M` given by `e`, the actual conjugacy
transport along the identity of `K` and `e` is the actual inflation map. -/
theorem relativeConjugacy_refl_hom_eq_relativeInflation (e : L ≃ₐ[K] M)
    [Algebra L M] [IsScalarTower K L M] [Normal K L]
    (he : ∀ x : L, algebraMap L M x = e x)
    (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) (n : ℕ) :
    (relativeConjugacy (RingEquiv.refl K) e.toRingEquiv h n).hom =
      relativeInflation K L M n := by
  unfold relativeConjugacy groupCohomology.mapIso
  apply groupCohomology.map_congr
  · exact (restrictNormalHom_eq_galoisConjugacy_symm e he h).symm
  · ext a
    apply congrArg Additive.ofMul
    apply Units.ext
    exact (he _).symm

/-- After installing the `L`-algebra structure on `M` induced by `e`, the actual
conjugacy transport along the identity of `K` and `e` is the actual inflation map. -/
theorem relativeConjugacy_refl_hom_eq_relativeInflation_algEquivAlgebra (e : L ≃ₐ[K] M)
    [Normal K L]
    (h : CompatibleFieldEquivalences (RingEquiv.refl K) e.toRingEquiv) (n : ℕ) :
    letI : Algebra L M := algEquivAlgebra e
    letI : IsScalarTower K L M := isScalarTower_algEquiv e
    (relativeConjugacy (RingEquiv.refl K) e.toRingEquiv h n).hom =
      relativeInflation K L M n :=
  letI : Algebra L M := algEquivAlgebra e
  letI : IsScalarTower K L M := isScalarTower_algEquiv e
  relativeConjugacy_refl_hom_eq_relativeInflation e (algebraMap_algEquivAlgebra e) h n

end SameBase

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- An inflation-compatible invariant family is unchanged by the actual
conjugacy transport along an algebra equivalence over the same p-adic base. -/
theorem relative_relativeConjugacy_refl_of_inflationCompatibility
    (I : InvariantFamily.{u,u} p) (hI : I.InflationCompatibility)
    (F : PadicField.{u} p) {L M : Type u} [Field L] [Field M]
    [Algebra F.Carrier L] [Algebra F.Carrier M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier L] [IsGalois F.Carrier M]
    (e : L ≃ₐ[F.Carrier] M)
    (h : CompatibleFieldEquivalences (RingEquiv.refl F.Carrier) e.toRingEquiv)
    (x : relativeCohomology F.Carrier L 2) :
    I.relative F M ((relativeConjugacy (RingEquiv.refl F.Carrier) e.toRingEquiv h 2).hom x) =
      I.relative F L x := by
  let _ : Algebra L M := algEquivAlgebra e
  have _ : IsScalarTower F.Carrier L M := isScalarTower_algEquiv e
  have _ : FiniteDimensional L M := finiteDimensional_algEquiv e
  rw [relativeConjugacy_refl_hom_eq_relativeInflation e (algebraMap_algEquivAlgebra e) h 2]
  exact hI F L M x

end InvariantFamily

end Langlands.ClassFieldTheory.Local
