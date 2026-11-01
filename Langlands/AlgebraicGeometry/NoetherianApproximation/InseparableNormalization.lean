import Langlands.AlgebraicGeometry.NoetherianApproximation.FrobeniusFinite
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Finiteness

universe u v w

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Finiteness descends through an injective last factor over a noetherian base. -/
theorem finite_of_finite_comp_of_injective
    {R : Type u} {B : Type v} {C : Type w}
    [CommRing R] [IsNoetherianRing R] [CommRing B] [CommRing C]
    (f : R →+* B) (g : B →+* C) (h : (g.comp f).Finite)
    (hg : Function.Injective g) : f.Finite := by
  algebraize [f, g, g.comp f]
  exact Module.Finite.of_injective ((Algebra.linearMap B C).restrictScalars R) hg

/-- A finite extension of the fraction field of a normal finite type integer
domain has finite integral closure, including in positive characteristic. -/
theorem finite_integralClosure_of_normal_integer_finiteType
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Algebra.FiniteType ℤ R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] :
    Module.Finite R (integralClosure R L) := by
  let S := separableClosure K L
  let p := ringExpChar K
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ExpChar R p := (algebraMap R K).expChar (IsFractionRing.injective R K) p
  let n := IsPurelyInseparable.exponent S L
  let F : L →+* S := IsPurelyInseparable.iterateFrobenius S L p (le_refl n)
  have hF (x : L) : algebraMap S L (F x) = x ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius S p (le_refl n) x
  let G : integralClosure R L →+* integralClosure R S :=
    (F.comp (integralClosure R L).val.toRingHom).codRestrict
      (integralClosure R S).toSubring fun x ↦ by
        apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S L)
          (algebraMap S L).injective).mp
        change IsIntegral R (algebraMap S L (F x.val))
        rw [hF]
        exact x.property.pow _
  have hG : Function.Injective G := by
    intro x y h
    apply Subtype.ext
    exact F.injective (congrArg Subtype.val h)
  have hcomp : G.comp (algebraMap R (integralClosure R L)) =
      (algebraMap R (integralClosure R S)).comp (iterateFrobenius R p n) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply (algebraMap S L).injective
    change algebraMap S L (F (algebraMap R L r)) =
      algebraMap S L (algebraMap R S (iterateFrobenius R p n r))
    rw [hF, ← IsScalarTower.algebraMap_apply R S L,
      iterateFrobenius_def, map_pow]
  have hsep : Module.Finite R (integralClosure R S) :=
    IsIntegralClosure.finite R K S (integralClosure R S)
  apply RingHom.finite_algebraMap.mp
  apply finite_of_finite_comp_of_injective _ G _ hG
  rw [hcomp]
  exact (RingHom.finite_algebraMap.mpr hsep).comp (finite_iterateFrobenius R p n)

end Langlands.AlgebraicGeometry.NoetherianApproximation
