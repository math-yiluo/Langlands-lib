import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationStatement

/-! # Normal subalgebras from finite normalization -/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- The normalization-image construction gives the required subalgebra inside the ambient ring. -/
theorem integerFiniteTypeNormalizationReduction :
    IntegerFiniteTypeNormalizationReductionStatement.{u} := by
  classical
  intro h R _ _ _ s
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ (s : Set R)
  have hA : A.FG := Subalgebra.fg_adjoin_finset s
  let : Algebra.FiniteType ℤ A := A.fg_iff_finiteType.mp hA
  let B := integralClosure A (FractionRing A)
  let : Module.Finite A B := h A
  let : IsIntegrallyClosed B :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn B (FractionRing A)
  let : Algebra.FiniteType ℤ B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A)
      (inferInstance : Algebra.FiniteType A B)
  let g : FractionRing A →ₐ[A] FractionRing R :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId A (FractionRing R))
      ((IsFractionRing.injective R (FractionRing R)).comp Subtype.val_injective)
  let k : B →ₐ[A] FractionRing R := g.comp (integralClosure A (FractionRing A)).val
  have hk (x : B) : IsIntegral R (k x) :=
    ((integralClosure.isIntegral x).map k).tower_top
  let j : B →+* R :=
    { toFun := fun x => IsIntegralClosure.mk' R (k x) (hk x)
      map_one' := by
        apply IsFractionRing.injective R (FractionRing R)
        simp only [IsIntegralClosure.algebraMap_mk', map_one]
      map_zero' := by
        apply IsFractionRing.injective R (FractionRing R)
        simp only [IsIntegralClosure.algebraMap_mk', map_zero]
      map_add' := by
        intro x y
        apply IsFractionRing.injective R (FractionRing R)
        simp only [map_add, IsIntegralClosure.algebraMap_mk']
      map_mul' := by
        intro x y
        apply IsFractionRing.injective R (FractionRing R)
        simp only [map_mul, IsIntegralClosure.algebraMap_mk'] }
  have hj (x : B) : algebraMap R (FractionRing R) (j x) = k x :=
    IsIntegralClosure.algebraMap_mk' R (k x) (hk x)
  have hji : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply g.toRingHom.injective
    exact (hj x).symm.trans ((congrArg (algebraMap R (FractionRing R)) hxy).trans (hj y))
  let f : B →ₐ[ℤ] R :=
    { j with commutes' := fun n => by simp [algebraMap_int_eq] }
  have hT : f.range.FG := by
    simpa only [Algebra.map_top] using
      (Algebra.FiniteType.out (R := ℤ) (A := B)).map f
  refine ⟨f.range, hT, ?_, ?_, isNoetherianRing_of_fg hT⟩
  · intro x hx
    refine ⟨algebraMap A B ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    apply IsFractionRing.injective R (FractionRing R)
    change algebraMap R (FractionRing R) (j _) = algebraMap R (FractionRing R) x
    rw [hj, k.commutes]
    rfl
  · exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective f hji).toRingEquiv

end Langlands.AlgebraicGeometry.NoetherianApproximation
