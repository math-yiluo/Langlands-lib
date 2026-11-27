import Langlands.FieldTheory.CountableGaloisFamily
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Finiteness.Small

/-! # Separable generators over a dense subfield -/

noncomputable section

open Polynomial IntermediateField

namespace Langlands.FieldTheory

universe u

variable {K : Type*} {F : Type u} [Field K]

private theorem exists_separable_generator_of_denseRange_nontrivial
    [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [Algebra K F]
    (h : DenseRange (algebraMap K F))
    (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ y : E, F⟮y⟯ = ⊤ ∧ IsSeparable K y := by
  let := Module.Finite.small.{u} F E
  let e : Shrink.{u} E ≃ₐ[F] E := Shrink.algEquiv F E
  have : FiniteDimensional F (Shrink.{u} E) := e.symm.toLinearEquiv.finiteDimensional
  have : Algebra.IsSeparable F (Shrink.{u} E) := AlgEquiv.Algebra.isSeparable e.symm
  obtain ⟨n, a, y, hy, hroot⟩ := CountableGaloisFamily.exists_dense_generator h (Shrink.{u} E)
  have hgen : F⟮e y⟯ = ⊤ := by
    change F⟮e.toAlgHom y⟯ = ⊤
    rw [← Set.image_singleton, ← adjoin_map F _ e.toAlgHom, hy, ← AlgHom.fieldRange_eq_map]
    exact e.fieldRange_eq_top
  choose b hb using fun i => (a i).property
  let p : K[X] := X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ)
  have hp : p.Monic := monic_X_pow_add (degree_sum_fin_lt b)
  have hpmap : p.map (algebraMap K F) =
      X ^ n + ∑ i : Fin n, C (a i : F) * X ^ (i : ℕ) := by
    simp [p, Polynomial.map_sum, hb]
  have hproot : aeval (e y) p = 0 := by
    rw [← aeval_map_algebraMap F, hpmap, aeval_algHom_apply e, hroot, map_zero]
  have hyK : IsIntegral K (e y) := ⟨p, hp, hproot⟩
  let q := ringExpChar K
  have : ExpChar F q := expChar_of_injective_algebraMap (algebraMap K F).injective q
  obtain ⟨g, hg, m, hmin⟩ := (minpoly.irreducible hyK).hasSeparableContraction q
  have hgroot : aeval (e y ^ q ^ m) g = 0 := by
    simpa only [expand_aeval, minpoly.aeval] using congr(aeval (e y) $hmin)
  refine ⟨e y ^ q ^ m, ?_, hg.of_dvd (minpoly.dvd K _ hgroot)⟩
  rw [← adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E (e y) q m]
  exact hgen

variable [NormedField F] [IsUltrametricDist F] [CompleteSpace F] [Algebra K F]

/-- A finite separable extension of a complete nonarchimedean field has a primitive element
that is separable over the given dense subfield. -/
theorem exists_separable_generator_of_denseRange (h : DenseRange (algebraMap K F))
    (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ y : E, F⟮y⟯ = ⊤ ∧ IsSeparable K y := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hdiscrete | ⟨_, hnorm⟩
  · have := hdiscrete
    have hsurj := denseRange_discrete.mp h
    have : Algebra.IsSeparable K F := ⟨fun x => by
      obtain ⟨a, rfl⟩ := hsurj x
      exact isSeparable_algebraMap a⟩
    have := Algebra.IsSeparable.trans K F E
    obtain ⟨y, hy⟩ := Field.exists_primitive_element F E
    exact ⟨y, hy, Algebra.IsSeparable.isSeparable K y⟩
  · cases hnorm
    exact exists_separable_generator_of_denseRange_nontrivial h E

/-- The separable closure of a complete nonarchimedean field in an overfield is generated
by the elements of that overfield that are separable over the dense subfield. -/
theorem adjoin_separableClosure_of_denseRange (h : DenseRange (algebraMap K F))
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L] :
    adjoin F (separableClosure K L : Set L) = separableClosure F L := by
  apply le_antisymm
  · exact adjoin_le_iff.mpr fun x hx => mem_separableClosure_iff.mpr
      ((mem_separableClosure_iff.mp hx).tower_top F)
  · intro x hx
    have hxsep : IsSeparable F x := mem_separableClosure_iff.mp hx
    let E := F⟮x⟯
    have : FiniteDimensional F E := adjoin.finiteDimensional hxsep.isIntegral
    have : Algebra.IsSeparable F E :=
      (isSeparable_adjoin_simple_iff_isSeparable F L).mpr hxsep
    obtain ⟨y, hgen, hy⟩ := exists_separable_generator_of_denseRange h E
    have hy' : (y : L) ∈ separableClosure K L := mem_separableClosure_iff.mpr
      (hy.map (E.val.restrictScalars K) Subtype.val_injective)
    have hgen' : F⟮(y : L)⟯ = E := by
      change F⟮E.val y⟯ = E
      rw [← Set.image_singleton, ← adjoin_map F _ E.val, hgen, ← AlgHom.fieldRange_eq_map]
      exact E.fieldRange_val
    apply (adjoin_simple_le_iff.mpr (subset_adjoin F _ hy'))
    rw [hgen']
    exact mem_adjoin_simple_self F x

end Langlands.FieldTheory
