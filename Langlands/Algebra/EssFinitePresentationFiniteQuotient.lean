import Langlands.Algebra.EssFinitePresentationFiniteQuotientStatement
import Langlands.Algebra.EssFinitePresentationTransportProof
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic

/-! # Essential finite presentation under finitely generated ideal quotients -/

universe u v w

namespace Langlands.Algebra

/-- A finitely generated ideal in a localization is the extension of a finitely
 generated ideal, obtained by taking numerators of a finite generating family. -/
private theorem exists_fg_ideal_map_eq
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (J : Ideal S) (hJ : J.FG) :
    ∃ K : Ideal A, K.FG ∧ K.map (algebraMap A S) = J := by
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  choose a d hd using fun i : Fin n => IsLocalization.exists_mk'_eq M (s i)
  let K : Ideal A := Ideal.span (Set.range a)
  refine ⟨K, Submodule.fg_span (Set.finite_range a), le_antisymm ?_ ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change algebraMap A S (a i) ∈ J
    apply (IsLocalization.mk'_mem_iff (M := M) (y := d i)).mp
    rw [hd i]
    rw [← hs]
    exact Ideal.subset_span (Set.mem_range_self i)
  · rw [← hs]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hd i]
    apply (IsLocalization.mk'_mem_iff (M := M) (y := d i)).mpr
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

/-- Quotient closure for the target of an arbitrary localization presentation. -/
private theorem finite_quotient_of_localization
    {R : Type u} {A : Type v} {S : Type w} {B : Type*}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra A S] [Algebra R B]
    [IsScalarTower R A S] [_root_.Algebra.FinitePresentation R A]
    (M : Submonoid A) [IsLocalization M S] (e : S ≃ₐ[R] B)
    (J : Ideal B) (hJ : J.FG) : EssFinitePresentation R (B ⧸ J) := by
  let J' : Ideal S := J.map e.symm.toRingHom
  obtain ⟨K, hK, hKmap⟩ := exists_fg_ideal_map_eq M J' (hJ.map e.symm.toRingHom)
  have eJ : (S ⧸ K.map (algebraMap A S)) ≃ₐ[R] (B ⧸ J) :=
    Ideal.quotientEquivAlg _ _ e (by
      rw [hKmap]
      dsimp only [J']
      rw [Ideal.map_map]
      have he : (e : S →+* B).comp e.symm.toRingHom = RingHom.id B := by
        ext b
        exact e.apply_symm_apply b
      rw [he, Ideal.map_id])
  have : _root_.Algebra.FinitePresentation R (A ⧸ K) :=
    _root_.Algebra.FinitePresentation.quotient hK
  have : IsScalarTower R (A ⧸ K) (S ⧸ K.map (algebraMap A S)) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change Ideal.Quotient.mk (K.map (algebraMap A S)) (algebraMap R S r) =
        Ideal.Quotient.mk (K.map (algebraMap A S))
          (algebraMap A S (algebraMap R A r))
      rw [IsScalarTower.algebraMap_apply R A S]
  exact essFinitePresentation_of_algEquiv (R := R) eJ
    (essFinitePresentation_of_isLocalization R (A ⧸ K)
      (S ⧸ K.map (algebraMap A S)) (Algebra.algebraMapSubmonoid (A ⧸ K) M))

/-- Quotients by finitely generated ideals preserve essential finite presentation. -/
theorem essFinitePresentationFiniteQuotient :
    EssFinitePresentationFiniteQuotientStatement.{u, v} := by
  intro R B _ _ _ J hB hJ
  obtain ⟨n, I, hI, M, ⟨e⟩⟩ := hB
  let A := MvPolynomial (Fin n) R ⧸ I
  have : _root_.Algebra.FinitePresentation R A :=
    _root_.Algebra.FinitePresentation.quotient hI
  exact finite_quotient_of_localization (R := R) (A := A) (S := Localization M) M e J hJ

example : EssFinitePresentationFiniteQuotientStatement.{u, v} :=
  @essFinitePresentationFiniteQuotient.{u, v}

end Langlands.Algebra
