import Langlands.Global.Arithmetic.HarrisProposition48SingletonDescentStatement
import Langlands.Global.Arithmetic.HarrisProposition48MackeyGaloisProof
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily

/-! # Galois stability of the singleton Mackey constituent -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.Unramified AdelicFunctoriality

private theorem exists_lift_fixing_conjugateEmbedding (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) [Normal Q.E Q.L]
    (hIndex : Nat.card (Q.MackeyIndex D) = 1) (σ : D ≃ₐ[Q.E] D) :
    ∃ τ : Q.L ≃ₐ[Q.E] Q.L, (∀ x : D, (σ x : Q.L) = τ x) ∧
      Q.conjugateEmbedding τ = Q.conjugateEmbedding 1 := by
  let g := σ.liftNormal Q.L
  let H := D.fixingSubgroup
  let K := (Q.conjugateField 1).fixingSubgroup
  let : Subsingleton (Q.MackeyIndex D) := (Nat.card_eq_one_iff_unique.mp hIndex).1
  have hcoset : DoubleCoset.mk H K 1 = DoubleCoset.mk H K g :=
    Subsingleton.elim (α := Q.MackeyIndex D) _ _
  obtain ⟨h, hh, τ, hτ, hfactor⟩ := DoubleCoset.eq.mp hcoset
  simp only [mul_one] at hfactor
  have hD := (IntermediateField.mem_fixingSubgroup_iff D h).mp hh
  have hK := (IntermediateField.mem_fixingSubgroup_iff (Q.conjugateField 1) τ).mp hτ
  refine ⟨τ, fun x => ?_, ?_⟩
  · apply h.injective
    calc
      h (σ x : Q.L) = (σ x : Q.L) := hD _ (σ x).property
      _ = g x := (σ.liftNormal_commutes Q.L x).symm
      _ = h (τ x) := congrArg (fun a : Q.L ≃ₐ[Q.E] Q.L => a x) hfactor
  · apply AlgHom.ext
    intro x
    exact hK (Q.conjugateEmbedding 1 x) ⟨x, rfl⟩

private theorem isMackeyConstituent_congr_embedding (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) [CompactSpace (AdeleQuotient D)]
    {a b : Q.L ≃ₐ[Q.E] Q.L} (h : Q.conjugateEmbedding a = Q.conjugateEmbedding b)
    {r : ℕ} (c : CuspidalOperatorRealization.IsoClass D r) :
    Q.IsMackeyConstituent.{uF, uV} D a c ↔ Q.IsMackeyConstituent.{uF, uV} D b c := by
  -- Vary the embedding together with its image, compositum and inclusion algebras.
  let P (j : Q.E' →ₐ[Q.E] Q.L) : Prop :=
    let A := j.fieldRange
    let M := D ⊔ A
    letI : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
    letI : Algebra A M := (IntermediateField.inclusion (show A ≤ M from le_sup_right)).toAlgebra
    c.IsWeakAutomorphicInductionOf.{0, 0, uV}
      (HeckeCharacter.normComp (L := M) (HeckeCharacter.comap j.equivFieldRange.symm.toRingEquiv Q.ξ))
  change P (Q.conjugateEmbedding a) ↔ P (Q.conjugateEmbedding b)
  rw [h]

/-- The identity-coset Mackey constituent is stable under every step-field automorphism
when the Mackey double-coset space is a singleton. -/
theorem proposition48SingletonMackeyGaloisStableTC :
    Proposition48SingletonMackeyGaloisStableTCStatement.{uF, uV} := by
  classical
  intro hRig hInv Q D hNormal hIndex
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  intro r S hS σ
  let : IsNormalClosure Q.E Q.E' Q.L := hNormal
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  obtain ⟨τ, hστ, hτ⟩ := exists_lift_fixing_conjugateEmbedding Q D hIndex σ
  have hConj : Q.IsMackeyConstituent.{uF, uV} D 1 (S.isoClass.galoisConj σ) := by
    apply (isMackeyConstituent_congr_embedding Q D hτ _).mp
    simpa only [mul_one] using
      proposition48MackeyConstituentGaloisConjugate.{uF, uV} Q D 1 τ σ hστ r S.isoClass hS
  let M := Q.mackeyField D 1
  let : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  obtain ⟨s, hs, hsInd⟩ := hS
  obtain ⟨t, ht, htInd⟩ := hConj
  -- Both weak inductions give the same polynomial for a common family of uniformizers.
  have hEuler : s.SameEulerPolynomials t := by
    filter_upwards [hsInd.2, htInd.2] with v hsv htv
    intro hsGood htGood
    choose ϖ hϖ using fun w : FinitePlacesAbove M v => WeakInduction.exists_uniformizer w.1
    exact ((hsv hsGood).2 ϖ hϖ).trans ((htv htGood).2 ϖ hϖ).symm
  let c := PositiveRankCuspidalClass.ofFixedRank S.isoClass
  let A := IsobaricData.ofCuspidal c
  have hsA : A.HasSpectralSystem.{0, uV} s :=
    IsobaricData.hasSpectralSystem_ofCuspidal_of (c := c) hs
      (SpectralSystem.sameEulerPolynomials_refl s)
  have htA : (A.galoisConj σ).HasSpectralSystem.{0, uV} t :=
    IsobaricData.hasSpectralSystem_ofCuspidal_of (c := c.galoisConj σ) ht
      (SpectralSystem.sameEulerPolynomials_refl t)
  let : IsTotallyComplex D := isTotallyComplex_of_algebra Q.E D
  have hStable : (IsobaricData.ofCuspidal c).galoisConj σ = IsobaricData.ofCuspidal c :=
    hInv hRig Q.E D σ A s t hsA htA hEuler
  rw [IsobaricData.galoisConj_ofCuspidal] at hStable
  exact (PositiveRankCuspidalClass.isGaloisStable_iff_galoisConj_ofFixedRank σ S.isoClass).2
    (Multiset.singleton_inj.mp hStable)

end Langlands.Global.Harris
