/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.NoetherianPrincipalCoverModel
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-! # Descending a bounded principal-open cover to a finite coefficient ring

Source: Stacks Project, Algebra, proof of Tag 00SU, final paragraph.
(blueprint: lem-weil-pbc-noetherian-bounded-principal-cover-descent).
-/

@[expose] public section

universe u v

namespace Algebra

open scoped _root_.TensorProduct in
private theorem dimension_le_of_fibre_principal_cover
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} (g : ι → B)
    (hcover : ∀ q : PrimeSpectrum B, ∃ j, g j ∉ q.asIdeal)
    (p : Ideal A) [p.IsPrime] (d : ℕ)
    (hbound : ∀ j, Nontrivial (p.Fiber (Localization.Away (g j))) →
      topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away (g j)))) ≤
        (d : WithBot ℕ∞))
    (hn : Nontrivial (p.Fiber B)) :
    Nonempty ι ∧ topologicalKrullDim (PrimeSpectrum (p.Fiber B)) ≤ (d : WithBot ℕ∞) := by
  let := hn
  let t : ι → p.Fiber B := fun j ↦ (1 : p.ResidueField) ⊗ₜ[A] g j
  have hc : ∀ q : PrimeSpectrum (p.Fiber B), ∃ j, t j ∉ q.asIdeal := by
    intro q
    exact hcover (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q)
  have hu : ⨆ j, PrimeSpectrum.basicOpen (t j) = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨j, hj⟩ := hc q
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  have hi : Nonempty ι := by
    obtain ⟨q⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr hn
    obtain ⟨j, _⟩ := hc q
    exact ⟨j⟩
  refine ⟨hi, topologicalKrullDim_le_of_iSup_eq_top _ hu _ ?_⟩
  intro j
  let L := Localization.Away (t j)
  let H := PrimeSpectrum.localization_away_isOpenEmbedding L (t j)
  have he : topologicalKrullDim (PrimeSpectrum L) =
      topologicalKrullDim (PrimeSpectrum.basicOpen (t j)) := by
    rw [H.isEmbedding.topologicalKrullDim_eq_range,
      PrimeSpectrum.localization_away_comap_range L (t j)]
    rfl
  rw [← he]
  by_cases hL : Nontrivial L
  · let E := IsLocalization.Away.tensorProductEquivTMulRight A p.ResidueField
      (g j) (Localization.Away (g j))
    have hn' : Nontrivial (p.Fiber (Localization.Away (g j))) :=
      E.toRingEquiv.nontrivial_congr.mpr hL
    let e := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
    exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans_le
      (hbound j hn')
  · let : Subsingleton L := not_nontrivial_iff_subsingleton.mp hL
    let : IsEmpty (PrimeSpectrum L) := inferInstance
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum L)) :=
      ⟨fun Z ↦ by obtain ⟨q, _⟩ := Z.isIrreducible.nonempty; exact isEmptyElim q⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le

open scoped _root_.TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem localized_model_fibre_dimension
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (n c : ℕ) (f₀ : Fin c → MvPolynomial (Fin n) A)
    (G : MvPolynomial (Fin n) A) (p : Ideal B) [p.IsPrime]
    (hn : Nontrivial (p.Fiber (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range
        (fun i ↦ MvPolynomial.map (algebraMap A B) (f₀ i))))
          (MvPolynomial.map (algebraMap A B) G))))) :
    Nontrivial ((p.comap (algebraMap A B)).Fiber
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) G))) ∧
    topologicalKrullDim (PrimeSpectrum (p.Fiber (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range
        (fun i ↦ MvPolynomial.map (algebraMap A B) (f₀ i))))
          (MvPolynomial.map (algebraMap A B) G))))) =
    topologicalKrullDim (PrimeSpectrum ((p.comap (algebraMap A B)).Fiber
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) G)))) := by
  let f₁ := fun i ↦ MvPolynomial.map (algebraMap A B) (f₀ i)
  let S₀ := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f₀)
  let S₁ := MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range f₁)
  let g₀ : S₀ := Ideal.Quotient.mk _ G
  let g₁ : S₁ := Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A B) G)
  let P := (Presentation.naive (v := f₀)).baseChange B
  have hrel : P.relation = f₁ := rfl
  let E : S₁ ≃ₐ[B] B ⊗[A] S₀ :=
    (Ideal.quotientEquivAlgOfEq B (hrel ▸ P.span_range_relation_eq_ker)).trans
      (P.quotientEquiv.restrictScalars B)
  have hg : E g₁ = (1 : B) ⊗ₜ[A] g₀ := by
    dsimp only [E, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
    rw [Ideal.quotientEquivAlgOfEq_mk]
    change P.quotientEquiv _ = _
    rw [Presentation.quotientEquiv_mk, Generators.algebraMap_apply]
    rw [MvPolynomial.aeval_map_algebraMap]
    change (MvPolynomial.aeval fun i ↦ (1 : B) ⊗ₜ[A]
      (Ideal.Quotient.mk (Ideal.span (Set.range f₀))) (MvPolynomial.X i)) G = _
    rw [MvPolynomial.aeval_one_tmul]
    congr 1
    exact AlgHom.congr_fun (MvPolynomial.aeval_unique
      (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f₀)))).symm G
  let L₀ := Localization.Away g₀
  let L₁ := Localization.Away g₁
  let eL : L₁ ≃ₐ[B] Localization.Away ((1 : B) ⊗ₜ[A] g₀) :=
    IsLocalization.algEquivOfAlgEquiv _ _ E (by
      rw [Submonoid.map_powers, hg])
  let eT : B ⊗[A] L₀ ≃ₐ[B] Localization.Away ((1 : B) ⊗ₜ[A] g₀) :=
    IsLocalization.Away.tensorProductEquivTMulRight A B g₀ L₀
  let e : L₁ ≃ₐ[B] B ⊗[A] L₀ := eL.trans eT.symm
  let p₀ := p.comap (algebraMap A B)
  let k := p₀.ResidueField
  let K := p.ResidueField
  let : Algebra k K := (Ideal.ResidueField.map p₀ p (algebraMap A B) rfl).toAlgebra
  let : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq fun a ↦ by
    exact (Ideal.ResidueField.map_algebraMap p₀ p (algebraMap A B) rfl a).symm
  let e₁ : p.Fiber L₁ ≃ₐ[K] K ⊗[B] (B ⊗[A] L₀) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  let e₂ := Algebra.TensorProduct.cancelBaseChange A B K K L₀
  let e₃ := Algebra.TensorProduct.cancelBaseChange A k K K L₀
  let eF : p.Fiber L₁ ≃ₐ[K] K ⊗[k] (p₀.Fiber L₀) := e₁.trans (e₂.trans e₃.symm)
  have : Algebra.FiniteType A S₀ := inferInstance
  have : Algebra.FiniteType A L₀ := inferInstance
  have : Algebra.FiniteType k (p₀.Fiber L₀) := inferInstance
  let H := PrimeSpectrum.homeomorphOfRingEquiv eF.toRingEquiv
  have : Nontrivial (K ⊗[k] (p₀.Fiber L₀)) := eF.toRingEquiv.nontrivial_congr.mp hn
  refine ⟨(Algebra.TensorProduct.includeRight (R := k) (A := K)
    (B := p₀.Fiber L₀)).toRingHom.domain_nontrivial, ?_⟩
  exact (IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph).trans
    (AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension
      k K (p₀.Fiber L₀))

set_option backward.isDefEq.respectTransparency false in
/-- A cover by principal opens with bounded model fibres descends, together with its bound,
to a finite type coefficient ring. A nonzero descended fibre also ensures the indexing
type of the original covering family is inhabited; this handles an empty spectrum.
Source: Stacks Project, Algebra, proof of Tag 00SU, final paragraph.
(blueprint: lem-weil-pbc-noetherian-bounded-principal-cover-descent).

Proof:
1. Put S₀ = R₀[x]/(f₀) and S = R[x]/(f). The displayed principal opens cover
   Spec S. Quasi-compactness selects finitely many indices j. The unit-ideal
   criterion gives 1 = ∑ h̄ⱼ ḡⱼ in S. Lift h̄ⱼ to polynomials hⱼ over R.
   The difference 1 - ∑ hⱼ map(Gⱼ) is in the ideal generated by the finite family f,
   hence equals ∑ aᵢ fᵢ for polynomials aᵢ over R. For S = 0 the empty subcover
   is permitted, and the identity instead reads 1 = ∑ aᵢ fᵢ.
2. Since R₀ is finite type over ℤ, choose a finite ring-generating set for it.
   Adjoin its images and the coefficients of f, the selected Gⱼ, hⱼ and aᵢ inside R.
   This explicitly constructs a finite type subring R₁ containing R₀. Regard all
   displayed polynomials as polynomials over R₁; injectivity into R makes the same
   identity hold there. Let f₁ be the original equations with these coefficients.
   The Gⱼ consequently generate the unit ideal in S₁ = R₁[x]/(f₁).
3. For a prime p₁ of R₁, contract to p₀ in R₀. Polynomial and quotient scalar
   extension and localization base change identify the localized p₁-fibre with
   scalar extension of the localized p₀-fibre along κ(p₀) → κ(p₁). At every point
   the local dimension is unchanged under field extension and is at most d by
   the assumed bound on the old fibre. Taking suprema gives the bound d for the
   new localized fibre. A new nonzero fibre maps to an old nonzero fibre.
4. The Gⱼ cover Spec S₁ by the identity. Every point of any fibre therefore lies
   on one of these principal opens. Local dimension agrees on an open subspace,
   so all these point dimensions are at most d. The supremum formula proves the
   global bound. A nonzero fibre has a prime and therefore a point in some Gⱼ;
   its index inhabits ι. If ι is empty, the identity makes S₁ zero, and the
   conclusion concerning nonzero fibres is vacuous. -/
theorem exists_finiteType_model_of_bounded_principal_cover
    (R : Type u) [CommRing R] (n c d : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (R₀ : Subring R) (hR₀ : Algebra.FiniteType ℤ R₀)
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (hf₀ : ∀ i, MvPolynomial.map R₀.subtype (f₀ i) = f i)
    (ι : Type v) (G : ι → MvPolynomial (Fin n) R₀)
    (hcover : ∀ q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)),
      ∃ j, Ideal.Quotient.mk (Ideal.span (Set.range f))
        (MvPolynomial.map R₀.subtype (G j)) ∉ q.asIdeal)
    (hbound : ∀ (j : ι) (p₀ : Ideal R₀) [p₀.IsPrime],
      Nontrivial (p₀.Fiber (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) (G j)))) →
      topologicalKrullDim (PrimeSpectrum (p₀.Fiber (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) (G j))))) ≤ (d : WithBot ℕ∞)) :
    ∃ (R₁ : Subring R), Algebra.FiniteType ℤ R₁ ∧
      ∃ (f₁ : Fin c → MvPolynomial (Fin n) R₁),
        (∀ i, MvPolynomial.map R₁.subtype (f₁ i) = f i) ∧
        ∀ (p₁ : Ideal R₁) [p₁.IsPrime],
          Nontrivial (p₁.Fiber (MvPolynomial (Fin n) R₁ ⧸ Ideal.span (Set.range f₁))) →
          Nonempty ι ∧ topologicalKrullDim
            (PrimeSpectrum (p₁.Fiber (MvPolynomial (Fin n) R₁ ⧸ Ideal.span (Set.range f₁))))
              ≤ (d : WithBot ℕ∞) := by
  classical
  obtain ⟨R₁, h₀₁, hR₁, hcover₁⟩ := exists_finiteType_principal_cover_model
    R n c f R₀ hR₀ f₀ hf₀ ι G hcover
  let : Algebra R₀ R₁ := (Subring.inclusion h₀₁).toAlgebra
  let f₁ := fun i ↦ MvPolynomial.map (Subring.inclusion h₀₁) (f₀ i)
  refine ⟨R₁, hR₁, f₁, ?_, ?_⟩
  · intro i
    dsimp only [f₁]
    rw [MvPolynomial.map_map]
    exact hf₀ i
  · intro p₁ hp₁ hn
    apply dimension_le_of_fibre_principal_cover
      (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f₁))
        (MvPolynomial.map (Subring.inclusion h₀₁) (G j))) hcover₁ p₁ d _ hn
    intro j hn'
    have hb := localized_model_fibre_dimension (A := R₀) (B := R₁)
      n c f₀ (G j) p₁ hn'
    exact hb.2.trans_le (hbound j (p₁.comap (algebraMap R₀ R₁)) hb.1)

end Algebra
