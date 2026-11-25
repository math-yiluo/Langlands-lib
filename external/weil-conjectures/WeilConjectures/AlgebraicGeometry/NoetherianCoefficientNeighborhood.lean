/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.RingTheory.FibreDimensionNeighborhood
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Extension.Presentation.Basic
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension

/-! # Bounded principal neighbourhoods in a coefficient model

Source: Stacks Project, Algebra, proof of Tag 00SU, first two paragraphs.
(blueprint: lem-weil-pbc-noetherian-coefficient-model-principal-neighborhood).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- Each point upstairs lies in a principal open from the coefficient model on which all
nonempty model fibres have dimension at most the expected dimension.
Source: Stacks Project, Algebra, proof of Tag 00SU, first two paragraphs.
(blueprint: lem-weil-pbc-noetherian-coefficient-model-principal-neighborhood).

Proof:
1. Put S₀ = R₀[x]/(f₀) and S = R[x]/(f). Polynomial scalar extension and tensoring
   a quotient give R ⊗[R₀] S₀ ≃ S since the mapped equations are f.
   Contract q to q₀ in S₀, p in R and p₀ in R₀. The fibre-prime correspondence
   shows that both fibres at p and p₀ are nonzero. Tensor cancellation identifies
   the first fibre with scalar extension of the second along κ(p₀) → κ(p).
2. The hypothesis gives c ≤ n and dimension n-c for the first fibre. The field
   extension is faithfully flat, hence surjective on spectra. Dimension at a
   point is preserved by field extension. Taking the supremum of local dimensions
   therefore gives dimension n-c for the model fibre as well.
3. The local dimension at the fibre point corresponding to q₀ is a natural number
   d ≤ n-c: it is nonnegative since the point exists, and bounded by the finite
   global dimension. Apply the principal fibre-dimension neighbourhood theorem
   to the finite type algebra S₀ over R₀ at q₀ with this d. Obtain g ∉ q₀
   whose localized nonzero fibres all have dimension ≤ d ≤ n-c.
4. Lift g to a polynomial G over R₀ using quotient surjectivity. Its image in S
   avoids q by contraction, and its model localization is exactly (S₀)_g.
   If S is zero there is no q, so the statement has no nonvacuous case. -/
theorem exists_coefficient_model_principal_neighborhood
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (R₀ : Subring R)
    (f₀ : Fin c → MvPolynomial (Fin n) R₀)
    (hf₀ : ∀ i, MvPolynomial.map R₀.subtype (f₀ i) = f i)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ G : MvPolynomial (Fin n) R₀,
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.map R₀.subtype G)
        ∉ q.asIdeal ∧
      ∀ (p₀ : Ideal R₀) [p₀.IsPrime],
        Nontrivial (p₀.Fiber (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) G))) →
        topologicalKrullDim (PrimeSpectrum (p₀.Fiber (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) G)))) ≤
            ((n - c : ℕ) : WithBot ℕ∞) := by
  classical
  let : Algebra R₀ R := R₀.subtype.toAlgebra
  let S₀ := MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)
  let S := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  have : IsScalarTower R₀ R S := inferInstance
  let F : MvPolynomial (Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R :=
    MvPolynomial.mapAlgHom (Algebra.ofId R₀ R)
  have hI : Ideal.span (Set.range f₀) ≤ (Ideal.span (Set.range f)).comap F := by
    rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    change MvPolynomial.map R₀.subtype (f₀ i) ∈ Ideal.span (Set.range f)
    rw [hf₀]
    exact Ideal.subset_span (Set.mem_range_self i)
  let φ : S₀ →ₐ[R₀] S := Ideal.quotientMapₐ (Ideal.span (Set.range f)) F hI
  let q₀ := PrimeSpectrum.comap φ.toRingHom q
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let p₀ := p.asIdeal.comap R₀.subtype
  have : p₀.IsPrime := Ideal.comap_isPrime _ _
  have hq₀ : PrimeSpectrum.comap (algebraMap R₀ S₀) q₀ = ⟨p₀, inferInstance⟩ := by
    ext r
    change φ (algebraMap R₀ S₀ r) ∈ q.asIdeal ↔
      algebraMap R S (R₀.subtype r) ∈ q.asIdeal
    rw [φ.commutes]
    rfl
  let k := p₀.ResidueField
  let K := p.asIdeal.ResidueField
  let : Algebra k K := (Ideal.ResidueField.map p₀ p.asIdeal R₀.subtype rfl).toAlgebra
  let : Algebra R₀ K := ((algebraMap R K).comp R₀.subtype).toAlgebra
  have : IsScalarTower R₀ R K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₀ k K := IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact (Ideal.ResidueField.map_algebraMap p₀ p.asIdeal R₀.subtype rfl r).symm
  let P := (Presentation.naive (v := f₀)).baseChange R
  have hrel : P.relation = f := by
    funext i
    exact hf₀ i
  have e : S ≃ₐ[R] R ⊗[R₀] S₀ :=
    (Ideal.quotientEquivAlgOfEq R (hrel ▸ P.span_range_relation_eq_ker)).trans
      (P.quotientEquiv.restrictScalars R)
  have e₁ : p.asIdeal.Fiber S ≃ₐ[K] K ⊗[R] (R ⊗[R₀] S₀) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  have e₂ := Algebra.TensorProduct.cancelBaseChange R₀ R K K S₀
  have e₃ := Algebra.TensorProduct.cancelBaseChange R₀ k K K S₀
  have E : p.asIdeal.Fiber S ≃ₐ[K] K ⊗[k] (p₀.Fiber S₀) :=
    e₁.trans (e₂.trans e₃.symm)
  have hn : Nontrivial (p.asIdeal.Fiber S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr ⟨q, rfl⟩
  have hdim := (h p.asIdeal hn).2
  have : Algebra.FinitePresentation k (p₀.Fiber S₀) :=
    ((Presentation.naive (v := f₀)).baseChange k).finitePresentation_of_isFinite
  have hd₀ : topologicalKrullDim (PrimeSpectrum (p₀.Fiber S₀)) =
      ((n - c : ℕ) : WithBot ℕ∞) := by
    let H : PrimeSpectrum (p.asIdeal.Fiber S) ≃ₜ
        PrimeSpectrum (K ⊗[k] (p₀.Fiber S₀)) :=
      PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
    have he := IsHomeomorph.topologicalKrullDim_eq H H.isHomeomorph
    have hfield := AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension
      k K (p₀.Fiber S₀)
    exact hfield.symm.trans (he.symm.trans hdim)
  let Q := PrimeSpectrum.preimageEquivFiber R₀ S₀
    (PrimeSpectrum.comap (algebraMap R₀ S₀) q₀) ⟨q₀, rfl⟩
  have hle : topologicalKrullDimAt Q ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
    have hglobal : topologicalKrullDimAt Q ≤ topologicalKrullDim
        (PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R₀ S₀) q₀).asIdeal.Fiber S₀)) := by
      rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
      exact le_iSup _ Q
    apply hglobal.trans_eq
    rw [hq₀]
    exact hd₀
  have hnonneg : 0 ≤ topologicalKrullDimAt Q := by
    unfold topologicalKrullDimAt
    refine le_iInf₂ fun U hQU ↦ ?_
    have : Nonempty U := ⟨⟨Q, hQU⟩⟩
    have : Nonempty (TopologicalSpace.IrreducibleCloseds U) :=
      ⟨⟨closure {(⟨Q, hQU⟩ : U)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  obtain ⟨D, hD⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot (by simp) hnonneg)
  have hDn : D ≤ (n - c : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    exact hD ▸ hle
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by simp) hDn)
  have hlocal : topologicalKrullDimAt Q = (d : WithBot ℕ∞) := by
    rw [← hD, ← hd]
    rfl
  obtain ⟨g, hg, hgbound⟩ := exists_away_fibre_dimension_le q₀ d hlocal
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨G, ?_, ?_⟩
  · change φ (Ideal.Quotient.mk (Ideal.span (Set.range f₀)) G) ∉ q.asIdeal
    rw [hG]
    exact hg
  · intro p' hp' hn'
    rw [hG]
    have hu := hgbound ⟨p', hp'⟩ (by rw [hG] at hn'; exact hn')
    exact hu.trans (by
      apply WithBot.coe_le_coe.mpr
      change (d : ℕ∞) ≤ _
      rw [hd]
      exact hDn)

end Algebra
