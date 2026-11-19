import Langlands.AlgebraicGeometry.FiniteEtale.AffineSplitFieldTransfer
import Langlands.AlgebraicGeometry.PointManifold.Analytic.ComplexEtaleSections
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Geometric splitting of finite étale affine-space algebras -/

noncomputable section

universe u

open Function MvPolynomial
open scoped Cardinal TensorProduct

namespace Langlands.Algebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem exists_ringHom_complex_of_countable (F : Type*) [Field F] [CharZero F]
    [Countable F] : Nonempty (F →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hC : ℵ₀ < #ℂ := Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum
  have hCt : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
      Cardinal.mk_le_aleph0 hC
  let : Infinite t := Cardinal.aleph0_le_mk_iff.mp (hCt ▸ hC.le)
  obtain ⟨f, hf⟩ := exists_injective_nat s
  let j : s → t := Infinite.natEmbedding t ∘ f
  let y : s → ℂ := (Subtype.val : t → ℂ) ∘ j
  have hy : AlgebraicIndependent ℚ y := ht.1.comp j ((Infinite.natEmbedding t).injective.comp hf)
  let P := Algebra.adjoin ℚ (Set.range (Subtype.val : s → F))
  let g : P →ₐ[ℚ] ℂ := (aeval y).comp hs.1.aevalEquiv.symm.toAlgHom
  let : Algebra P ℂ := g.toRingHom.toAlgebra
  let : Module.IsTorsionFree P ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr
    ((algebraicIndependent_iff_injective_aeval.mp hy).comp hs.1.aevalEquiv.symm.injective)
  let : Algebra.IsAlgebraic P F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[P] ℂ).toRingHom⟩

private theorem exists_countable_coefficient_field {k : Type u} [Field k] [CharZero k]
    [IsAlgClosed k] (t : Finset k) :
    ∃ (F : Type u) (_ : Field F) (_ : IsAlgClosed F) (_ : Countable F) (_ : Algebra F k),
      (t : Set k) ⊆ Set.range (algebraMap F k) := by
  let L := IntermediateField.adjoin ℚ (t : Set k)
  have hL : #L ≤ ℵ₀ := by
    have h : #(IntermediateField.adjoin ℚ (t : Set k)) ≤
        Cardinal.lift #ℚ ⊔ #(t : Set k) ⊔ ℵ₀ := by
      simpa only [Cardinal.lift_id'] using
        IntermediateField.lift_cardinalMk_adjoin_le ℚ (t : Set k)
    exact h.trans (sup_le (sup_le (by simp) (Cardinal.lt_aleph0_of_finite _).le) le_rfl)
  let F := AlgebraicClosure L
  let : Countable F := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max L F).trans (max_le hL le_rfl))
  let f : F →ₐ[L] k := IsAlgClosed.lift
  let : Algebra F k := f.toRingHom.toAlgebra
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, fun c hc => ?_⟩
  let d : L := ⟨c, IntermediateField.subset_adjoin _ _ hc⟩
  exact ⟨algebraMap L F d, f.commutes d⟩

set_option maxHeartbeats 600000 in
private theorem exists_countable_model {k A : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {n : ℕ} [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.Etale (MvPolynomial (Fin n) k) A] [Module.Finite (MvPolynomial (Fin n) k) A] :
    ∃ (F : Type u) (_ : Field F) (_ : IsAlgClosed F) (_ : Countable F) (_ : Algebra F k)
      (B : Type u) (_ : CommRing B) (_ : Algebra (MvPolynomial (Fin n) F) B)
      (_ : Algebra.Etale (MvPolynomial (Fin n) F) B)
      (_ : Module.Finite (MvPolynomial (Fin n) F) B),
      Nonempty (A ≃ₐ[MvPolynomial (Fin n) k]
        (MvPolynomial (Fin n) k ⊗[MvPolynomial (Fin n) F] B)) := by
  classical
  let R := MvPolynomial (Fin n) k
  obtain ⟨R₀, A₀, _, _, hR₀, _, ⟨e₀⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℚ R A
  obtain ⟨s, hs⟩ := hR₀
  let t := s.biUnion fun a => a.coeffs
  obtain ⟨F, _, _, _, _, hF⟩ := exists_countable_coefficient_field t
  let : CharZero F := RingHom.charZero (algebraMap F k)
  let S := MvPolynomial (Fin n) F
  let f : S →ₐ[ℚ] R :=
    ⟨MvPolynomial.map (algebraMap F k), fun q => by
      change MvPolynomial.map (algebraMap F k) (C (q : F)) = C (q : k)
      rw [map_C, map_ratCast]⟩
  have hf : Injective f := MvPolynomial.map_injective _ (RingHom.injective _)
  have hR₀' : R₀ ≤ f.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    change x ∈ Set.range (MvPolynomial.map (algebraMap F k))
    exact MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc =>
      hF (Finset.mem_biUnion.mpr ⟨x, hx, hc⟩)
  let e := AlgEquiv.ofInjective f hf
  let g₀ := R₀.val.codRestrict f.range fun x => hR₀' x.property
  let g : R₀ →ₐ[ℚ] S := e.symm.toAlgHom.comp g₀
  let : Algebra R₀ S := g.toRingHom.toAlgebra
  let : IsScalarTower R₀ S R := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg Subtype.val (e.apply_symm_apply (g₀ x))).symm
  let B := S ⊗[R₀] A₀
  let e₁ : A ≃ₐ[R] R ⊗[S] B :=
    e₀.trans (Algebra.TensorProduct.cancelBaseChange R₀ S R R A₀).symm
  let : Module.FaithfullyFlat S R :=
    Module.FaithfullyFlat.of_linearEquiv S (S ⊗[F] k)
      (Algebra.IsPushout.equiv F S k R).symm.toLinearEquiv
  let : Module.Finite R (R ⊗[S] B) := Module.Finite.of_surjective e₁.toLinearMap e₁.surjective
  let : Module.Finite S B := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, B,
    inferInstance, inferInstance, inferInstance, inferInstance, ⟨e₁⟩⟩

set_option maxHeartbeats 600000 in
/-- Every finite étale algebra over affine space over an algebraically closed
field of characteristic zero splits over the polynomial base. -/
theorem exists_algEquiv_pi_of_isAlgClosed {k A : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {n : ℕ} [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.Etale (MvPolynomial (Fin n) k) A] [Module.Finite (MvPolynomial (Fin n) k) A] :
    ∃ m : ℕ, Nonempty (A ≃ₐ[MvPolynomial (Fin n) k] (Fin m → MvPolynomial (Fin n) k)) := by
  let R := MvPolynomial (Fin n) k
  obtain ⟨F, _, _, _, _, B, _, _, _, _, ⟨e⟩⟩ := exists_countable_model (k := k) (n := n) (A := A)
  let S := MvPolynomial (Fin n) F
  let T := MvPolynomial (Fin n) ℂ
  let : CharZero F := RingHom.charZero (algebraMap F k)
  obtain ⟨f⟩ := exists_ringHom_complex_of_countable F
  let : Algebra F ℂ := f.toAlgebra
  have h := AlgebraicGeometry.PointManifold.Analytic.exists_algEquiv_pi_of_complex
    (n := n) (A := T ⊗[S] B)
  obtain ⟨m, ⟨e₀⟩⟩ := AlgebraicGeometry.FiniteEtale.exists_algEquiv_pi_of_split_extension h
  exact ⟨m, ⟨e.trans <| (Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e₀).trans
    (Algebra.TensorProduct.piScalarRight S R R (Fin m))⟩⟩

end Langlands.Algebra
