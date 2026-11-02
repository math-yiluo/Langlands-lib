import Langlands.Algebra.ProjectiveTensorCoefficients
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Quotients representing projective tensor vanishing -/

noncomputable section

universe uR uP uA uB uC

open scoped TensorProduct

namespace Langlands.Algebra.ProjectiveTensorCoefficients

section Quotients

variable {R : Type uR} [CommRing R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {A : Type uA} [CommRing A] [Algebra R A]
variable {B : Type uB} [CommRing B] [Algebra R B]

/-- The coefficient algebra imposing the vanishing of a set of tensors. -/
abbrev vanishingQuotient (I : Set (A ⊗[R] P)) := A ⧸ coefficientIdeal I

/-- Adding tensor equations can only enlarge their coefficient ideal. -/
theorem coefficientIdeal_mono {I J : Set (A ⊗[R] P)} (h : I ⊆ J) :
    coefficientIdeal I ≤ coefficientIdeal J :=
  Ideal.span_mono fun _ ⟨x, hx, φ, hφ⟩ => ⟨x, h hx, φ, hφ⟩

/-- A map factors uniquely through the coefficient quotient exactly when it
annihilates all the selected tensors after base change. -/
theorem existsUnique_lift_iff [Module.Projective R P]
    (I : Set (A ⊗[R] P)) (f : A →ₐ[R] B) :
    (∃! g : vanishingQuotient I →ₐ[R] B,
      g.comp (Ideal.Quotient.mkₐ R (coefficientIdeal I)) = f) ↔
      ∀ x ∈ I, f.toLinearMap.rTensor P x = 0 := by
  rw [← coefficientIdeal_le_ker_iff I f]
  constructor
  · rintro ⟨g, hg, _⟩ a ha
    apply RingHom.mem_ker.mpr
    change f a = 0
    have heq := AlgHom.congr_fun hg a
    have hz : Ideal.Quotient.mk (coefficientIdeal I) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hz, map_zero] using heq.symm
  · intro h
    let g := Ideal.Quotient.liftₐ (coefficientIdeal I) f
      (fun a ha => (RingHom.mem_ker (f := f.toRingHom)).mp (h ha))
    refine ⟨g, Ideal.Quotient.liftₐ_comp _ _ _, ?_⟩
    intro g' hg'
    apply Ideal.Quotient.algHom_ext
    exact hg'.trans (Ideal.Quotient.liftₐ_comp _ _ _).symm

/-- The quotient itself annihilates every selected tensor. -/
theorem vanishingQuotient_kills [Module.Projective R P]
    (I : Set (A ⊗[R] P)) (x : A ⊗[R] P) (hx : x ∈ I) :
    (Ideal.Quotient.mkₐ R (coefficientIdeal I)).toLinearMap.rTensor P x = 0 := by
  apply (coefficientIdeal_le_ker_iff I _).mp _ x hx
  exact le_of_eq (Ideal.Quotient.mkₐ_ker R (coefficientIdeal I)).symm

end Quotients

section TensorAlgebras

variable {R : Type uR} [CommRing R]
variable {A : Type uA} [CommRing A] [Algebra R A]
variable {B : Type uB} [CommRing B] [Algebra R B]
variable {C : Type uC} [CommRing C] [Algebra R C]

/-- The usual algebra tensor map agrees with the module tensor map used in the
coefficient construction. -/
@[simp]
theorem algebraTensorMap_apply (f : A →ₐ[R] B) (x : A ⊗[R] C) :
    Algebra.TensorProduct.map f (AlgHom.id R C) x = f.toLinearMap.rTensor C x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => rfl
  | add x y hx hy => simp [hx, hy]

/-- Ideal version of the universal tensor-vanishing criterion. -/
theorem coefficientIdeal_le_ker_iff_ideal [Module.Projective R C]
    (I : Ideal (A ⊗[R] C)) (f : A →ₐ[R] B) :
    coefficientIdeal (I : Set (A ⊗[R] C)) ≤ RingHom.ker f.toRingHom ↔
      I ≤ RingHom.ker (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom := by
  rw [coefficientIdeal_le_ker_iff]
  constructor
  · intro h x hx
    apply RingHom.mem_ker.mpr
    change Algebra.TensorProduct.map f (AlgHom.id R C) x = 0
    rw [algebraTensorMap_apply]
    exact h x hx
  · intro h x hx
    have hz := (RingHom.mem_ker
      (f := (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom)).mp (h hx)
    change Algebra.TensorProduct.map f (AlgHom.id R C) x = 0 at hz
    simpa using hz

/-- Extending an ideal in the tensor algebra commutes with taking its
coefficient ideal, for every coefficient-algebra base change. -/
theorem coefficientIdeal_map [Module.Projective R C]
    (I : Ideal (A ⊗[R] C)) (f : A →ₐ[R] B) :
    coefficientIdeal
      ((I.map (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom) :
        Set (B ⊗[R] C)) =
      (coefficientIdeal (I : Set (A ⊗[R] C))).map f.toRingHom := by
  let K := (coefficientIdeal (I : Set (A ⊗[R] C))).map f.toRingHom
  let q := Ideal.Quotient.mkₐ R K
  apply le_antisymm
  · have hk : coefficientIdeal (I : Set (A ⊗[R] C)) ≤
        RingHom.ker (q.comp f).toRingHom := by
      intro a ha
      apply RingHom.mem_ker.mpr
      change q (f a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.toRingHom ha)
    have hi := (coefficientIdeal_le_ker_iff_ideal I (q.comp f)).mp hk
    have hle : coefficientIdeal
        ((I.map (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom) :
          Set (B ⊗[R] C)) ≤ RingHom.ker q.toRingHom := by
      apply (coefficientIdeal_le_ker_iff_ideal _ q).mpr
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      apply RingHom.mem_ker.mpr
      change Algebra.TensorProduct.map q (AlgHom.id R C)
        (Algebra.TensorProduct.map f (AlgHom.id R C) x) = 0
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
      exact (RingHom.mem_ker
        (f := (Algebra.TensorProduct.map (q.comp f) (AlgHom.id R C)).toRingHom)).mp
          (hi hx)
    simpa only [q, Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using hle
  · rw [← coefficientIdeal_image]
    apply coefficientIdeal_mono
    rintro y ⟨x, hx, rfl⟩
    rw [← algebraTensorMap_apply]
    exact Ideal.mem_map_of_mem _ hx

end TensorAlgebras

end Langlands.Algebra.ProjectiveTensorCoefficients
