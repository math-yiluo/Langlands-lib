import Langlands.RingTheory.Smooth.SectionJetBaseChange
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.FiniteType

/-! # Noetherian models of smooth affine sections and ideals -/

noncomputable section

universe u

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra.SectionJet

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A smooth model together with its section and an ideal that extend to the given data. -/
structure NoetherianModel (ε : B →ₐ[R] R) (J : Ideal B) where
  (Base : Type u)
  [commRingBase : CommRing Base]
  [algebraBase : Algebra Base R]
  [isNoetherianRing : IsNoetherianRing Base]
  (Model : Type u)
  [commRingModel : CommRing Model]
  [algebraModel : Algebra Base Model]
  [smooth : Smooth Base Model]
  augmentation : Model →ₐ[Base] Base
  ideal : Ideal Model
  comparison : R ⊗[Base] Model ≃ₐ[R] B
  augmentation_eq (x : R ⊗[Base] Model) :
    ε (comparison x) = baseChangeAugmentation augmentation R x
  ideal_map :
    ideal.map (comparison.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Model →ₐ[Base] R ⊗[Base] Model).toRingHom) = J

attribute [instance] NoetherianModel.commRingBase NoetherianModel.algebraBase
  NoetherianModel.isNoetherianRing NoetherianModel.commRingModel NoetherianModel.algebraModel
  NoetherianModel.smooth

set_option maxHeartbeats 800000 in
/-- A finitely generated ideal of a smooth algebra with a section admits a smooth
Noetherian model carrying both the section and the ideal. -/
def noetherianModel [Smooth R B] (ε : B →ₐ[R] R) (J : Ideal B) (hJ : J.FG) :
    NoetherianModel ε J := Classical.choice (by
  classical
  obtain ⟨R₀, B₀, _, _, hR₀, _, ⟨e⟩⟩ := Smooth.exists_subalgebra_fg ℤ R B
  let : FiniteType ℤ R₀ := (Subalgebra.fg_iff_finiteType R₀).mp hR₀
  let : IsNoetherianRing R₀ := FiniteType.isNoetherianRing ℤ _
  obtain ⟨s, hs⟩ := FiniteType.out (R := R₀) (A := B₀)
  obtain ⟨t, ht⟩ := hJ
  have hex (b : B) : ∃ Q : Finset (R × B₀), e b = ∑ x ∈ Q, x.1 ⊗ₜ[R₀] x.2 :=
    TensorProduct.exists_finset (e b)
  choose Q hQ using hex
  let e₀ : B₀ →ₐ[R₀] R :=
    (ε.restrictScalars R₀).comp ((e.symm.toAlgHom.restrictScalars R₀).comp
      Algebra.TensorProduct.includeRight)
  let coeff : Finset R := s.image e₀ ∪ t.biUnion (fun b => (Q b).image Prod.fst)
  let A := Algebra.adjoin R₀ (coeff : Set R)
  let : FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp ⟨coeff, rfl⟩
  let : IsNoetherianRing A := FiniteType.isNoetherianRing R₀ _
  have hA : ∀ x ∈ coeff, x ∈ A := fun x hx => Algebra.subset_adjoin hx
  have he₀ : ∀ b : B₀, e₀ b ∈ A := by
    have hle : (⊤ : Subalgebra R₀ B₀) ≤ A.comap e₀ := by
      rw [← hs]
      exact Algebra.adjoin_le fun b hb => hA _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem e₀ hb))
    exact fun b => hle (show b ∈ (⊤ : Subalgebra R₀ B₀) from trivial)
  let e₁ : B₀ →ₐ[R₀] A := e₀.codRestrict A he₀
  let B₁ := A ⊗[R₀] B₀
  let ε₁ : B₁ →ₐ[A] A :=
    Algebra.TensorProduct.lift (AlgHom.id A A) e₁ (fun _ _ => Commute.all _ _)
  let cmp := (Algebra.TensorProduct.cancelBaseChange R₀ A R R B₀).trans e.symm
  let inc : B₁ →ₐ[A] B :=
    (cmp.toAlgHom.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let liftCoeff (r : R) : A := if hr : r ∈ A then ⟨r, hr⟩ else 0
  let liftGen (b : B) : B₁ := ∑ x ∈ Q b, liftCoeff x.1 ⊗ₜ[R₀] x.2
  have hgen (b : B) (hb : b ∈ t) : inc (liftGen b) = b := by
    apply e.injective
    change e (cmp (1 ⊗ₜ[A] liftGen b)) = e b
    rw [hQ b]
    simp only [liftGen, TensorProduct.tmul_sum, map_sum, cmp, AlgEquiv.trans_apply,
      AlgEquiv.apply_symm_apply, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def,
      mul_one]
    apply Finset.sum_congr rfl
    intro x hx
    have hxA : x.1 ∈ A := hA _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨b, hb, Finset.mem_image_of_mem Prod.fst hx⟩))
    simp only [liftCoeff, dite_eq_left hxA]
    rfl
  let J₁ : Ideal B₁ := Ideal.span (liftGen '' (t : Set B))
  have hJ₁ : J₁.map inc.toRingHom = J := by
    dsimp only [J₁]
    rw [Ideal.map_span, ht.symm, Set.image_image]
    congr 1
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        hgen c hc] using hc
    · intro hb
      exact ⟨b, hb, hgen b hb⟩
  have haug (x : R ⊗[A] B₁) :
      ε (cmp x) = baseChangeAugmentation (R := A) (A := B₁) ε₁ R x := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        rw [baseChangeAugmentation_tmul]
        change ε (e.symm (Algebra.TensorProduct.cancelBaseChange R₀ A R R B₀
          (r ⊗ₜ[A] (a ⊗ₜ[R₀] b)))) = r * algebraMap A R (ε₁ (a ⊗ₜ[R₀] b))
        rw [Algebra.TensorProduct.cancelBaseChange_tmul (R := R₀) (S := A) R R B₀ r a b,
          show ε₁ (a ⊗ₜ[R₀] b) = a * e₁ b from rfl, map_mul]
        rw [show ((a • r) ⊗ₜ[R₀] b) =
          (a • r) • ((1 : R) ⊗ₜ[R₀] b) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
        simp only [map_smul, Algebra.smul_def, map_mul, ε.commutes]
        change (algebraMap A R a * r) * ε (e.symm (1 ⊗ₜ[R₀] b)) =
          r * (algebraMap A R a * ε (e.symm (1 ⊗ₜ[R₀] b)))
        ac_rfl
      | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact ⟨{
    Base := A
    commRingBase := inferInstanceAs (CommRing A)
    algebraBase := inferInstanceAs (Algebra A R)
    isNoetherianRing := inferInstanceAs (IsNoetherianRing A)
    Model := B₁
    commRingModel := inferInstanceAs (CommRing (A ⊗[R₀] B₀))
    algebraModel := inferInstanceAs (Algebra A (A ⊗[R₀] B₀))
    smooth := inferInstanceAs (Smooth A (A ⊗[R₀] B₀))
    augmentation := ε₁
    ideal := J₁
    comparison := cmp
    augmentation_eq := haug
    ideal_map := hJ₁
  }⟩)

end Algebra.SectionJet
