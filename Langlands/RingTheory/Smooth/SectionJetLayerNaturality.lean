import Langlands.RingTheory.Smooth.SectionJetHomogeneousLayers

/-! # Independence of lifts and coordinate changes for actual augmentation layers -/

noncomputable section

universe u v w w'

namespace Algebra.SectionJet.Coordinates

open MvPolynomial
open Langlands.GroupScheme.CoordinateWeights

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ε : A →ₐ[R] R} {σ : Type w} {τ : Type w'}

/-- Cotangent equality of augmentation-ideal lifts is equality modulo the square. -/
theorem sub_mem_sq_of_classMap_eq {a a' : A} (ha : ε a = 0) (ha' : ε a' = 0)
    (h : AugmentedAlgebra.classMap ε a = AugmentedAlgebra.classMap ε a') :
    a - a' ∈ RingHom.ker ε ^ 2 := by
  apply ((RingHom.ker ε).toCotangent_eq (x := ⟨a, ha⟩) (y := ⟨a', ha'⟩)).mp
  exact (AugmentedAlgebra.classMap_ideal ε ⟨a, ha⟩).symm.trans
    (h.trans (AugmentedAlgebra.classMap_ideal ε ⟨a', ha'⟩))

/-- Evaluation at two systems of lifts with the same cotangent classes agrees to
one higher order on the corresponding power of the variable ideal. -/
theorem aeval_sub_aeval_mem_pow_succ (z z' : σ → A)
    (hz : ∀ s, ε (z s) = 0) (hz' : ∀ s, ε (z' s) = 0)
    (hzz' : ∀ s, AugmentedAlgebra.classMap ε (z s) =
      AugmentedAlgebra.classMap ε (z' s)) (d : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ idealOfVars σ R ^ d) :
    aeval z p - aeval z' p ∈ RingHom.ker ε ^ (d + 1) := by
  have hzmap : (idealOfVars σ R).map (aeval z) ≤ RingHom.ker ε := by
    apply Ideal.map_le_iff_le_comap.mpr
    simpa only [pow_one] using idealOfVars_pow_le_comap z hz 1
  have hzmap' : (idealOfVars σ R).map (aeval z') ≤ RingHom.ker ε := by
    apply Ideal.map_le_iff_le_comap.mpr
    simpa only [pow_one] using idealOfVars_pow_le_comap z' hz' 1
  apply Langlands.GroupScheme.TorusUnipotence.sub_mem_pow_succ
    (idealOfVars σ R) (Set.range X) rfl
    (fun q => ⟨constantCoeff q,
      Langlands.GroupScheme.TorusUnipotence.sub_C_constantCoeff_mem_idealOfVars q⟩)
    (RingHom.ker ε) (aeval z) (aeval z') hzmap hzmap' ?_ d hp
  rintro _ ⟨s, rfl⟩
  simpa only [aeval_X] using sub_mem_sq_of_classMap_eq (hz s) (hz' s) (hzz' s)

/-- The actual homogeneous evaluation map depends only on the cotangent classes
of the chosen lifts. -/
theorem homogeneousToLayer_eq_of_classMap_eq (z z' : σ → A)
    (hz : ∀ s, ε (z s) = 0) (hz' : ∀ s, ε (z' s) = 0)
    (hzz' : ∀ s, AugmentedAlgebra.classMap ε (z s) =
      AugmentedAlgebra.classMap ε (z' s)) (n : ℕ) :
    homogeneousToLayer z hz n = homogeneousToLayer z' hz' n := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  rw [homogeneousToLayer_val, homogeneousToLayer_val, Ideal.Quotient.eq]
  exact aeval_sub_aeval_mem_pow_succ z z' hz hz' hzz' (n + 1)
    (homogeneous_mem_idealOfVars_pow p.property)

/-- Substitution by linear forms preserves each homogeneous degree. -/
def homogeneousSubstitution (f : τ → homogeneousSubmodule σ R 1) (d : ℕ) :
    homogeneousSubmodule τ R d →ₗ[R] homogeneousSubmodule σ R d :=
  (((aeval (fun t => (f t).val)).toLinearMap).comp
    (homogeneousSubmodule τ R d).subtype).codRestrict _ (fun p => by
      change (aeval (fun t => (f t).val) p.val).IsHomogeneous d
      simpa only [one_mul] using p.property.aeval (fun t => (f t).val)
        (fun t => (f t).property))

@[simp]
theorem homogeneousSubstitution_val (f : τ → homogeneousSubmodule σ R 1) (d : ℕ)
    (p : homogeneousSubmodule τ R d) :
    (homogeneousSubstitution f d p).val = aeval (fun t => (f t).val) p.val := rfl

/-- Evaluating linear forms in augmentation-ideal lifts again gives such a lift. -/
theorem augmentation_aeval_linear (z : σ → A) (hz : ∀ s, ε (z s) = 0)
    (f : homogeneousSubmodule σ R 1) : ε (aeval z f.val) = 0 := by
  have hf := idealOfVars_pow_le_comap z hz 1 (homogeneous_mem_idealOfVars_pow f.property)
  simpa only [pow_one, Ideal.mem_comap, RingHom.mem_ker] using hf

/-- Coordinate substitution commutes with actual layer evaluation whenever it gives
the specified new cotangent classes. -/
theorem homogeneousToLayer_substitution (z : σ → A) (hz : ∀ s, ε (z s) = 0)
    (z' : τ → A) (hz' : ∀ t, ε (z' t) = 0)
    (f : τ → homogeneousSubmodule σ R 1)
    (hf : ∀ t, AugmentedAlgebra.classMap ε (aeval z (f t).val) =
      AugmentedAlgebra.classMap ε (z' t))
    (n : ℕ) (p : homogeneousSubmodule τ R (n + 1)) :
    homogeneousToLayer z hz n (homogeneousSubstitution f (n + 1) p) =
      homogeneousToLayer z' hz' n p := by
  let zf : τ → A := fun t => aeval z (f t).val
  have hzf : ∀ t, ε (zf t) = 0 := fun t => augmentation_aeval_linear z hz (f t)
  calc
    homogeneousToLayer z hz n (homogeneousSubstitution f (n + 1) p) =
        homogeneousToLayer zf hzf n p := by
      apply Subtype.ext
      change Ideal.Quotient.mk _ (aeval z (aeval (fun t => (f t).val) p.val)) =
        Ideal.Quotient.mk _ (aeval zf p.val)
      rw [comp_aeval_apply]
    _ = homogeneousToLayer z' hz' n p :=
      LinearMap.congr_fun (homogeneousToLayer_eq_of_classMap_eq zf z' hzf hz' hf n) p

/-- The linear polynomial with a specified finite family of coefficients. -/
def linearForm (c : σ →₀ R) : MvPolynomial σ R :=
  Finsupp.linearCombination R X c

theorem linearForm_isHomogeneous (c : σ →₀ R) : (linearForm c).IsHomogeneous 1 := by
  classical
  change linearForm c ∈ homogeneousSubmodule σ R 1
  unfold linearForm
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ (fun s _ =>
    Submodule.smul_mem _ _ (isHomogeneous_X R s))

theorem aeval_linearForm (z : σ → A) (c : σ →₀ R) :
    aeval z (linearForm c) = Finsupp.linearCombination R z c := by
  unfold linearForm
  rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination]
  have h : (⇑(aeval z : MvPolynomial σ R →ₐ[R] A).toLinearMap ∘ X) = z :=
    funext (fun s => aeval_X z s)
  rw [h]

/-- The degree-preserving substitution determined by the transition matrix of two
actual cotangent bases. -/
def cotangentBasisChange (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (b' : Module.Basis τ R (RingHom.ker ε).Cotangent) (d : ℕ) :
    homogeneousSubmodule τ R d →ₗ[R] homogeneousSubmodule σ R d :=
  homogeneousSubstitution
    (fun t => ⟨linearForm (b.repr (b' t)), linearForm_isHomogeneous _⟩) d

/-- The actual higher-layer coordinates transform by the symmetric polynomial
substitution of the actual cotangent transition matrix. -/
theorem homogeneousToLayer_cotangentBasisChange
    (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, AugmentedAlgebra.classMap ε (z s) = b s)
    (z' : τ → A) (b' : Module.Basis τ R (RingHom.ker ε).Cotangent)
    (hz' : ∀ t, ε (z' t) = 0)
    (hzb' : ∀ t, AugmentedAlgebra.classMap ε (z' t) = b' t)
    (n : ℕ) (p : homogeneousSubmodule τ R (n + 1)) :
    homogeneousToLayer z hz n (cotangentBasisChange b b' (n + 1) p) =
      homogeneousToLayer z' hz' n p := by
  apply homogeneousToLayer_substitution
  intro t
  rw [aeval_linearForm, hzb', Finsupp.apply_linearCombination]
  have hb : (AugmentedAlgebra.classMap ε ∘ z) = b := funext hzb
  rw [hb]
  exact b.linearCombination_repr (b' t)

end Algebra.SectionJet.Coordinates
