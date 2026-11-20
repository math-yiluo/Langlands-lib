import Langlands.Algebra.ProjectiveTensorCoefficients
import Langlands.RingTheory.Smooth.SectionJetBaseChange

/-! # The closed base locus for isomorphisms on section jets -/

noncomputable section

universe u v w t

open scoped TensorProduct

namespace Algebra.SectionJet

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  {A : Type w} [CommRing A] [Algebra R A]
  {δ : P →ₐ[R] R} {ε : A →ₐ[R] R} {f : P →ₐ[R] A} (hf : ε.comp f = δ)

include hf in
/-- An augmented map carries each power of the source augmentation ideal into the
corresponding power of the target augmentation ideal. -/
theorem ker_pow_le_comap (k : ℕ) :
    RingHom.ker δ ^ k ≤ (RingHom.ker ε ^ k).comap f := by
  have h : RingHom.ker δ ≤ (RingHom.ker ε).comap f := by
    intro p hp
    change ε (f p) = 0
    rw [← AlgHom.comp_apply, hf]
    exact hp
  exact (Ideal.pow_right_mono h k).trans (Ideal.le_comap_pow _ k)

/-- The map on actual jets induced by an augmented algebra map. -/
def jetMap (n : ℕ) : Quotient δ n →ₐ[R] Quotient ε n :=
  Ideal.quotientMapₐ _ f (ker_pow_le_comap hf (n + 1))

@[simp]
theorem jetMap_mk (n : ℕ) (p : P) :
    jetMap hf n (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (f p) := rfl

variable (B : Type t) [CommRing B] [Algebra R B]

include hf in
/-- An augmented map remains augmented on arbitrary extension of scalars. -/
theorem baseChangeAugmentation_comp_map :
    (baseChangeAugmentation ε B).comp (Algebra.TensorProduct.map (AlgHom.id B B) f) =
      baseChangeAugmentation δ B := by
  ext p
  simp [show ε (f p) = δ p from AlgHom.congr_fun hf p]

/-- The comparison with the tensor product respects the actual base-changed jet map. -/
theorem baseChangeEquiv_jetMap (n : ℕ) (x : B ⊗[R] Quotient δ n) :
    baseChangeEquiv ε B n
      (Algebra.TensorProduct.map (AlgHom.id B B) (jetMap hf n) x) =
    jetMap (baseChangeAugmentation_comp_map hf B) n (baseChangeEquiv δ B n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b p =>
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    simp
  | add x y hx hy => simp [hx, hy]

/-- The ideal imposing that the kernels of all jet maps vanish after scalar extension. -/
def jetIsomorphismIdeal : Ideal R :=
  ⨆ n : ℕ, coefficientIdeal
    ((fun x : Quotient δ n => (1 : R) ⊗ₜ[R] x) '' (RingHom.ker (jetMap hf n) : Set _))

/-- When the source algebra is smooth and its maps onto the target jets are surjective,
the isomorphism condition on all jets after scalar extension is defined by one ideal. -/
def SectionJetIsomorphismLocusStatement : Prop :=
  ∀ (R : Type u) (P : Type v) (A : Type w) (B : Type t)
    [CommRing R] [CommRing P] [CommRing A] [CommRing B]
    [Algebra R P] [Algebra R A] [Algebra R B] [Smooth R P]
    (δ : P →ₐ[R] R) (ε : A →ₐ[R] R) (f : P →ₐ[R] A)
    (hf : ε.comp f = δ),
    (∀ n : ℕ, Function.Surjective (jetMap hf n)) →
      (jetIsomorphismIdeal hf ≤ RingHom.ker (algebraMap R B) ↔
        ∀ n : ℕ, Function.Bijective (jetMap (baseChangeAugmentation_comp_map hf B) n))

theorem sectionJetIsomorphismLocus : SectionJetIsomorphismLocusStatement.{u, v, w, t} := by
  intro R P A B _ _ _ _ _ _ _ _ δ ε f hf hsurj
  simp only [jetIsomorphismIdeal, iSup_le_iff]
  refine forall_congr' fun n => ?_
  let g := jetMap hf n
  let gB := Algebra.TensorProduct.map (AlgHom.id B B) g
  let j := jetMap (baseChangeAugmentation_comp_map hf B) n
  have hbij : Function.Bijective j ↔ Function.Bijective gB := by
    rw [← Function.Bijective.of_comp_iff j (baseChangeEquiv δ B n).bijective,
      ← (baseChangeEquiv ε B n).bijective.of_comp_iff' gB]
    have he : ⇑j ∘ ⇑(baseChangeEquiv δ B n) = ⇑(baseChangeEquiv ε B n) ∘ ⇑gB :=
      funext fun x => (baseChangeEquiv_jetMap hf B n x).symm
    rw [he]
  have hgB : Function.Surjective gB :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id (hsurj n)
  have hker : RingHom.ker gB.toRingHom =
      (RingHom.ker g).map
        (Algebra.TensorProduct.includeRight : Quotient δ n →ₐ[R] B ⊗[R] Quotient δ n) :=
    Algebra.TensorProduct.lTensor_ker g (hsurj n)
  change
    coefficientIdeal ((fun x : Quotient δ n => (1 : R) ⊗ₜ[R] x) ''
      (RingHom.ker g : Set _)) ≤ RingHom.ker (Algebra.ofId R B).toRingHom ↔
    Function.Bijective j
  rw [hbij, show Function.Bijective gB ↔ Function.Injective gB.toRingHom from
      ⟨And.left, fun h => ⟨h, hgB⟩⟩,
    RingHom.injective_iff_ker_eq_bot, hker, Ideal.map_eq_bot_iff_le_ker,
    coefficientIdeal_le_ker_iff _ (Algebra.ofId R B)]
  constructor
  · intro h x hx
    have hzero := h _ ⟨x, hx, rfl⟩
    rw [LinearMap.rTensor_tmul, show (Algebra.ofId R B).toLinearMap 1 = 1 from
      map_one (Algebra.ofId R B)] at hzero
    exact hzero
  · rintro h _ ⟨x, hx, rfl⟩
    rw [LinearMap.rTensor_tmul, show (Algebra.ofId R B).toLinearMap 1 = 1 from
      map_one (Algebra.ofId R B)]
    exact h hx

end Algebra.SectionJet
