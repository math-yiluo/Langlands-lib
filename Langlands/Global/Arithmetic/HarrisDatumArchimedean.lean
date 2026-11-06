import Langlands.Global.Arithmetic.HarrisSetup

/-! # Archimedean components of Hecke characters with prescribed infinity type -/

noncomputable section

namespace Langlands.Global.HarrisDatum

open NumberField InfinitePlace.Completion

variable {K : Type*} [Field K] [NumberField K]

/-- The archimedean idele equal to `y` at `v` and to `1` at every other place. -/
def single (v : InfinitePlace K) : (InfiniteCompletion K v)ˣ →* (InfiniteAdeles K)ˣ :=
  Units.map (InfiniteAdeleRing.ofCompletion v)

theorem infiniteIdeleInclusion_eq (v : InfinitePlace K) (y : (InfiniteCompletion K v)ˣ) :
    infiniteIdeleInclusion K v y = infiniteIdelesInclusion K (single v y) := by
  apply Units.ext
  rfl

theorem infiniteComponent_eq_atInfinity (χ : HeckeCharacter K) (v : InfinitePlace K)
    (y : (InfiniteCompletion K v)ˣ) :
    χ.infiniteComponent v y = χ.atInfinity (single v y) := by
  change χ (ideleClassMap K (infiniteIdeleInclusion K v y)) =
    χ (ideleClassMap K (infiniteIdelesInclusion K (single v y)))
  rw [infiniteIdeleInclusion_eq]

omit [NumberField K] in
theorem coordinate_single_self (v : InfinitePlace K) (y : (InfiniteCompletion K v)ˣ) :
    (InfinityType.coordinate v (single v y) : ℂ) = extensionEmbedding v y := by
  classical
  simp [InfinityType.coordinate_apply, single, InfiniteAdeleRing.ofCompletion_apply]

omit [NumberField K] in
theorem coordinate_single_ne {v w : InfinitePlace K} (h : w ≠ v)
    (y : (InfiniteCompletion K v)ˣ) : InfinityType.coordinate w (single v y) = 1 := by
  classical
  apply Units.ext
  simp [InfinityType.coordinate_apply, single, InfiniteAdeleRing.ofCompletion_apply,
    Pi.mulSingle_eq_of_ne h]

theorem toCharacter_single [IsTotallyComplex K] (a : InfinityType K) (v : InfinitePlace K)
    (y : (InfiniteCompletion K v)ˣ) :
    (InfinityType.toCharacter a (single v y) : ℂ) =
      (extensionEmbedding v y) ^ a v.embedding *
        star (extensionEmbedding v y) ^ a (ComplexEmbedding.conjugate v.embedding) := by
  rw [InfinityType.toCharacter_apply, Finset.prod_eq_single v]
  · simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_star,
      coordinate_single_self]
  · intro w _ hw
    rw [coordinate_single_ne hw]
    simp
  · simp

section LiesOver

open scoped NumberField.LiesOver

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E']

/-- The complex embedding of `E'` at `w` that extends the chosen embedding of `E` at `τ`:
`w.embedding` or its conjugate. -/
def lift (τ : InfinitePlace E) (w : InfinitePlace E') : E' →+* ℂ :=
  open Classical in
  if w.embedding.comp (algebraMap E E') = τ.embedding then w.embedding
  else ComplexEmbedding.conjugate w.embedding

theorem lift_comp (τ : InfinitePlace E) (w : InfinitePlace E') [w.LiesOver τ] :
    (lift τ w).comp (algebraMap E E') = τ.embedding := by
  classical
  unfold lift
  split_ifs with h
  · exact h
  · exact (InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w τ).resolve_left h

theorem lift_of_eq {τ : InfinitePlace E} {w : InfinitePlace E'}
    (h : w.embedding.comp (algebraMap E E') = τ.embedding) : lift τ w = w.embedding := by
  classical
  unfold lift
  simp [h]

theorem lift_of_ne {τ : InfinitePlace E} {w : InfinitePlace E'}
    (h : ¬ w.embedding.comp (algebraMap E E') = τ.embedding) :
    lift τ w = ComplexEmbedding.conjugate w.embedding := by
  classical
  unfold lift
  simp [h]

theorem mk_lift (τ : InfinitePlace E) (w : InfinitePlace E') : InfinitePlace.mk (lift τ w) = w := by
  classical
  unfold lift
  split_ifs
  · exact w.mk_embedding
  · rw [InfinitePlace.mk_conjugate_eq]; exact w.mk_embedding

theorem extensionEmbedding_completionMap_of_eq (τ : InfinitePlace E) (w : InfinitePlace E')
    [w.LiesOver τ] (h : w.embedding.comp (algebraMap E E') = τ.embedding) (x : τ.Completion) :
    extensionEmbedding w (LiesOver.completionMap x) = extensionEmbedding τ x := by
  have : ComplexEmbedding.LiesOver w.embedding τ.embedding := ⟨h⟩
  have := liesOver_extensionEmbedding w τ
  exact liesOver_extensionEmbedding_apply w τ (φ := extensionEmbedding w)

theorem extensionEmbedding_completionMap_of_ne (τ : InfinitePlace E) (w : InfinitePlace E')
    [w.LiesOver τ] (h : ¬ w.embedding.comp (algebraMap E E') = τ.embedding) (x : τ.Completion) :
    extensionEmbedding w (LiesOver.completionMap x) = star (extensionEmbedding τ x) := by
  have h' := (InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w τ).resolve_left h
  have : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w.embedding) τ.embedding := ⟨h'⟩
  have := liesOver_conjugate_extensionEmbedding w τ
  have hx := liesOver_extensionEmbedding_apply w τ
    (φ := ComplexEmbedding.conjugate (extensionEmbedding w)) (x := x)
  rw [ComplexEmbedding.conjugate_coe_eq] at hx
  change star (extensionEmbedding w (LiesOver.completionMap x)) = extensionEmbedding τ x at hx
  rw [← hx, star_star]

omit [Algebra E E'] in
theorem norm_coordinate_single [NumberField E'] (w : InfinitePlace E') (y : (InfiniteCompletion E' w)ˣ) :
    ∏ v : InfinitePlace E', ((‖(InfinityType.coordinate v (single w y) : ℂ)‖ : ℝ) : ℂ) =
      ((‖extensionEmbedding w y‖ : ℝ) : ℂ) := by
  rw [Finset.prod_eq_single w]
  · rw [coordinate_single_self]
  · intro v _ hv
    rw [coordinate_single_ne hv]
    simp
  · simp

variable [NumberField E'] [IsTotallyComplex E']

/-- The archimedean component at `w` of a character of prescribed integral type `A`, read on
`E_τ` through the completion map: `z ↦ z^{A ŝ} z̄^{A ŝ̄}` with `ŝ = lift τ w`. -/
theorem infiniteComponent_completionMap (χ : HeckeCharacter E') (A : InfinityType E')
    (hχ : χ.HasPrescribedInfinityComponent (InfinityType.toCharacter A))
    (τ : InfinitePlace E) (w : InfinitePlace E') [w.LiesOver τ] (x : (InfiniteCompletion E τ)ˣ) :
    (χ.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) :
        ℂ) =
      (extensionEmbedding τ x) ^ A (lift τ w) *
        star (extensionEmbedding τ x) ^ A (ComplexEmbedding.conjugate (lift τ w)) := by
  classical
  rw [infiniteComponent_eq_atInfinity, hχ, toCharacter_single]
  change (extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))) ^ _ *
      star (extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))) ^ _ = _
  by_cases h : w.embedding.comp (algebraMap E E') = τ.embedding
  · rw [extensionEmbedding_completionMap_of_eq τ w h, lift_of_eq h]
  · rw [extensionEmbedding_completionMap_of_ne τ w h, lift_of_ne h, star_star,
      ComplexEmbedding.involutive_conjugate E' w.embedding, mul_comm]

/-- The same for a character whose archimedean part, multiplied by `∏ |z_v|`, has integral
type `t`. -/
theorem infiniteComponent_completionMap_twist (χ : HeckeCharacter E') (t : InfinityType E')
    (hχ : ∀ x : (InfiniteAdeles E')ˣ, (χ.atInfinity x : ℂ) *
        ∏ v : InfinitePlace E', ((‖(InfinityType.coordinate v x : ℂ)‖ : ℝ) : ℂ) =
      (InfinityType.toCharacter t x : ℂ))
    (τ : InfinitePlace E) (w : InfinitePlace E') [w.LiesOver τ] (x : (InfiniteCompletion E τ)ˣ) :
    (χ.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) :
        ℂ) * ((‖extensionEmbedding τ x‖ : ℝ) : ℂ) =
      (extensionEmbedding τ x) ^ t (lift τ w) *
        star (extensionEmbedding τ x) ^ t (ComplexEmbedding.conjugate (lift τ w)) := by
  classical
  have hy := hχ (single w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x))
  rw [norm_coordinate_single, toCharacter_single, ← infiniteComponent_eq_atInfinity] at hy
  have hnorm : ‖extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))‖ =
      ‖extensionEmbedding τ x‖ := by
    by_cases h : w.embedding.comp (algebraMap E E') = τ.embedding
    · rw [extensionEmbedding_completionMap_of_eq τ w h]
    · rw [extensionEmbedding_completionMap_of_ne τ w h, Complex.star_def, Complex.norm_conj]
  change _ * ((‖extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))‖ : ℝ) : ℂ) =
      (extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))) ^ _ *
      star (extensionEmbedding w (LiesOver.completionMap (x : τ.Completion))) ^ _ at hy
  rw [hnorm] at hy
  rw [hy]
  by_cases h : w.embedding.comp (algebraMap E E') = τ.embedding
  · rw [extensionEmbedding_completionMap_of_eq τ w h, lift_of_eq h]
  · rw [extensionEmbedding_completionMap_of_ne τ w h, lift_of_ne h, star_star,
      ComplexEmbedding.involutive_conjugate E' w.embedding, mul_comm]

theorem exp_zpow_mul_star_zpow (θ : ℝ) (a : ℤ) :
    Complex.exp (θ * Complex.I) ^ a * star (Complex.exp (θ * Complex.I)) ^ (-a) =
      Complex.exp ((2 * a * θ : ℝ) * Complex.I) := by
  have hstar : star (Complex.exp (θ * Complex.I)) = Complex.exp ((-θ : ℝ) * Complex.I) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hstar, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable [NumberField E] [IsTotallyComplex E]

/-- Relative regularity of `X * Y` from distinct weights of `X` along the embeddings lifted
from each place of `E`, when `Y` has the same component at all places above a place of `E`. -/
theorem isRelativelyRegular_of_weights (X Y : HeckeCharacter E') (A : InfinityType E')
    (hX : X.HasPrescribedInfinityComponent (InfinityType.toCharacter A))
    (hA : A.IsAnticyclotomic)
    (hY : ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ]
      (x : (InfiniteCompletion E τ)ˣ),
      Y.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) =
        Y.infiniteComponent w' (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x))
    (hdist : ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ],
      w ≠ w' → A (lift τ w) ≠ A (lift τ w')) :
    Harris.IsRelativelyRegular E (X * Y) := by
  intro τ w w' _ _ hne
  set k : ℤ := A (lift τ w) - A (lift τ w') with hk
  have hk0 : k ≠ 0 := sub_ne_zero.mpr (hdist τ w w' hne)
  set θ : ℝ := Real.pi / (2 * k) with hθ
  set z : ℂ := Complex.exp (θ * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hτ : τ.IsComplex := IsTotallyComplex.isComplex τ
  obtain ⟨x₀, hx₀⟩ := surjective_extensionEmbedding_of_isComplex hτ z
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx₀
    exact hz0 hx₀.symm
  refine ⟨Units.mk0 x₀ hx₀0, fun heq => ?_⟩
  have h := congrArg (fun u : ℂˣ => (u : ℂ)) heq
  simp only [HeckeCharacter.infiniteComponent_mul, ContinuousMonoidHom.mul_apply, Units.val_mul] at h
  rw [hY τ w w' (Units.mk0 x₀ hx₀0)] at h
  have hYne : (Y.infiniteComponent w'
      (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom (Units.mk0 x₀ hx₀0)) : ℂ)
      ≠ 0 := Units.ne_zero _
  have hX' := mul_right_cancel₀ hYne h
  rw [infiniteComponent_completionMap X A hX τ w, infiniteComponent_completionMap X A hX τ w',
    hA (lift τ w), hA (lift τ w')] at hX'
  simp only [Units.val_mk0, hx₀, hz] at hX'
  rw [exp_zpow_mul_star_zpow, exp_zpow_mul_star_zpow] at hX'
  have hdiff : Complex.exp ((2 * k * θ : ℝ) * Complex.I) = 1 := by
    have hsub : ((2 * k * θ : ℝ) : ℂ) * Complex.I =
        ((2 * (A (lift τ w)) * θ : ℝ) : ℂ) * Complex.I -
          ((2 * (A (lift τ w')) * θ : ℝ) : ℂ) * Complex.I := by
      rw [hk]
      push_cast
      ring
    rw [hsub, Complex.exp_sub, hX', div_self (Complex.exp_ne_zero _)]
  have hpi : ((2 * k * θ : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I := by
    congr 1
    rw [hθ]
    push_cast
    field_simp
  rw [hpi, Complex.exp_pi_mul_I] at hdiff
  norm_num at hdiff

end LiesOver

section Weights

variable {K₀ : Type*} [Field K₀] [NumberField K₀] [IsTotallyComplex K₀]

omit [NumberField K₀] in
theorem conjugate_ne (τK : K₀ →+* ℂ) : ComplexEmbedding.conjugate τK ≠ τK := by
  intro h
  exact (InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex (InfinitePlace.mk τK)))
    (ComplexEmbedding.isReal_iff.mpr h)

/-- An imaginary quadratic field has exactly the two embeddings `τK` and `τ̄K`. -/
theorem eq_or_eq_conjugate (h2 : Module.finrank ℚ K₀ = 2) (τK κ : K₀ →+* ℂ) :
    κ = τK ∨ κ = ComplexEmbedding.conjugate τK := by
  classical
  by_contra hne
  push Not at hne
  have hcard := NumberField.Embeddings.card K₀ ℂ
  rw [h2] at hcard
  have h3 : ({κ, τK, ComplexEmbedding.conjugate τK} : Finset (K₀ →+* ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]),
      Finset.card_pair_eq_two_iff.mpr (conjugate_ne τK).symm]
  have := Finset.card_le_univ ({κ, τK, ComplexEmbedding.conjugate τK} : Finset (K₀ →+* ℂ))
  omega

theorem conjugate_comp {A B : Type*} [Field A] [Field B] (σ : B →+* ℂ) (f : A →+* B) :
    (ComplexEmbedding.conjugate σ).comp f = ComplexEmbedding.conjugate (σ.comp f) :=
  RingHom.ext fun _ => rfl

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E'] [NumberField E']
  (h2 : Module.finrank ℚ K₀ = 2) (j : K₀ →+* E) (τK : K₀ →+* ℂ)

/-- Integral weights `σ ↦ ±(g σ + 1)`, positive exactly on the embeddings over `τK`. -/
def regularWeights : InfinityType E' :=
  open Classical in
  fun σ => if σ.comp ((algebraMap E E').comp j) = τK then
      ((Fintype.equivFin (E' →+* ℂ) σ : ℕ) : ℤ) + 1
    else -(((Fintype.equivFin (E' →+* ℂ) (ComplexEmbedding.conjugate σ) : ℕ) : ℤ) + 1)

include h2 in
theorem regularWeights_anticyclotomic :
    (regularWeights (E := E) (E' := E') j τK).IsAnticyclotomic := by
  classical
  intro σ
  unfold regularWeights
  rw [conjugate_comp]
  have h1 : ¬ ComplexEmbedding.conjugate τK = τK := conjugate_ne τK
  rcases eq_or_eq_conjugate h2 τK (σ.comp ((algebraMap E E').comp j)) with h | h
  · rw [h]
    simp [h1, ComplexEmbedding.involutive_conjugate E' σ]
  · rw [h, ComplexEmbedding.involutive_conjugate K₀ τK]
    simp [h1]

omit [NumberField K₀] [IsTotallyComplex K₀] in
theorem regularWeights_distinct :
    InfinityType.DistinctWeightsAbove ((algebraMap E E').comp j) τK
      (regularWeights (E := E) (E' := E') j τK) := by
  classical
  rintro ⟨σ, hσ⟩ ⟨σ', hσ'⟩ h
  have h' : ((Fintype.equivFin (E' →+* ℂ) σ : ℕ) : ℤ) + 1 =
      ((Fintype.equivFin (E' →+* ℂ) σ' : ℕ) : ℤ) + 1 := by
    simpa [regularWeights, hσ, hσ'] using h
  apply Subtype.ext
  show σ = σ'
  exact (Fintype.equivFin _).injective (Fin.ext (by omega))

/-- The weight-one type equal to `1` on the embeddings over `τK` and `0` on the others. -/
def halfWeights : InfinityType E' :=
  open Classical in
  fun σ => if σ.comp ((algebraMap E E').comp j) = τK then 1 else 0

omit [NumberField E'] in
include h2 in
theorem halfWeights_pure : (halfWeights (E := E) (E' := E') j τK).IsPureOfWeight 1 := by
  classical
  intro σ
  unfold halfWeights
  rw [conjugate_comp]
  have h1 : ¬ ComplexEmbedding.conjugate τK = τK := conjugate_ne τK
  rcases eq_or_eq_conjugate h2 τK (σ.comp ((algebraMap E E').comp j)) with h | h
  · rw [h]
    simp [h1]
  · rw [h, ComplexEmbedding.involutive_conjugate K₀ τK]
    simp [h1]

end Weights

section Regularity

open scoped NumberField.LiesOver

variable {K₀ : Type*} [Field K₀] [NumberField K₀] [IsTotallyComplex K₀]
  {E E' : Type*} [Field E] [Field E'] [Algebra E E'] [NumberField E] [NumberField E']
  (h2 : Module.finrank ℚ K₀ = 2) (j : K₀ →+* E) (τK : K₀ →+* ℂ)

omit [NumberField K₀] [IsTotallyComplex K₀] [NumberField E] [NumberField E'] in
theorem lift_comp_j (τ : InfinitePlace E) (w : InfinitePlace E') [w.LiesOver τ] :
    (lift τ w).comp ((algebraMap E E').comp j) = τ.embedding.comp j := by
  rw [← RingHom.comp_assoc, lift_comp]

omit [NumberField E] [NumberField E'] in
include h2 in
/-- Distinct weights above `τK` separate the lifted embeddings at distinct places above any
place of `E`. -/
theorem weights_ne_of_distinct (A : InfinityType E') (hA : A.IsAnticyclotomic)
    (hD : InfinityType.DistinctWeightsAbove ((algebraMap E E').comp j) τK A)
    (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ]
    (hne : w ≠ w') : A (lift τ w) ≠ A (lift τ w') := by
  have hl : lift τ w ≠ lift τ w' := fun h => hne (by rw [← mk_lift τ w, h, mk_lift])
  intro heq
  rcases eq_or_eq_conjugate h2 τK (τ.embedding.comp j) with h | h
  · exact hl (congrArg Subtype.val (@hD ⟨lift τ w, (lift_comp_j j τ w).trans h⟩
      ⟨lift τ w', (lift_comp_j j τ w').trans h⟩ heq))
  · have c1 : (ComplexEmbedding.conjugate (lift τ w)).comp ((algebraMap E E').comp j) = τK := by
      rw [conjugate_comp, lift_comp_j, h, ComplexEmbedding.involutive_conjugate K₀ τK]
    have c2 : (ComplexEmbedding.conjugate (lift τ w')).comp ((algebraMap E E').comp j) = τK := by
      rw [conjugate_comp, lift_comp_j, h, ComplexEmbedding.involutive_conjugate K₀ τK]
    have hc := congrArg Subtype.val (@hD ⟨_, c1⟩ ⟨_, c2⟩ (by
      change A (ComplexEmbedding.conjugate (lift τ w)) = A (ComplexEmbedding.conjugate (lift τ w'))
      rw [hA, hA, heq]))
    apply hl
    have hc' := congrArg ComplexEmbedding.conjugate hc
    simp only [ComplexEmbedding.involutive_conjugate E' _] at hc'
    exact hc'

omit [NumberField K₀] [IsTotallyComplex K₀] [NumberField E] in
/-- A character realizing the weight-one type `halfWeights` has the same component, read on
`E_τ`, at all places above `τ`. -/
theorem halfWeight_component_eq [IsTotallyComplex E'] (ψ : HeckeCharacter E')
    (hψ : ∀ x : (InfiniteAdeles E')ˣ, (ψ.atInfinity x : ℂ) *
        ∏ v : InfinitePlace E', ((‖(InfinityType.coordinate v x : ℂ)‖ : ℝ) : ℂ) =
      (InfinityType.toCharacter (halfWeights (E := E) j τK) x : ℂ))
    (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ]
    (x : (InfiniteCompletion E τ)ˣ) :
    ψ.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) =
      ψ.infiniteComponent w' (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x) := by
  have e1 := infiniteComponent_completionMap_twist ψ _ hψ τ w x
  have e2 := infiniteComponent_completionMap_twist ψ _ hψ τ w' x
  have ht : halfWeights (E := E) j τK (lift τ w) = halfWeights (E := E) j τK (lift τ w') := by
    unfold halfWeights; rw [lift_comp_j, lift_comp_j]
  have ht' : halfWeights (E := E) j τK (ComplexEmbedding.conjugate (lift τ w)) =
      halfWeights (E := E) j τK (ComplexEmbedding.conjugate (lift τ w')) := by
    unfold halfWeights; rw [conjugate_comp, conjugate_comp, lift_comp_j, lift_comp_j]
  rw [ht, ht'] at e1
  have hx : extensionEmbedding τ (x : InfiniteCompletion E τ) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero x)
  have hn : ((‖extensionEmbedding τ (x : InfiniteCompletion E τ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hx
  apply Units.ext
  exact mul_right_cancel₀ hn (e1.trans e2.symm)

end Regularity

section Algebraicity

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

theorem toCharacter_add (t s : InfinityType K) (x : (InfiniteAdeles K)ˣ) :
    InfinityType.toCharacter (t + s) x =
      InfinityType.toCharacter t x * InfinityType.toCharacter s x :=
  Harris.toCharacter_add t s x

omit [IsTotallyComplex K] in
theorem atInfinity_mul (X Y : HeckeCharacter K) (x : (InfiniteAdeles K)ˣ) :
    (X * Y).atInfinity x = X.atInfinity x * Y.atInfinity x := rfl

theorem isAlgebraicAfterTwist_zero_of_type (X : HeckeCharacter K) (A : InfinityType K)
    (hX : X.HasPrescribedInfinityComponent (InfinityType.toCharacter A)) :
    Harris.IsAlgebraicAfterTwist 0 X :=
  (Harris.isAlgebraicAfterTwist_zero_iff X).mpr ⟨A, hX⟩

theorem isAlgebraicAfterTwist_one_of_types (X ψ : HeckeCharacter K) (A t : InfinityType K)
    (hX : X.HasPrescribedInfinityComponent (InfinityType.toCharacter A))
    (hψ : ∀ x : (InfiniteAdeles K)ˣ, (ψ.atInfinity x : ℂ) *
        ∏ v : InfinitePlace K, ((‖(InfinityType.coordinate v x : ℂ)‖ : ℝ) : ℂ) =
      (InfinityType.toCharacter t x : ℂ)) :
    Harris.IsAlgebraicAfterTwist 1 (X * ψ) := by
  refine ⟨A + t, fun x => ?_⟩
  rw [atInfinity_mul, Units.val_mul, toCharacter_add, Units.val_mul, ← hψ x, hX]
  simp only [pow_one]
  ring

theorem isAlgebraicAfterTwist_of_mod_two (χ : HeckeCharacter K) (k : ℕ)
    (h : Harris.IsAlgebraicAfterTwist (k % 2) χ) : Harris.IsAlgebraicAfterTwist k χ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rwa [Nat.mod_eq_of_lt hk] at h
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [Harris.isAlgebraicAfterTwist_add_two_iff]
      exact ih m (by omega) (by rwa [Nat.add_mod_right] at h)

omit [IsTotallyComplex K] in
theorem isConjugateInverse_mul [IsCMField K] (X Y : HeckeCharacter K)
    (hX : Harris.IsConjugateInverse X) (hY : Harris.IsConjugateInverse Y) :
    Harris.IsConjugateInverse (X * Y) := by
  intro x
  change X _ * Y _ = (X x * Y x)⁻¹
  rw [hX x, hY x, mul_inv]

end Algebraicity

end Langlands.Global.HarrisDatum
