import Langlands.GroupScheme.Rational.PositiveRootMonoidPointed
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.HighestWeightScalarEndomorphisms
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Langlands.GroupScheme.Rational.PathFundamentalWeights

/-! # Weights of tensor products of representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  (p : SplitPinning H)

/-- If `α ≤ λ`, `β ≤ μ` and `α + β = λ + μ` for the positive root order, then `α = λ` and
`β = μ`. -/
theorem eq_of_add_eq_of_sub_mem {lam mu α β : characterLattice p.torus}
    (hα : lam - α ∈ p.positiveRootMonoid) (hβ : mu - β ∈ p.positiveRootMonoid)
    (h : α + β = lam + mu) : α = lam ∧ β = mu := by
  have h1 : lam - α = -(mu - β) := by
    have : lam - α + (mu - β) = 0 := by rw [sub_add_sub_comm, ← h, sub_self]
    exact eq_neg_of_add_eq_zero_left this
  have h2 := p.eq_zero_of_mem_positiveRootMonoid_of_neg_mem hα (by rw [h1, neg_neg]; exact hβ)
  refine ⟨(sub_eq_zero.mp h2).symm, ?_⟩
  rw [h2, eq_comm, neg_eq_zero, sub_eq_zero] at h1
  exact h1.symm

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The tensor product of weight vectors is a weight vector of the tensor product, of the sum
weight. -/
theorem kronecker_mem_representationWeightSpace (ρ : MatrixRepresentation H n)
    (τ : MatrixRepresentation H m) {α β : characterLattice p.torus} {v : n → F} {w : m → F}
    (hv : v ∈ p.representationWeightSpace ρ α) (hw : w ∈ p.representationWeightSpace τ β) :
    (fun ij : n × m => v ij.1 * w ij.2) ∈ p.representationWeightSpace (ρ.tensor τ) (α + β) := by
  let := p.isSplitTorus.isAffineHom
  change _ ∈ ((ρ.tensor τ).restrict p.inclusion).characterSpace
    ((rationalCharacters.equivCharacterLattice p.torus).symm (α + β))
  change v ∈ (ρ.restrict p.inclusion).characterSpace
    ((rationalCharacters.equivCharacterLattice p.torus).symm α) at hv
  change w ∈ (τ.restrict p.inclusion).characterSpace
    ((rationalCharacters.equivCharacterLattice p.torus).symm β) at hw
  rw [← MatrixRepresentation.tensor_restrict, map_add]
  apply (MatrixRepresentation.mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  have h1 := MatrixRepresentation.characterSpace_affine hv A x
  have h2 := MatrixRepresentation.characterSpace_affine hw A x
  rw [rationalCharacters.comp_add, map_mul, Units.val_mul]
  funext ij
  obtain ⟨i, j⟩ := ij
  have e1 := congrFun h1 i
  have e2 := congrFun h2 j
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  rw [Fintype.sum_prod_type]
  have key : ∀ k l, ((ρ.restrict p.inclusion).tensor (τ.restrict p.inclusion)).affineMatrix A x
      (i, j) (k, l) = (ρ.restrict p.inclusion).affineMatrix A x i k *
        (τ.restrict p.inclusion).affineMatrix A x j l := fun k l =>
    MatrixRepresentation.tensor_affineMatrix_entry _ _ _ _ i k j l
  rw [map_mul (algebraMap F A) (v i) (w j), mul_mul_mul_comm, ← e1, ← e2, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [key]
  simp only [map_mul]
  ring

/-- An independent family of submodules that contains a spanning family termwise equals it. -/
theorem _root_.iSupIndep.eq_of_le_of_iSup_eq_top {R M J : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {W U : J → Submodule R M} (hW : iSupIndep W) (hUW : ∀ i, U i ≤ W i)
    (hU : ⨆ i, U i = ⊤) (i : J) : W i = U i := by
  refine le_antisymm ?_ (hUW i)
  have hX : (⨆ (j) (_ : j ≠ i), U j) ≤ ⨆ (j) (_ : j ≠ i), W j :=
    iSup₂_mono fun j _ => hUW j
  calc W i = (U i ⊔ ⨆ (j) (_ : j ≠ i), U j) ⊓ W i := by
        rw [← iSup_split_single, hU, top_inf_eq]
    _ = U i ⊔ (⨆ (j) (_ : j ≠ i), U j) ⊓ W i := sup_inf_assoc_of_le _ (hUW i)
    _ ≤ U i := by
        have hd := (iSupIndep_def.mp hW i).symm.mono_left hX
        rw [hd.eq_bot, sup_bot_eq]

/-- The span of tensor products of weight vectors of weights `α` and `β`. -/
def tensorWeightSpan (ρ : MatrixRepresentation H n) (τ : MatrixRepresentation H m)
    (α β : characterLattice p.torus) : Submodule F (n × m → F) :=
  Submodule.span F (Set.image2 (fun (v : n → F) (w : m → F) (ij : n × m) => v ij.1 * w ij.2)
    (p.representationWeightSpace ρ α) (p.representationWeightSpace τ β))

theorem tensorWeightSpan_le (ρ : MatrixRepresentation H n) (τ : MatrixRepresentation H m)
    (α β : characterLattice p.torus) :
    p.tensorWeightSpan ρ τ α β ≤ p.representationWeightSpace (ρ.tensor τ) (α + β) := by
  rw [tensorWeightSpan, Submodule.span_le]
  rintro _ ⟨v, hv, w, hw, rfl⟩
  exact p.kronecker_mem_representationWeightSpace ρ τ hv hw

/-- `v ⊗ w` as a linear map in `v`. -/
def kroneckerRightVec (w : m → F) : (n → F) →ₗ[F] (n × m → F) where
  toFun v ij := v ij.1 * w ij.2
  map_add' v v' := by funext ij; simp [add_mul]
  map_smul' c v := by funext ij; simp [mul_assoc]

/-- `v ⊗ w` as a linear map in `w`. -/
def kroneckerLeftVec (v : n → F) : (m → F) →ₗ[F] (n × m → F) where
  toFun w ij := v ij.1 * w ij.2
  map_add' w w' := by funext ij; simp [mul_add]
  map_smul' c w := by
    funext ij
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The tensor weight spans of all pairs of weights span the tensor product. -/
theorem iSup_tensorWeightSpan (ρ : MatrixRepresentation H n) (τ : MatrixRepresentation H m) :
    (⨆ ab : characterLattice p.torus × characterLattice p.torus,
      p.tensorWeightSpan ρ τ ab.1 ab.2) = ⊤ := by
  classical
  set S := ⨆ ab : characterLattice p.torus × characterLattice p.torus,
    p.tensorWeightSpan ρ τ ab.1 ab.2
  have hpair : ∀ α β, ∀ v ∈ p.representationWeightSpace ρ α,
      ∀ w ∈ p.representationWeightSpace τ β, (fun ij : n × m => v ij.1 * w ij.2) ∈ S := by
    intro α β v hv w hw
    exact (le_iSup (fun ab : characterLattice p.torus × characterLattice p.torus =>
      p.tensorWeightSpan ρ τ ab.1 ab.2) (α, β)) (Submodule.subset_span ⟨v, hv, w, hw, rfl⟩)
  have hw : ∀ β, ∀ w ∈ p.representationWeightSpace τ β, ∀ v : n → F,
      (fun ij : n × m => v ij.1 * w ij.2) ∈ S := by
    intro β w hw v
    have hle : (⨆ α, p.representationWeightSpace ρ α) ≤ S.comap (kroneckerRightVec w) :=
      iSup_le fun α v hv => hpair α β v hv w hw
    rw [p.iSup_representationWeightSpace_eq_top ρ] at hle
    exact hle Submodule.mem_top
  have hall : ∀ (v : n → F) (w : m → F), (fun ij : n × m => v ij.1 * w ij.2) ∈ S := by
    intro v w
    have hle : (⨆ β, p.representationWeightSpace τ β) ≤ S.comap (kroneckerLeftVec v) :=
      iSup_le fun β w hw' => hw β w hw' v
    rw [p.iSup_representationWeightSpace_eq_top τ] at hle
    exact hle Submodule.mem_top
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ ij : n × m, x ij • (fun kl : n × m =>
      (Pi.single ij.1 (1 : F) : n → F) kl.1 * (Pi.single ij.2 (1 : F) : m → F) kl.2) := by
    funext kl
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single kl]
    · simp
    · intro ij _ hij
      by_cases h1 : kl.1 = ij.1
      · have h2 : kl.2 ≠ ij.2 := fun h2 => hij (Prod.ext h1.symm h2.symm)
        simp [Pi.single_apply, h2]
      · simp [Pi.single_apply, h1]
    · simp
  rw [hx]
  exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (hall _ _)

/-- The weight spaces of a tensor product are the spans of tensor products of weight vectors
with weights adding up. -/
theorem representationWeightSpace_tensor (ρ : MatrixRepresentation H n)
    (τ : MatrixRepresentation H m) (nu : characterLattice p.torus) :
    p.representationWeightSpace (ρ.tensor τ) nu =
      ⨆ (ab : characterLattice p.torus × characterLattice p.torus) (_ : ab.1 + ab.2 = nu),
        p.tensorWeightSpan ρ τ ab.1 ab.2 := by
  refine (iSupIndep_representationWeightSpace (p := p) (ρ.tensor τ)).eq_of_le_of_iSup_eq_top
    (U := fun nu => ⨆ (ab : characterLattice p.torus × characterLattice p.torus)
      (_ : ab.1 + ab.2 = nu), p.tensorWeightSpan ρ τ ab.1 ab.2) ?_ ?_ nu
  · intro nu
    refine iSup₂_le fun ab hab => ?_
    rw [← hab]
    exact p.tensorWeightSpan_le ρ τ ab.1 ab.2
  · refine eq_top_iff.mpr (le_of_eq_of_le (p.iSup_tensorWeightSpan ρ τ).symm ?_)
    refine iSup_le fun ab => ?_
    let U : characterLattice p.torus → Submodule F (n × m → F) := fun nu =>
      ⨆ (ab : characterLattice p.torus × characterLattice p.torus) (_ : ab.1 + ab.2 = nu),
        p.tensorWeightSpan ρ τ ab.1 ab.2
    have h1 : p.tensorWeightSpan ρ τ ab.1 ab.2 ≤ U (ab.1 + ab.2) :=
      le_iSup₂ (f := fun (ab' : characterLattice p.torus × characterLattice p.torus)
        (_ : ab'.1 + ab'.2 = ab.1 + ab.2) => p.tensorWeightSpan ρ τ ab'.1 ab'.2) ab rfl
    exact h1.trans (le_iSup U (ab.1 + ab.2))

theorem tensorWeightSpan_eq_bot_left (ρ : MatrixRepresentation H n)
    (τ : MatrixRepresentation H m) {α β : characterLattice p.torus}
    (h : p.representationWeightSpace ρ α = ⊥) : p.tensorWeightSpan ρ τ α β = ⊥ := by
  rw [eq_bot_iff, tensorWeightSpan, Submodule.span_le]
  rintro _ ⟨v, hv, w, -, rfl⟩
  rw [h, SetLike.mem_coe, Submodule.mem_bot] at hv
  subst hv
  rw [SetLike.mem_coe, Submodule.mem_bot]
  funext ij
  simp

theorem tensorWeightSpan_eq_bot_right (ρ : MatrixRepresentation H n)
    (τ : MatrixRepresentation H m) {α β : characterLattice p.torus}
    (h : p.representationWeightSpace τ β = ⊥) : p.tensorWeightSpan ρ τ α β = ⊥ := by
  rw [eq_bot_iff, tensorWeightSpan, Submodule.span_le]
  rintro _ ⟨v, -, w, hw, rfl⟩
  rw [h, SetLike.mem_coe, Submodule.mem_bot] at hw
  subst hw
  rw [SetLike.mem_coe, Submodule.mem_bot]
  funext ij
  simp

variable {ρ : MatrixRepresentation H n} {τ : MatrixRepresentation H m}
  {lam mu : characterLattice p.torus}

/-- Only the pair of highest weights contributes to the sum of the highest weights. -/
theorem tensorWeightSpan_eq_bot_of_ne (hρ : p.IsHighestWeight ρ lam)
    (hτ : p.IsHighestWeight τ mu) {α β : characterLattice p.torus} (h : α + β = lam + mu)
    (hne : (α, β) ≠ (lam, mu)) : p.tensorWeightSpan ρ τ α β = ⊥ := by
  by_cases hα : p.representationWeightSpace ρ α = ⊥
  · exact p.tensorWeightSpan_eq_bot_left ρ τ hα
  by_cases hβ : p.representationWeightSpace τ β = ⊥
  · exact p.tensorWeightSpan_eq_bot_right ρ τ hβ
  obtain ⟨h1, h2⟩ := p.eq_of_add_eq_of_sub_mem (hρ.2.2.2 α hα) (hτ.2.2.2 β hβ) h
  exact absurd (Prod.ext h1 h2) hne

theorem representationWeightSpace_tensor_add (hρ : p.IsHighestWeight ρ lam)
    (hτ : p.IsHighestWeight τ mu) :
    p.representationWeightSpace (ρ.tensor τ) (lam + mu) = p.tensorWeightSpan ρ τ lam mu := by
  rw [representationWeightSpace_tensor]
  apply le_antisymm
  · refine iSup₂_le fun ab hab => ?_
    by_cases hab' : ab = (lam, mu)
    · subst hab'
      exact le_rfl
    · rw [p.tensorWeightSpan_eq_bot_of_ne hρ hτ hab (by simpa using hab')]
      exact bot_le
  · exact le_iSup₂ (f := fun (ab : characterLattice p.torus × characterLattice p.torus)
      (_ : ab.1 + ab.2 = lam + mu) => p.tensorWeightSpan ρ τ ab.1 ab.2) (lam, mu) rfl

/-- The sum of the highest weights has multiplicity one in the tensor product. -/
theorem finrank_representationWeightSpace_tensor_add (hρ : p.IsHighestWeight ρ lam)
    (hτ : p.IsHighestWeight τ mu) :
    Module.finrank F (p.representationWeightSpace (ρ.tensor τ) (lam + mu)) = 1 := by
  obtain ⟨v₀, hv₀, hv⟩ := finrank_eq_one_iff'.mp hρ.2.2.1
  obtain ⟨w₀, hw₀, hw⟩ := finrank_eq_one_iff'.mp hτ.2.2.1
  set x : n × m → F := fun ij => (v₀ : n → F) ij.1 * (w₀ : m → F) ij.2 with hx
  have hx0 : x ≠ 0 := by
    have hv₀' : (v₀ : n → F) ≠ 0 := fun h => hv₀ (Subtype.ext h)
    have hw₀' : (w₀ : m → F) ≠ 0 := fun h => hw₀ (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv₀'
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw₀'
    intro h
    have := congrFun h (i, j)
    simp only [hx, Pi.zero_apply, mul_eq_zero] at this hi hj
    tauto
  have heq : p.tensorWeightSpan ρ τ lam mu = F ∙ x := by
    apply le_antisymm
    · rw [tensorWeightSpan, Submodule.span_le]
      rintro _ ⟨v, hvm, w, hwm, rfl⟩
      obtain ⟨c, hc⟩ := hv ⟨v, hvm⟩
      obtain ⟨d, hd⟩ := hw ⟨w, hwm⟩
      have hc' : v = c • (v₀ : n → F) := (congrArg Subtype.val hc).symm
      have hd' : w = d • (w₀ : m → F) := (congrArg Subtype.val hd).symm
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c * d, ?_⟩
      funext ij
      simp only [hx, hc', hd', Pi.smul_apply, smul_eq_mul]
      ring
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨v₀, v₀.2, w₀, w₀.2, rfl⟩
  rw [p.representationWeightSpace_tensor_add hρ hτ, heq, finrank_span_singleton hx0]

/-- Every weight of the tensor product lies below the sum of the highest weights. -/
theorem sub_mem_positiveRootMonoid_tensor (hρ : p.IsHighestWeight ρ lam)
    (hτ : p.IsHighestWeight τ mu) (nu : characterLattice p.torus)
    (hnu : p.representationWeightSpace (ρ.tensor τ) nu ≠ ⊥) :
    lam + mu - nu ∈ p.positiveRootMonoid := by
  by_contra hcon
  apply hnu
  rw [representationWeightSpace_tensor, eq_bot_iff]
  refine iSup₂_le fun ab hab => ?_
  by_cases hα : p.representationWeightSpace ρ ab.1 = ⊥
  · rw [p.tensorWeightSpan_eq_bot_left ρ τ hα]
  by_cases hβ : p.representationWeightSpace τ ab.2 = ⊥
  · rw [p.tensorWeightSpan_eq_bot_right ρ τ hβ]
  exfalso
  apply hcon
  have := add_mem (hρ.2.2.2 ab.1 hα) (hτ.2.2.2 ab.2 hβ)
  rwa [show lam - ab.1 + (mu - ab.2) = lam + mu - (ab.1 + ab.2) by abel, hab] at this

end Langlands.GroupScheme.SplitPinning
