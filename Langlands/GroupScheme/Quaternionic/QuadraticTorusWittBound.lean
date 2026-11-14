import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities
import Langlands.GroupScheme.Quaternionic.QuadraticValueExt
import Langlands.GroupScheme.Torus.FiniteAlgebraWeightIdempotents
import Langlands.GroupScheme.Torus.HermitianWeightIsotropy
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Split tori in the quaternionic isometry group are bounded by the Witt index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MatrixNormOneSplitRank (coeffTensor coeffTensor_tmul)

namespace QuadraticTorusWittBound

/-! ### Coefficients of Laurent tensors -/

section Coefficients

variable {K A Λ : Type u} [Field K] [Ring A] [Algebra K A] [AddCommMonoid Λ]

/-- Taking a coefficient maps the scalar extension of a subspace into the subspace. -/
theorem coeffTensor_mem_of_mem_baseChange (M : Submodule K A) (m : Λ)
    {z : AddMonoidAlgebra K Λ ⊗[K] A} (hz : z ∈ M.baseChange (AddMonoidAlgebra K Λ)) :
    coeffTensor A m z ∈ M := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul p x =>
    rw [LinearMap.baseChange_tmul, coeffTensor_tmul]
    exact M.smul_mem _ x.2
  | add w w' hw hw' =>
    rw [map_add, map_add]
    exact M.add_mem hw hw'

variable [DecidableEq Λ] (τ : FirstKindInvolution K A) (Q : A)

/-- The constant coefficient of the defect of a Laurent element `∑ₘ Xᵐ ⊗ eₘ`. -/
theorem coeffTensor_zero_defect_sum (s : Finset Λ) (e : Λ → A) :
    coeffTensor A 0 (IsometryCut.defect τ Q
      (∑ m ∈ s, AddMonoidAlgebra.single m (1 : K) ⊗ₜ[K] e m)) =
    (∑ m ∈ s, ∑ p ∈ s, if m + p = 0 then e m * Q * τ (e p) else 0) - Q := by
  simp only [IsometryCut.defect, FirstKindInvolution.baseChange_tmul,
    Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    AddMonoidAlgebra.single_mul_single, mul_one, map_sub, map_sum, coeffTensor_tmul,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
    AddMonoidAlgebra.coeff_one_zero]
  rw [Finset.sum_comm]

end Coefficients

/-! ### Sandwiching by a sum of weight idempotents -/

section Sandwich

variable {K A : Type u} [Field K] [Ring A] [Algebra K A] (τ : FirstKindInvolution K A)

/-- Conjugation `z ↦ a z τ(a)` preserves the alternating subspace `{x - τ x}`. -/
theorem sandwich_mem_alternatingSubspace (a : A) {z : A}
    (hz : z ∈ τ.alternatingSubspace) : a * z * τ a ∈ τ.alternatingSubspace := by
  obtain ⟨c, rfl⟩ := τ.mem_alternatingSubspace.mp hz
  apply τ.mem_alternatingSubspace.mpr
  refine ⟨a * c * τ a, ?_⟩
  simp only [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply]
  noncomm_ring

variable {Λ : Type u} [AddCommMonoid Λ] [DecidableEq Λ]

/-- Let `e` be a family of orthogonal idempotents, `S` a finite set of indices no two of which
(possibly equal) add up to `0`, and `f = ∑_{p ∈ S} eₚ`. Sandwiching
`∑_{m + p = 0} eₘ Q τ(eₚ) - Q` between `f` and `τ(f)` leaves `-f Q τ(f)`. -/
theorem sandwich_coefficient (Q : A) (s S : Finset Λ) (e : Λ → A)
    (he : ∀ m p, e m * e p = if m = p then e m else 0)
    (hS : ∀ m ∈ S, ∀ p ∈ S, m + p ≠ 0) :
    (∑ p ∈ S, e p) * ((∑ m ∈ s, ∑ p ∈ s, if m + p = 0 then e m * Q * τ (e p) else 0) - Q) *
        τ (∑ p ∈ S, e p) =
      -((∑ p ∈ S, e p) * Q * τ (∑ p ∈ S, e p)) := by
  set f := ∑ p ∈ S, e p
  have hf : ∀ m, f * e m = if m ∈ S then e m else 0 := by
    intro m
    simp only [f, Finset.sum_mul, he, Finset.sum_ite_eq']
  have hterm : ∀ m p, f * (if m + p = 0 then e m * Q * τ (e p) else 0) * τ f = 0 := by
    intro m p
    split_ifs with hmp
    · have h1 : f * (e m * Q * τ (e p)) * τ f = (f * e m) * Q * τ (f * e p) := by
        simp only [FirstKindInvolution.map_mul, mul_assoc]
      rw [h1, hf, hf]
      by_cases hm : m ∈ S
      · by_cases hp : p ∈ S
        · exact absurd hmp (hS m hm p hp)
        · simp [hp]
      · simp [hm]
    · simp
  rw [mul_sub, sub_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, hterm, Finset.sum_const_zero, zero_sub]

end Sandwich

/-! ### Singular subspaces from idempotents -/

section Vectors

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- If `f Q τ(f)` lies in Tits's subspace `{x - ᵗx^σ}`, then every row vector fixed by `f` is
singular for `q`. -/
theorem quadraticValue_eq_zero_of_vecMul_eq (q : σ.QuadraticForms n) (f : Matrix n n D)
    (hf : f * Quotient.out q * σ.matrix n f ∈ σ.quadraticKernel n) {x : n → D}
    (hx : x ᵥ* f = x) : σ.quadraticValue x q = 0 := by
  have hq : (Submodule.Quotient.mk (Quotient.out q) : σ.QuadraticForms n) = q :=
    Submodule.Quotient.mk_out q
  have h0 : (Submodule.Quotient.mk (f * Quotient.out q * σ.matrix n f) :
      σ.QuadraticForms n) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hf
  rw [← hq, FirstKindInvolution.quadraticValue_mk, ← hx, ← σ.sesqForm_congruence,
    ← FirstKindInvolution.quadraticValue_mk, h0, map_zero]

/-- A family of orthogonal idempotent matrices `e`, nonzero on a finite set `S`, with
`f Q τ(f) ∈ {x - ᵗx^σ}` for `f = ∑_{p ∈ S} eₚ`, gives a totally singular subspace of dimension
`|S|`; hence `|S|` is at most the Witt index. -/
theorem card_le_quadraticWittIndex_of_idempotents (q : σ.QuadraticForms n) {ι : Type*}
    [DecidableEq ι] (S : Finset ι) (e : ι → Matrix n n D)
    (he : ∀ m p, e m * e p = if m = p then e m else 0)
    (hne : ∀ m ∈ S, e m ≠ 0)
    (hf : (∑ p ∈ S, e p) * Quotient.out q * σ.matrix n (∑ p ∈ S, e p) ∈
      σ.quadraticKernel n) :
    S.card ≤ σ.quadraticWittIndex q := by
  classical
  have hrow : ∀ m : S, ∃ r, e m r ≠ 0 := by
    intro m
    by_contra h
    exact hne m m.2 (funext fun r => not_not.mp fun hr => h ⟨r, hr⟩)
  choose r hr using hrow
  let w : S → n → D := fun m => e m (r m)
  have hw : ∀ (m : S) p, w m ᵥ* e p = if (m : ι) = p then w m else 0 := by
    intro m p
    have h : w m ᵥ* e p = (e m * e p) (r m) := by
      funext c
      simp only [w, Matrix.vecMul, Matrix.mul_apply, dotProduct]
    rw [h, he]
    split_ifs <;> rfl
  have hli : LinearIndependent D w := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have h2 : ∑ j ∈ t, g j • (w j ᵥ* e i) = g i • w i := by
      rw [Finset.sum_eq_single i]
      · rw [hw]; simp
      · intro j _ hji
        rw [hw, ite_eq_right (fun h => hji (Subtype.ext h)), smul_zero]
      · intro hi'
        exact absurd hi hi'
    have h3 : (∑ j ∈ t, g j • w j) ᵥ* e i = ∑ j ∈ t, g j • (w j ᵥ* e i) := by
      rw [Matrix.sum_vecMul]
      simp only [Matrix.smul_vecMul]
    rw [hg, Matrix.zero_vecMul, h2] at h3
    exact (smul_eq_zero.mp h3.symm).resolve_right (hr i)
  let W := Submodule.span D (Set.range w)
  have hdim : Module.finrank D W = S.card := by
    rw [finrank_span_eq_card hli, Fintype.card_coe]
  have hfix : ∀ x ∈ W, x ᵥ* (∑ p ∈ S, e p) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [Matrix.vecMul_sum, Finset.sum_congr rfl (fun p _ => hw m p), Finset.sum_ite_eq,
        ite_eq_left m.2]
    | zero => exact Matrix.zero_vecMul _
    | add x y _ _ hx hy => rw [Matrix.add_vecMul, hx, hy]
    | smul a x _ hx => rw [Matrix.smul_vecMul, hx]
  have hsing : σ.IsTotallySingular q W := fun x hx =>
    quadraticValue_eq_zero_of_vecMul_eq σ q _ hf (hfix x hx)
  rw [← hdim]
  exact hsing.finrank_le_quadraticWittIndex

end Vectors

/-! ### Split tori in the isometry group -/

section Torus

open FiniteAlgebraUnits FiniteAlgebraTorusWeights SplitTorusRepresentationWeights

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-- Every point of `O(q)` with values in a commutative `K`-algebra `R` is a unit of
`R ⊗[K] M_n(D)` whose defect `u Q ᵗu^σ - Q` lies in `R ⊗ {x - ᵗx^σ}`. -/
theorem defect_affinePoint_mem (q : σ.QuadraticForms n) (R : CommAlgCat.{u} (CommRingCat.of K))
    (z : (σ.isometryGroup q).affinePoints R) :
    IsometryCut.defect (σ.matrix n) (Quotient.out q)
      (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
        (z ≫ (σ.isometryGroupι q).hom.hom) : R ⊗[K] Matrix n n D) ∈
      (σ.quadraticKernel n).baseChange R := by
  let hI := IsometryCut.isCutOutBy
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
  have h : FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R
        (z ≫ (σ.isometryGroupι q).hom.hom) =
      (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI) R z).val := by
    change Corepresented.affinePointsEquiv _ (FiniteAlgebraUnits.corepresentableBy
      (Module.finBasis K (Matrix n n D))) R (z ≫ (Corepresented.cutHom hI).hom.hom) = _
    rw [Corepresented.cutHom, Corepresented.groupSchemeMap_affinePoints]
    rfl
  rw [h]
  exact (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI) R z).2

/-- **Witt-index bound for split tori.** If `𝔾ₘ^I → O(q)` is a split torus whose composite
with the inclusion into the unit group of `M_n(D)` is a monomorphism, then `|I|` is at most the
Witt index of `q`. No nondegeneracy and no infinitude of `K` is needed. -/
theorem card_le_quadraticWittIndex_of_mono (q : σ.QuadraticForms n)
    {I : Type u} [Fintype I] [DecidableEq I]
    (t : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (ht : Mono (t ≫ σ.isometryGroupι q).hom.hom.left) :
    Fintype.card I ≤ σ.quadraticWittIndex q := by
  classical
  set j := t ≫ σ.isometryGroupι q with hj
  set supp := weightSupport (rightRegularRepresentation (Module.finBasis K (Matrix n n D))) I j
  have hu : IsometryCut.defect (σ.matrix n) (Quotient.out q)
      ((universalUnit j : (AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D)ˣ) :
        AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix n n D) ∈
      (σ.quadraticKernel n).baseChange (AddMonoidAlgebra K (I → ℤ)) := by
    have h := defect_affinePoint_mem σ q
      (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K (I → ℤ)))
      (splitTorus.universalPoint (R := CommRingCat.of K) I ≫ t.hom.hom)
    rw [Category.assoc] at h
    exact h
  have hv := (IsometryCut.isometrySubgroup
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
    (AddMonoidAlgebra K (I → ℤ))).inv_mem (x := universalUnit j) hu
  rw [IsometryCut.mem_isometrySubgroup, universalUnit_inv_eq_sum] at hv
  have hc := coeffTensor_mem_of_mem_baseChange _ 0 hv
  rw [coeffTensor_zero_defect_sum] at hc
  obtain ⟨s', hs', hcover⟩ := HermitianWeights.exists_nonopposite_subfamily
    (fun m : supp => (m : I → ℤ))
  have hcard := HermitianWeights.card_le_of_generators_up_to_sign
    (fun m : supp => (m : I → ℤ)) (by
      have h := closure_weightSupport j ht
      convert h using 2
      ext m
      simp [supp]) s' hcover
  let S : Finset (I → ℤ) := s'.map (Function.Embedding.subtype _)
  have hS : ∀ m ∈ S, ∀ p ∈ S, m + p ≠ 0 := by
    intro m hm p hp
    obtain ⟨m', hm', rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
    exact hs' m' hm' p' hp'
  have hSsupp : ∀ m ∈ S, m ∈ supp := by
    intro m hm
    obtain ⟨m', _, rfl⟩ := Finset.mem_map.mp hm
    exact m'.2
  have hf := sandwich_mem_alternatingSubspace (σ.matrix n) (∑ p ∈ S, weightElement j p) hc
  rw [sandwich_coefficient (σ.matrix n) _ _ S _ (weightElement_mul j) hS] at hf
  have hf' := (σ.quadraticKernel n).neg_mem hf
  rw [neg_neg] at hf'
  have hbound := card_le_quadraticWittIndex_of_idempotents σ q S (weightElement j)
    (weightElement_mul j) (fun m hm => weightElement_ne_zero j (hSsupp m hm)) hf'
  rw [Finset.card_map] at hbound
  exact hcard.trans hbound

/-- The split rank of `O(q)` is at most the Witt index of `q`. -/
theorem splitRank_isometryGroup_le (q : σ.QuadraticForms n) :
    splitRank (σ.isometryGroup q) ≤ (σ.quadraticWittIndex q : ℕ∞) := by
  unfold splitRank
  refine iSup_le fun I => iSup_le fun hI => iSup_le fun t => iSup_le fun ht => ?_
  classical
  let : Fintype I := Fintype.ofFinite I
  set i := (σ.isometryGroupι q).hom.hom
  have h1c : IsClosedImmersion t.hom.hom.left := ht
  have h2c : IsClosedImmersion i.left := σ.isClosedSubgroup_isometryGroupι q
  have h1 : Mono t.hom.hom.left := (IsClosedImmersion.iff_isFinite_and_mono _).mp h1c |>.2
  have h2 : Mono i.left := (IsClosedImmersion.iff_isFinite_and_mono _).mp h2c |>.2
  have hmono : Mono (t ≫ σ.isometryGroupι q).hom.hom.left := by
    change Mono (t.hom.hom.left ≫ i.left)
    exact mono_comp _ _
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast card_le_quadraticWittIndex_of_mono σ q t hmono

/-- The split rank of `O(q)⁰` is at most the Witt index of `q`. -/
theorem splitRank_connectedIsometryGroup_le (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom] :
    splitRank (σ.connectedIsometryGroup q) ≤ (σ.quadraticWittIndex q : ℕ∞) :=
  (splitRank_le_of_isClosedSubgroup (identityComponentι _)
    (IdentityComponent.isClosedSubgroup_identityComponentι _)).trans
    (splitRank_isometryGroup_le σ q)

end Torus

end QuadraticTorusWittBound

end Langlands.GroupScheme.Quaternionic
