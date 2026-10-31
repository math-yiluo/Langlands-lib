import Langlands.Algebra.FilteredSymmetricAlgebraSymmetrization
import Mathlib.Algebra.Algebra.Bilinear

/-! # Separated symmetrization spans the genuine enveloping algebra -/

noncomputable section
universe v w
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]
variable {P : Type w} [AddCommGroup P] [Module R P]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The symmetric-algebra map induced by an arbitrary linear family of Lie vectors. -/
def symmetricLinearLift (f : P →ₗ[R] L) :
    SymmetricAlgebra R P →ₐ[R] SymmetricAlgebra R L :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R L).comp f)

@[simp] theorem symmetricLinearLift_ι (f : P →ₗ[R] L) (x : P) :
    symmetricLinearLift R L f (SymmetricAlgebra.ι R P x) =
      SymmetricAlgebra.ι R L (f x) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Symmetrization restricted along an arbitrary linear family of Lie vectors. -/
def linearFamilySymmetrize (f : P →ₗ[R] L) : SymmetricAlgebra R P →ₗ[R] U :=
  (symmetricAlgebraSymmetrize R L).comp (symmetricLinearLift R L f).toLinearMap

/-- Multiply a symmetrized first factor by an element of a prescribed right subalgebra. -/
def separatedSymmetrization (f : P →ₗ[R] L) (B : Subalgebra R U) :
    SymmetricAlgebra R P ⊗[R] B →ₗ[R] U :=
  (LinearMap.mul' R U).comp
    (TensorProduct.map (linearFamilySymmetrize R L f) B.val.toLinearMap)

@[simp] theorem separatedSymmetrization_tmul (f : P →ₗ[R] L) (B : Subalgebra R U)
    (a : SymmetricAlgebra R P) (b : B) :
    separatedSymmetrization R L f B (a ⊗ₜ[R] b) =
      linearFamilySymmetrize R L f a * b.val := rfl

private theorem separated_product_mem_range (f : P →ₗ[R] L) (B : Subalgebra R U)
    (l r : List L) (hl : ∀ x ∈ l, x ∈ LinearMap.range f)
    (hr : ∀ x ∈ r, UniversalEnvelopingAlgebra.ι R x ∈ B) :
    symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) *
      word R L r ∈ LinearMap.range (separatedSymmetrization R L f B) := by
  have hleft :
      (l.map (SymmetricAlgebra.ι R L)).prod ∈ (symmetricLinearLift R L f).range := by
    apply Subalgebra.list_prod_mem
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨p, hp⟩ := hl x hx
    refine ⟨SymmetricAlgebra.ι R P p, ?_⟩
    change symmetricLinearLift R L f (SymmetricAlgebra.ι R P p) =
      SymmetricAlgebra.ι R L x
    simp only [symmetricLinearLift_ι, hp]
  obtain ⟨a, ha⟩ := hleft
  change symmetricLinearLift R L f a =
    (l.map (SymmetricAlgebra.ι R L)).prod at ha
  have hright : word R L r ∈ B := by
    apply Subalgebra.list_prod_mem
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hr x hx
  refine ⟨a ⊗ₜ[R] (⟨word R L r, hright⟩ : B), ?_⟩
  simp only [separatedSymmetrization_tmul, linearFamilySymmetrize,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, ha]

variable [CharZero R]

private theorem colored_word_mem_range (f : P →ₗ[R] L) (B : Subalgebra R U)
    {d : ℕ} (hlow : degreeFiltration R L d ≤
      LinearMap.range (separatedSymmetrization R L f B))
    (l : List L) (hlen : l.length ≤ d + 1)
    (hcolor : ∀ x ∈ l, x ∈ LinearMap.range f ∨ UniversalEnvelopingAlgebra.ι R x ∈ B) :
    word R L l ∈ LinearMap.range (separatedSymmetrization R L f B) := by
  classical
  let pred : L → Bool := fun x => decide (x ∈ LinearMap.range f)
  let lp := l.filter pred
  let lr := l.filter (fun x => !pred x)
  have hperm : (lp ++ lr).Perm l := List.filter_append_perm pred l
  have hlength : lp.length + lr.length = l.length := by
    simpa only [List.length_append] using hperm.length_eq
  have hp (x : L) (hx : x ∈ lp) : x ∈ LinearMap.range f := by
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  have hr (x : L) (hx : x ∈ lr) : UniversalEnvelopingAlgebra.ι R x ∈ B := by
    obtain ⟨hxl, hnot⟩ := List.mem_filter.mp hx
    have hn : x ∉ LinearMap.range f := by
      intro hx
      have htrue : pred x = true := decide_eq_true_iff.mpr hx
      simp [htrue] at hnot
    exact (hcolor x hxl).resolve_left hn
  have hmain := separated_product_mem_range R L f B lp lr hp hr
  have hpermError :
      word R L l - word R L (lp ++ lr) ∈ degreeFiltration R L (l.length - 1) :=
    word_sub_word_mem_of_perm R L hperm.symm
  have hsymError :
      word R L (lp ++ lr) -
        symmetricAlgebraSymmetrize R L ((lp.map (SymmetricAlgebra.ι R L)).prod) *
          word R L lr ∈ degreeFiltration R L (l.length - 1) := by
    by_cases hp0 : lp = []
    · simp [hp0, word]
    · have hpos : 0 < lp.length := List.length_pos_iff.mpr hp0
      have he := mul_mem_degreeFiltration R L
        (symmetricAlgebraSymmetrize_prod_sub_word_mem R L lp)
        (word_mem_degreeFiltration R L lr)
      have hd : lp.length - 1 + lr.length = l.length - 1 := by omega
      rw [hd] at he
      have heq :
          word R L (lp ++ lr) -
            symmetricAlgebraSymmetrize R L ((lp.map (SymmetricAlgebra.ι R L)).prod) *
              word R L lr =
          -((symmetricAlgebraSymmetrize R L ((lp.map (SymmetricAlgebra.ι R L)).prod) -
              word R L lp) * word R L lr) := by
        simp only [word, List.map_append, List.prod_append]
        noncomm_ring
      rw [heq]
      exact (degreeFiltration R L _).neg_mem he
  have herr :
      word R L l -
        symmetricAlgebraSymmetrize R L ((lp.map (SymmetricAlgebra.ι R L)).prod) *
          word R L lr ∈ degreeFiltration R L d := by
    apply degreeFiltration_mono R L (show l.length - 1 ≤ d by omega)
    simpa only [sub_add_sub_cancel] using
      (degreeFiltration R L _).add_mem hpermError hsymError
  simpa only [sub_add_cancel] using
    (LinearMap.range (separatedSymmetrization R L f B)).add_mem (hlow herr) hmain

/-- If the Lie vectors split into the chosen linear family and directions whose
generators lie in the right subalgebra, separated symmetrization is onto. -/
theorem separatedSymmetrization_surjective (f : P →ₗ[R] L) (B : Subalgebra R U)
    (hsplit : LinearMap.range f ⊔
      B.toSubmodule.comap (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap = ⊤) :
    Function.Surjective (separatedSymmetrization R L f B) := by
  have hdeg (d : ℕ) : degreeFiltration R L d ≤
      LinearMap.range (separatedSymmetrization R L f B) := by
    induction d with
    | zero =>
      intro a ha
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp ha
      refine ⟨algebraMap R (SymmetricAlgebra R P) r ⊗ₜ[R] (1 : B), ?_⟩
      simp [linearFamilySymmetrize]
    | succ d ih =>
      rw [degreeFiltration_eq_envelopingWordSpan]
      apply Submodule.span_le.mpr
      rintro a ⟨l, hl, rfl⟩
      have hsplitAt (i : Fin l.length) :
          ∃ p : P, ∃ y : L, UniversalEnvelopingAlgebra.ι R y ∈ B ∧
            f p + y = l.get i := by
        have hmem : l.get i ∈ LinearMap.range f ⊔
            B.toSubmodule.comap (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap := by
          rw [hsplit]
          trivial
        obtain ⟨x, hx, y, hy, heq⟩ := Submodule.mem_sup.mp hmem
        obtain ⟨p, rfl⟩ := hx
        exact ⟨p, y, hy, heq⟩
      choose p y hy heq using hsplitAt
      have hfn : l.get = (fun i => f (p i)) + y := by
        funext i
        exact (heq i).symm
      have hw : word R L l = orderedWord R L l.length l.get := by simp
      rw [hw, hfn, (orderedWord R L l.length).map_add_univ]
      apply Submodule.sum_mem
      intro s _
      rw [orderedWord_apply]
      apply colored_word_mem_range R L f B ih
      · simpa only [List.length_ofFn] using hl
      · intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        by_cases hi : i ∈ s
        · left
          simp [Finset.piecewise, hi]
        · right
          simpa [Finset.piecewise, hi] using hy i
  intro a
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration R L a
  exact hdeg d hd

end Langlands.Algebra.UniversalEnveloping
