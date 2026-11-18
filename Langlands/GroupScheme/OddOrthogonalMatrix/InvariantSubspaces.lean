import Langlands.GroupScheme.OddOrthogonalMatrix.ShortMatrices
import Langlands.GroupScheme.OrthogonalMatrix.Reductive

/-! # Invariant subspaces of the odd standard column representation -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

/-- Inclusion of the hyperbolic coordinate hyperplane. -/
def evenVector : (l ⊕ l → K) →ₗ[K] (Index l → K) where
  toFun v := Sum.elim 0 v
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

/-- A linear action on the hyperbolic block, fixing the axis coordinate. -/
def evenAction (A : Matrix (l ⊕ l) (l ⊕ l) K) : Matrix (Index l) (Index l) K :=
  Matrix.fromBlocks 1 0 0 A

omit [DecidableEq l] in
/-- Restricting the block action to the hyperbolic hyperplane. -/
theorem evenAction_evenVector (A : Matrix (l ⊕ l) (l ⊕ l) K) (v : l ⊕ l → K) :
    evenAction A *ᵥ evenVector v = evenVector (A *ᵥ v) := by
  ext (i | i) <;> simp [evenAction, evenVector, Matrix.fromBlocks_mulVec]

omit [DecidableEq l] in
/-- Subtracting the identity cancels the axis coordinate of a block action. -/
theorem evenAction_mulVec_sub (A : Matrix (l ⊕ l) (l ⊕ l) K) (v : Index l → K) :
    evenAction A *ᵥ v - v = evenVector (A *ᵥ (v ∘ Sum.inr) - v ∘ Sum.inr) := by
  ext (i | i) <;> simp [evenAction, evenVector, Matrix.fromBlocks_mulVec]

/-- A nonzero subspace stable under the connected even elementary generators
and the signed short families contains every vector of the hyperbolic hyperplane.
In characteristic two this hyperplane can be a proper invariant subspace. -/
theorem evenVector_mem_of_stable [Nontrivial l] (W : Submodule K (Index l → K)) (hW : W ≠ ⊥)
    (hlevi : ∀ g : GL l K, ∀ v ∈ W, evenAction (SymplecticMatrix.levi g) *ᵥ v ∈ W)
    (hupper : ∀ A : Matrix l l K, OrthogonalMatrix.IsAlt A → ∀ v ∈ W,
      evenAction (SymplecticMatrix.upper A) *ᵥ v ∈ W)
    (hlower : ∀ A : Matrix l l K, OrthogonalMatrix.IsAlt A → ∀ v ∈ W,
      evenAction (SymplecticMatrix.lower A) *ᵥ v ∈ W)
    (hshort : ∀ a : l ⊕ l, ∀ v ∈ W, shortMatrix a (1 : K) *ᵥ v ∈ W)
    (w : l ⊕ l → K) : evenVector w ∈ W := by
  let V := W.comap evenVector
  have hV : V ≠ ⊥ := by
    intro hV
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hW
    have hdiff (A : Matrix (l ⊕ l) (l ⊕ l) K)
        (hAv : evenAction A *ᵥ v ∈ W) : A *ᵥ (v ∘ Sum.inr) - v ∘ Sum.inr = 0 := by
      have hd := W.sub_mem hAv hv
      rw [evenAction_mulVec_sub] at hd
      have hz : A *ᵥ (v ∘ Sum.inr) - v ∘ Sum.inr ∈ V := hd
      rw [hV, Submodule.mem_bot] at hz
      exact hz
    have hy (b : l) : v (Sum.inr (Sum.inr b)) = 0 := by
      obtain ⟨a, hab⟩ := exists_ne b
      have he := hdiff (SymplecticMatrix.upper (OrthogonalMatrix.alt K a b))
        (hupper _ (OrthogonalMatrix.isAlt_alt _ _) v hv)
      rw [OrthogonalMatrix.upper_mulVec, add_sub_cancel_left] at he
      have hc := congrFun he (Sum.inl a)
      simpa [OrthogonalMatrix.alt_mulVec_apply_left hab] using hc
    have hx (b : l) : v (Sum.inr (Sum.inl b)) = 0 := by
      obtain ⟨a, hab⟩ := exists_ne b
      have he := hdiff (SymplecticMatrix.lower (OrthogonalMatrix.alt K a b))
        (hlower _ (OrthogonalMatrix.isAlt_alt _ _) v hv)
      rw [OrthogonalMatrix.lower_mulVec, add_sub_cancel_left] at he
      have hc := congrFun he (Sum.inr a)
      simpa [OrthogonalMatrix.alt_mulVec_apply_left hab] using hc
    have heven : ∀ a : l ⊕ l, v (Sum.inr a) = 0 := by
      rintro (a | a)
      · exact hx a
      · exact hy a
    obtain ⟨a⟩ := (inferInstance : Nonempty (l ⊕ l))
    have hd := W.sub_mem (hshort a v hv) hv
    have hformula : shortMatrix a (1 : K) *ᵥ v - v =
        evenVector (Pi.single a.swap (v (Sum.inl ()))) := by
      ext i
      rcases i with i | i
      · cases i
        simp [shortMatrix, Matrix.add_mulVec, Matrix.single_mulVec, evenVector, heven]
      · simp [shortMatrix, Matrix.add_mulVec, Matrix.single_mulVec, evenVector, heven, Pi.single_apply, Function.update_apply]
    rw [hformula] at hd
    have hz : Pi.single a.swap (v (Sum.inl ())) ∈ V := hd
    rw [hV, Submodule.mem_bot] at hz
    have haxis : v (Sum.inl ()) = 0 := by
      simpa using congrFun hz a.swap
    apply hv0
    ext i
    rcases i with i | i
    · cases i; exact haxis
    · exact heven i
  have htop : V = ⊤ := OrthogonalMatrix.eq_top_of_stable V hV
    (fun g v hv => by
      have h := hlevi g (evenVector v) hv
      rwa [evenAction_evenVector] at h)
    (fun A hA v hv => by
      have h := hupper A hA (evenVector v) hv
      rwa [evenAction_evenVector] at h)
    (fun A hA v hv => by
      have h := hlower A hA (evenVector v) hv
      rwa [evenAction_evenVector] at h)
  have hw : w ∈ V := htop ▸ Submodule.mem_top
  exact hw

end Langlands.GroupScheme.OddOrthogonalMatrix
