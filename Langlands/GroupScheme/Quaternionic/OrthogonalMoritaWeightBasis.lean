import Langlands.GroupScheme.Quaternionic.CocharacterWeightBasis
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentation
import Mathlib.LinearAlgebra.StdBasis

/-! # Multiplicity counts from a supplied orthogonal Morita weight basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {m : Type} [Fintype m] [DecidableEq m]
  (q : σ.QuadraticForms m)
  (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)

/-- Cancel the repeated-copy factor in a homogeneous extended basis. -/
theorem cocharacterWeightBasis_card_copies
    (L : Type u) [Field L] [Algebra K L]
    (degree : ℕ) (hdegree : 0 < degree)
    (hdim : finrank K D = degree ^ 2)
    {I : Type*} [Fintype I]
    (b : Basis (Fin degree × I) L (L ⊗[K] (m → D))) (w : I → ℤ)
    (hb : ∀ p, b p ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w p.2)) (c : ℤ) :
    Nat.card {i // w i = c} =
      degree * finrank D (σ.cocharacterWeightSpace q f c) := by
  let e : {p : Fin degree × I // w p.2 = c} ≃
      Fin degree × {i // w i = c} :=
    { toFun := fun p => (p.val.1, ⟨p.val.2, p.property⟩)
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card {p : Fin degree × I // w p.2 = c} =
      degree * Nat.card {i // w i = c} := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_fin]
  have h := σ.cocharacterWeightBasis_card q f L b (fun p => w p.2) hb c
  rw [hcard, hdim] at h
  apply Nat.mul_left_cancel hdegree
  simpa only [pow_two, Nat.mul_assoc] using h

end FirstKindInvolution

namespace OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Field L] [Algebra K L]
  {σ : FirstKindInvolution K D} {m n degree : ℕ}
  {q : σ.QuadraticForms (Fin m)}

/-- Pull back the direct product of copies of a split row basis through the
supplied Morita row equivalence. -/
def rowBasis (e : OrthogonalMoritaComparison σ q L degree n)
    {I : Type*} (b : Basis I L ((Fin n ⊕ Fin n) → L)) :
    Basis (Fin degree × I) L (L ⊗[K] (Fin m → D)) :=
  ((Pi.basis (fun _ : Fin degree => b)).reindex
    (Equiv.sigmaEquivProd (Fin degree) I)).map e.rowEquiv.symm

/-- Each pulled-back vector occupies exactly its designated copy. -/
theorem rowEquiv_rowBasis (e : OrthogonalMoritaComparison σ q L degree n)
    {I : Type*} (b : Basis I L ((Fin n ⊕ Fin n) → L))
    (p : Fin degree × I) :
    e.rowEquiv (rowBasis e b p) = Pi.single p.1 (b p.2) := by
  classical
  simp [rowBasis]

/-- A homogeneous Morita copy basis gives the original division-algebra
weight multiplicity after cancelling one positive degree factor. -/
theorem weight_card_of_rowBasis
    (e : OrthogonalMoritaComparison σ q L degree n)
    (hdegree : 0 < degree) (hdim : finrank K D = degree ^ 2)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    {I : Type*} [Fintype I] (b : Basis I L ((Fin n ⊕ Fin n) → L)) (w : I → ℤ)
    (hb : ∀ p, rowBasis e b p ∈ σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) (w p.2)) (c : ℤ) :
    Nat.card {i // w i = c} =
      degree * finrank D (σ.cocharacterWeightSpace q f c) :=
  σ.cocharacterWeightBasis_card_copies q f L degree hdegree hdim
    (rowBasis e b) w hb c

end OrthogonalMorita

end Langlands.GroupScheme.Quaternionic
