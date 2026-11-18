import Langlands.GroupScheme.SL2CentralExtension.Torus
import Langlands.GroupScheme.SL2CentralExtension.UnitPairing

/-! # Lifts of diagonal matrices commute when the kernel is separated -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

variable {S : Scheme.{u}}

namespace Ext

variable (X : Ext S) {T : Over S}

/-- The commutator of lifts of two diagonal matrices lies in the kernel of `Q`. -/
theorem Q_comm_h (s t : Γ(T.left, ⊤)ˣ) : X.Q T (X.comm (Mat.h s) (Mat.h t)) = 1 := by
  rw [X.Q_comm, Mat.h_comm, mul_inv_cancel_right, mul_inv_cancel]

/-- The commutator of lifts of diagonal matrices is multiplicative in the first entry. -/
theorem comm_h_mul_left (s s' t : Γ(T.left, ⊤)ˣ) :
    X.comm (Mat.h (s * s')) (Mat.h t) =
      X.comm (Mat.h s) (Mat.h t) * X.comm (Mat.h s') (Mat.h t) := by
  rw [X.comm_eq (e₁ := X.hl s * X.hl s') (e₂ := X.hl t)
      (by rw [map_mul, Q_hl, Q_hl, Mat.h_mul]) (X.Q_hl t),
    X.comm_eq (X.Q_hl s) (X.Q_hl t), X.comm_eq (X.Q_hl s') (X.Q_hl t)]
  exact commutator_mul_left _ _ _
    (X.commutator_central (by rw [Q_hl, Q_hl]; exact Mat.h_comm s' t))

/-- The commutator of lifts of diagonal matrices is multiplicative in the second entry. -/
theorem comm_h_mul_right (s t t' : Γ(T.left, ⊤)ˣ) :
    X.comm (Mat.h s) (Mat.h (t * t')) =
      X.comm (Mat.h s) (Mat.h t) * X.comm (Mat.h s) (Mat.h t') := by
  rw [X.comm_eq (e₁ := X.hl s) (e₂ := X.hl t * X.hl t')
      (X.Q_hl s) (by rw [map_mul, Q_hl, Q_hl, Mat.h_mul]),
    X.comm_eq (X.Q_hl s) (X.Q_hl t), X.comm_eq (X.Q_hl s) (X.Q_hl t')]
  exact commutator_mul_right _ _ _
    (X.commutator_central (by rw [Q_hl, Q_hl]; exact Mat.h_comm s t'))

/-- Restricting the commutator of lifts of diagonal matrices. -/
theorem comm_h_res {V : Over S} (k : V ⟶ T) (s t : Γ(T.left, ⊤)ˣ) :
    k ≫ X.comm (Mat.h s) (Mat.h t) = X.comm (Mat.h (umap k s)) (Mat.h (umap k t)) := by
  rw [X.comm_res, res, Mat.map_h, Mat.map_h]

variable {Z : CommGroupScheme S} (i : Z.toGrp ⟶ X.E)
  (hi : ∀ ⦃T : Over S⦄ (e : T ⟶ X.E.X), X.Q T e = 1 → ∃ c : T ⟶ Z.X, c ≫ i.hom.hom = e)

/-- The commutator of lifts of `h(s)` and `h(t)`, as a point of the kernel `Z`. -/
def hPair (s t : Γ(T.left, ⊤)ˣ) : T ⟶ Z.X :=
  (hi _ (X.Q_comm_h s t)).choose

theorem hPair_spec (s t : Γ(T.left, ⊤)ˣ) :
    X.hPair i hi s t ≫ i.hom.hom = X.comm (Mat.h s) (Mat.h t) :=
  (hi _ (X.Q_comm_h s t)).choose_spec

section Mono

variable [Mono i.hom.hom]

theorem hPair_mul_left (s s' t : Γ(T.left, ⊤)ˣ) :
    X.hPair i hi (s * s') t = X.hPair i hi s t * X.hPair i hi s' t := by
  rw [← cancel_mono i.hom.hom, MonObj.mul_comp, hPair_spec, hPair_spec, hPair_spec,
    comm_h_mul_left]

theorem hPair_mul_right (s t t' : Γ(T.left, ⊤)ˣ) :
    X.hPair i hi s (t * t') = X.hPair i hi s t * X.hPair i hi s t' := by
  rw [← cancel_mono i.hom.hom, MonObj.mul_comp, hPair_spec, hPair_spec, hPair_spec,
    comm_h_mul_right]

theorem hPair_res {V : Over S} (k : V ⟶ T) (s t : Γ(T.left, ⊤)ˣ) :
    k ≫ X.hPair i hi s t = X.hPair i hi (umap k s) (umap k t) := by
  rw [← cancel_mono i.hom.hom, Category.assoc, hPair_spec, hPair_spec, comm_h_res]

/-- The commutator pairing of lifts of diagonal matrices, a natural bimultiplicative pairing of
units with values in `Z`. -/
def hUnitPairing : UnitPairing Z where
  app _ := MonoidHom.mk'
    (fun s => MonoidHom.mk' (fun t => X.hPair i hi s t) (X.hPair_mul_right i hi s))
    (fun s s' => MonoidHom.ext fun t => X.hPair_mul_left i hi s s' t)
  naturality k s t := X.hPair_res i hi k s t

end Mono

include i hi in
/-- **Commutativity of `D'`.** If the kernel of `Q` is the image of a monomorphism from a
separated commutative group scheme `Z`, then lifts of diagonal matrices commute. -/
theorem dComm_of_separated (hm : Mono i.hom.hom) [IsSeparated Z.X.hom] : X.DComm := by
  intro T s t
  have := hm
  have h := (X.hUnitPairing i hi).eq_one T s t
  change X.hPair i hi s t = 1 at h
  rw [← X.hPair_spec i hi, h, MonObj.one_comp]

end Ext

end Langlands.GroupScheme.SL2CentralExtension
