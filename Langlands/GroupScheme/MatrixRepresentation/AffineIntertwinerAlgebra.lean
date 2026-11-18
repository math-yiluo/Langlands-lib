import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientAlgebra
import Langlands.Algebra.SemisimpleOperatorAlgebra
import Mathlib.RingTheory.Etale.Basic

/-! # The actual intertwiner algebra and the operator commutant -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.AffineIntertwinerAlgebra

open AffineCoefficientAlgebra AffineCoefficients

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

local instance operatorRing : Ring (operatorAlgebra ρ) := inferInstance

/-- The actual self-intertwiner algebra, obtained from the operator commutant
through the matrix-to-endomorphism equivalence. -/
def intertwinerAlgebra : Subalgebra k (Matrix n n k) :=
  (Subalgebra.centralizer k
    (operatorAlgebra ρ : Set (Module.End k (n → k)))).comap
      (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k)).toAlgHom

theorem mem_intertwinerAlgebra_iff (C : Matrix n n k) :
    C ∈ intertwinerAlgebra ρ ↔ Intertwines ρ ρ C := by
  constructor
  · intro h
    apply (intertwines_iff ρ C).mpr
    intro ℓ
    apply (Matrix.toLinAlgEquiv' :
      Matrix n n k ≃ₐ[k] Module.End k (n → k)).injective
    rw [map_mul, map_mul]
    exact (h (coefficientMap ρ ℓ).mulVecLin (Algebra.subset_adjoin ⟨ℓ, rfl⟩)).symm
  · intro h
    have hle : operatorAlgebra ρ ≤
        Subalgebra.centralizer k ({C.mulVecLin} : Set (Module.End k (n → k))) := by
      rw [operatorAlgebra, Algebra.adjoin_le_iff]
      rintro _ ⟨ℓ, rfl⟩ f hf
      rcases hf with rfl
      have hh := congrArg (Matrix.toLinAlgEquiv' :
        Matrix n n k ≃ₐ[k] Module.End k (n → k)) ((intertwines_iff ρ C).mp h ℓ)
      rw [map_mul, map_mul] at hh
      exact hh
    intro a ha
    exact (hle ha C.mulVecLin (Set.mem_singleton _)).symm

/-- The adjoin in the published target already consists of the actual
self-intertwiners. -/
theorem intertwinerAlgebra_eq_adjoin :
    intertwinerAlgebra ρ = Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C} := by
  apply le_antisymm
  · intro C hC
    exact Algebra.subset_adjoin ((mem_intertwinerAlgebra_iff ρ C).mp hC)
  · apply Algebra.adjoin_le
    intro C hC
    exact (mem_intertwinerAlgebra_iff ρ C).mpr hC

/-- Actual self-intertwiners are algebra-isomorphic to the operator commutant. -/
def intertwinerAlgebraEquiv :
    intertwinerAlgebra ρ ≃ₐ[k]
      Subalgebra.centralizer k
        (operatorAlgebra ρ : Set (Module.End k (n → k))) := by
  let f : intertwinerAlgebra ρ →ₐ[k]
      Subalgebra.centralizer k (operatorAlgebra ρ : Set (Module.End k (n → k))) :=
    ((((Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] Module.End k (n → k)).toAlgHom).comp
      (intertwinerAlgebra ρ).val).codRestrict _ (fun a => a.property))
  apply AlgEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Matrix.toLin'.injective
    exact congrArg Subtype.val hab
  · intro g
    refine ⟨⟨LinearMap.toMatrix' g.val, ?_⟩, ?_⟩
    · change Matrix.toLin' (LinearMap.toMatrix' g.val) ∈
        Subalgebra.centralizer k (operatorAlgebra ρ : Set (Module.End k (n → k)))
      rw [Matrix.toLin'_toMatrix']
      exact g.property
    · apply Subtype.ext
      exact Matrix.toLin'_toMatrix' g.val

/-- The exact adjoin algebra used by the target is the operator commutant. -/
def endAlgEquiv :
    Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C} ≃ₐ[k]
      Subalgebra.centralizer k
        (operatorAlgebra ρ : Set (Module.End k (n → k))) :=
  (Subalgebra.equivOfEq _ _ (intertwinerAlgebra_eq_adjoin ρ).symm).trans
    (intertwinerAlgebraEquiv ρ)

/-- An algebra equivalence induces an equivalence of its centres. -/
def centerCongr {A B : Type*} [Semiring A] [Semiring B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) : Subalgebra.center k A ≃ₐ[k] Subalgebra.center k B where
  toFun z := ⟨e z.val, by
    apply Subalgebra.mem_center_iff.mpr
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e ((Subalgebra.mem_center_iff.mp z.property) a)⟩
  invFun z := ⟨e.symm z.val, by
    apply Subalgebra.mem_center_iff.mpr
    intro a
    obtain ⟨b, rfl⟩ := e.symm.surjective a
    simpa only [map_mul] using
      congrArg e.symm ((Subalgebra.mem_center_iff.mp z.property) b)⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.val)
  right_inv z := Subtype.ext (e.apply_symm_apply z.val)
  map_add' z w := Subtype.ext (e.map_add z.val w.val)
  map_mul' z w := Subtype.ext (e.map_mul z.val w.val)
  commutes' c := Subtype.ext (e.commutes c)

/-- For a semisimple actual representation, the centre of its operator algebra
equals the centre of the target's actual endomorphism algebra. -/
def operatorCenterEquivEndCenter [IsSemisimpleModule (operatorAlgebra ρ) (n → k)] :
    Subalgebra.center k (operatorAlgebra ρ) ≃ₐ[k]
      Subalgebra.center k (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}) := by
  let e1 : Subalgebra.center k (operatorAlgebra ρ) ≃ₐ[k]
      Subalgebra.center k
        (Subalgebra.centralizer k (operatorAlgebra ρ : Set (Module.End k (n → k)))) :=
    Langlands.Algebra.SemisimpleOperatorAlgebra.centerCentralizerEquiv (operatorAlgebra ρ)
  let e2 : Subalgebra.center k
      (Subalgebra.centralizer k (operatorAlgebra ρ : Set (Module.End k (n → k)))) ≃ₐ[k]
      Subalgebra.center k (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}) :=
    centerCongr (endAlgEquiv ρ).symm
  exact e1.trans e2

/-- The target's étale-centre condition transfers to the operator algebra. -/
theorem etale_operatorCenter [IsSemisimpleModule (operatorAlgebra ρ) (n → k)]
    [Algebra.Etale k
      (Subalgebra.center k (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}))] :
    Algebra.Etale k (Subalgebra.center k (operatorAlgebra ρ)) :=
  Algebra.Etale.of_equiv (R := k)
    (A := Subalgebra.center k (Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}))
    (B := Subalgebra.center k (operatorAlgebra ρ)) (operatorCenterEquivEndCenter ρ).symm

end Langlands.GroupScheme.MatrixRepresentation.AffineIntertwinerAlgebra
