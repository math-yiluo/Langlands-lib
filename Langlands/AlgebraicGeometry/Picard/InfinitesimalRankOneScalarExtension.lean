import Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Actual scalar extension of patched rank-one modules -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct
open TensorProduct.AlgebraTensorModule

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneScalarExtension

open InfinitesimalRankOnePatching

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B]
  (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom a) (CommRingCat.ofHom b))

/-- Scalar extension to the first leg, with its actual first projection. -/
def firstEquiv (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    A ⊗[R] patchedModule a b h c ≃ₗ[A] A :=
  ((frameEquiv a b h c v hv).symm.baseChange R A _ _).trans
    (AlgebraTensorModule.rid R A A)

/-- Scalar extension to the second leg, with its actual second projection. -/
def secondEquiv (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    B ⊗[R] patchedModule a b h c ≃ₗ[B] B :=
  (((frameEquiv a b h c v hv).symm.baseChange R B _ _).trans
    (AlgebraTensorModule.rid R B B)).trans (v⁻¹.mulLeftLinearEquiv B B)

@[simp]
lemma firstEquiv_tmul (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (t : A) (z : patchedModule a b h c) :
    firstEquiv a b h c v hv (t ⊗ₜ[R] z) = t * z.val.1 := by
  have hp := congrArg (fun w : patchedModule a b h c ↦ w.val.1)
    ((frameEquiv a b h c v hv).apply_symm_apply z)
  change algebraMap R A ((frameEquiv a b h c v hv).symm z) = z.val.1 at hp
  simp only [firstEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, hp, mul_comm]

@[simp]
lemma secondEquiv_tmul (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (t : B) (z : patchedModule a b h c) :
    secondEquiv a b h c v hv (t ⊗ₜ[R] z) = t * z.val.2 := by
  have hq := congrArg (fun w : patchedModule a b h c ↦ w.val.2)
    ((frameEquiv a b h c v hv).apply_symm_apply z)
  change (↑v⁻¹ : B) * algebraMap R B ((frameEquiv a b h c v hv).symm z) = z.val.2 at hq
  simp only [secondEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    AlgebraTensorModule.rid_tmul, Units.mulLeftLinearEquiv_apply, Algebra.smul_def]
  calc
    (↑v⁻¹ : B) * (algebraMap R B ((frameEquiv a b h c v hv).symm z) * t) =
        t * ((↑v⁻¹ : B) * algebraMap R B ((frameEquiv a b h c v hv).symm z)) := by ring
    _ = t * z.val.2 := by rw [hq]

/-- The first actual scalar-extension map is independent of the chosen unit lift. -/
lemma firstEquiv_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    firstEquiv a b h c v hv = firstEquiv a b h c w hw := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro t z
  exact (firstEquiv_tmul a b h c v hv t z).trans
    (firstEquiv_tmul a b h c w hw t z).symm

/-- The second actual scalar-extension map is independent of the chosen unit lift. -/
lemma secondEquiv_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    secondEquiv a b h c v hv = secondEquiv a b h c w hw := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro t z
  exact (secondEquiv_tmul a b h c v hv t z).trans
    (secondEquiv_tmul a b h c w hw t z).symm

/-- The elementary-tensor first projection uniquely determines the equivalence. -/
lemma firstEquiv_unique (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (e : A ⊗[R] patchedModule a b h c ≃ₗ[A] A)
    (he : ∀ t z, e (t ⊗ₜ[R] z) = t * z.val.1) :
    e = firstEquiv a b h c v hv := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro t z
  exact (he t z).trans (firstEquiv_tmul a b h c v hv t z).symm

/-- The elementary-tensor second projection uniquely determines the equivalence. -/
lemma secondEquiv_unique (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (e : B ⊗[R] patchedModule a b h c ≃ₗ[B] B)
    (he : ∀ t z, e (t ⊗ₜ[R] z) = t * z.val.2) :
    e = secondEquiv a b h c v hv := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro t z
  exact (he t z).trans (secondEquiv_tmul a b h c v hv t z).symm

/-- The first projection commutes with scalar extension of the prescribed diagonal map. -/
lemma firstEquiv_diagonalMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y)
    (z : A ⊗[R] patchedModule a b h c) :
    firstEquiv a b h d w hw ((diagonalMap a b h c d x y hxy).baseChange A z) =
      x * firstEquiv a b h c v hv z := by
  induction z using TensorProduct.inductionOn with
  | tmul t z => simp [mul_left_comm]
  | add z z' hz hz' => simp [hz, hz', mul_add]

/-- The second projection commutes with scalar extension of the prescribed diagonal map. -/
lemma secondEquiv_diagonalMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y)
    (z : B ⊗[R] patchedModule a b h c) :
    secondEquiv a b h d w hw ((diagonalMap a b h c d x y hxy).baseChange B z) =
      y * secondEquiv a b h c v hv z := by
  induction z using TensorProduct.inductionOn with
  | tmul t z => simp [mul_left_comm]
  | add z z' hz hz' => simp [hz, hz', mul_add]

/-- The first scalar-extension identification preserves prescribed unit isomorphisms. -/
lemma firstEquiv_diagonalEquiv (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y)
    (z : A ⊗[R] patchedModule a b h c) :
    firstEquiv a b h d w hw ((diagonalEquiv a b h c d x y hxy).baseChange R A _ _ z) =
      (x : A) * firstEquiv a b h c v hv z :=
  firstEquiv_diagonalMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy) z

/-- The second scalar-extension identification preserves prescribed unit isomorphisms. -/
lemma secondEquiv_diagonalEquiv (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y)
    (z : B ⊗[R] patchedModule a b h c) :
    secondEquiv a b h d w hw ((diagonalEquiv a b h c d x y hxy).baseChange R B _ _ z) =
      (y : B) * secondEquiv a b h c v hv z :=
  secondEquiv_diagonalMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy) z

/-- A surjective nilpotent leg supplies both actual scalar-extension identifications. -/
lemma exists_scalarExtensionEquivs
    (hb : Function.Surjective b) (hker : IsNilpotent (RingHom.ker b)) (c : Cˣ) :
    ∃ eA : A ⊗[R] patchedModule a b h c ≃ₗ[A] A,
      ∃ eB : B ⊗[R] patchedModule a b h c ≃ₗ[B] B,
        (∀ t z, eA (t ⊗ₜ[R] z) = t * z.val.1) ∧
          ∀ t z, eB (t ⊗ₜ[R] z) = t * z.val.2 := by
  obtain ⟨v, hv⟩ := NilpotentUnitReduction.unitsMap_surjective b hb hker c
  exact ⟨firstEquiv a b h c v hv, secondEquiv a b h c v hv,
    firstEquiv_tmul a b h c v hv, secondEquiv_tmul a b h c v hv⟩

section Overlap

variable [Algebra R C] [Algebra A C] [Algebra B C]
  [IsScalarTower R A C] [IsScalarTower R B C]
  (hs : IsPullback (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom (algebraMap A C))
    (CommRingCat.ofHom (algebraMap B C)))

local notation "aC" => algebraMap A C
local notation "bC" => algebraMap B C
local notation "P" c => patchedModule aC bC hs c

/-- The first identification on the common overlap, using actual iterated scalar extension. -/
def firstOverlapEquiv (c : Cˣ) (v : Bˣ) (hv : Units.map (bC).toMonoidHom v = c) :
    C ⊗[R] (P c) ≃ₗ[C] C :=
  ((cancelBaseChange R A C C (P c)).symm.trans
    ((firstEquiv aC bC hs c v hv).baseChange A C _ _)).trans
      (AlgebraTensorModule.rid A C C)

/-- The second identification on the common overlap, using actual iterated scalar extension. -/
def secondOverlapEquiv (c : Cˣ) (v : Bˣ) (hv : Units.map (bC).toMonoidHom v = c) :
    C ⊗[R] (P c) ≃ₗ[C] C :=
  ((cancelBaseChange R B C C (P c)).symm.trans
    ((secondEquiv aC bC hs c v hv).baseChange B C _ _)).trans
      (AlgebraTensorModule.rid B C C)

omit [IsScalarTower R B C] in
@[simp]
lemma firstOverlapEquiv_tmul (c : Cˣ) (v : Bˣ) (hv : Units.map (bC).toMonoidHom v = c)
    (t : C) (z : P c) :
    firstOverlapEquiv hs c v hv (t ⊗ₜ[R] z) = t * aC z.val.1 := by
  simp [firstOverlapEquiv, Algebra.smul_def, mul_comm]

omit [IsScalarTower R A C] in
@[simp]
lemma secondOverlapEquiv_tmul (c : Cˣ) (v : Bˣ) (hv : Units.map (bC).toMonoidHom v = c)
    (t : C) (z : P c) :
    secondOverlapEquiv hs c v hv (t ⊗ₜ[R] z) = t * bC z.val.2 := by
  simp [secondOverlapEquiv, Algebra.smul_def, mul_comm]

/-- The specified overlap multiplier is retained on every element of the common scalar extension. -/
lemma overlap_compat (c : Cˣ) (v : Bˣ) (hv : Units.map (bC).toMonoidHom v = c)
    (z : C ⊗[R] (P c)) :
    firstOverlapEquiv hs c v hv z = (c : C) * secondOverlapEquiv hs c v hv z := by
  induction z using TensorProduct.inductionOn with
  | tmul t z =>
      simp only [firstOverlapEquiv_tmul, secondOverlapEquiv_tmul]
      rw [z.property]
      ring
  | add z z' hz hz' => simp [hz, hz', mul_add]

end Overlap

end Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneScalarExtension
