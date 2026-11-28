import Langlands.Cohomology.ModuleComplex.TensorSignsUpNat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.TotalComplex

/-! # Finite coordinates in the total cochains of a bicomplex -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Cohomology.ModuleComplex

local notation "up" => ComplexShape.up ℕ

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{u} R) up up)

/-- Pairs of bidegrees in one total degree. -/
abbrev TotalCochainIndex (n : ℕ) : Type :=
  ↑(ComplexShape.π up up up ⁻¹' ({n} : Set ℕ))

private def indexEquiv (n : ℕ) : TotalCochainIndex n ≃ Fin (n + 1) where
  toFun pq := ⟨pq.1.2, by have h : pq.1.1 + pq.1.2 = n := pq.2; omega⟩
  invFun q := ⟨(n - q, q), by change n - (q : ℕ) + q = n; omega⟩
  left_inv pq := Subtype.ext (Prod.ext (by
    have h : pq.1.1 + pq.1.2 = n := pq.2
    change n - pq.1.2 = pq.1.1
    omega) rfl)
  right_inv q := rfl

private abbrev indexFintype (n : ℕ) : Fintype (TotalCochainIndex n) :=
  Fintype.ofEquiv (Fin (n + 1)) (indexEquiv n).symm

/-- A total cochain is a finite family with one entry at each bidegree. -/
def totalCochainCoordinates (n : ℕ) :
    (K.total up).X n ≃ₗ[R] ∀ pq : TotalCochainIndex n, (K.X pq.1.1).X pq.1.2 := by
  letI := indexFintype n
  let C := K.toGradedObject.mapObjFun (ComplexShape.π up up up) n
  exact (ModuleCat.coprodIsoDirectSum C).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype R (TotalCochainIndex n) (fun pq => C pq))

/-- Inclusion of a bidegree summand is the family supported at that bidegree. -/
lemma totalCochainCoordinates_ι (n : ℕ) (pq : TotalCochainIndex n)
    (x : (K.X pq.1.1).X pq.1.2) :
    totalCochainCoordinates K n (K.ιTotal up pq.1.1 pq.1.2 n pq.2 x) =
      Pi.single (M := fun b => (K.X b.1.1).X b.1.2) pq x := by
  let := indexFintype n
  let C := K.toGradedObject.mapObjFun (ComplexShape.π up up up) n
  change DirectSum.linearEquivFunOnFintype R (TotalCochainIndex n) (fun pq => C pq)
    ((ModuleCat.coprodIsoDirectSum C).hom (Sigma.ι C pq x)) = _
  exact (congrArg (DirectSum.linearEquivFunOnFintype R (TotalCochainIndex n) (fun pq => C pq))
    (ConcreteCategory.congr_hom (ModuleCat.ι_coprodIsoDirectSum_hom C pq) (show C pq from x))).trans
    (DirectSum.linearEquivFunOnFintype_lof R (M := fun i : TotalCochainIndex n => C i) pq
      (show C pq from x))

/-- On an included term, the total differential is the horizontal
differential plus the signed vertical differential. -/
lemma ιTotal_d_cochain (n : ℕ) (pq : TotalCochainIndex n) :
    K.ιTotal up pq.1.1 pq.1.2 n pq.2 ≫ (K.total up).d n (n + 1) =
      (K.d pq.1.1 (pq.1.1 + 1)).f pq.1.2 ≫
        K.ιTotal up (pq.1.1 + 1) pq.1.2 (n + 1) (by
          have h : pq.1.1 + pq.1.2 = n := pq.2
          change pq.1.1 + 1 + pq.1.2 = n + 1
          omega) +
      (-1 : ℤ) ^ pq.1.1 • ((K.X pq.1.1).d pq.1.2 (pq.1.2 + 1) ≫
        K.ιTotal up pq.1.1 (pq.1.2 + 1) (n + 1) (by
          have h : pq.1.1 + pq.1.2 = n := pq.2
          change pq.1.1 + (pq.1.2 + 1) = n + 1
          omega)) := by
  have h : pq.1.1 + pq.1.2 = n := pq.2
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq K up (show (ComplexShape.up ℕ).Rel pq.1.1 (pq.1.1 + 1) from rfl)
      pq.1.2 (n + 1) (by change pq.1.1 + 1 + pq.1.2 = n + 1; omega),
    HomologicalComplex₂.d₂_eq K up pq.1.1 (show (ComplexShape.up ℕ).Rel pq.1.2 (pq.1.2 + 1) from rfl)
      (n + 1) (by change pq.1.1 + (pq.1.2 + 1) = n + 1; omega)]
  change (1 : ℤˣ) • _ + ((ComplexShape.up ℕ).ε pq.1.1) • _ = _
  rw [one_smul, ε_up_ℕ, Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end Langlands.Cohomology.ModuleComplex
