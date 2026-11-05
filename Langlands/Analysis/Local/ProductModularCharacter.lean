import Langlands.Analysis.Local.NormalSubgroupModularCharacter
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Induction.CompactQuotientDuality

/-! # Modular characters of binary and finite products -/

noncomputable section

universe u v w

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal

namespace Langlands.QuotientIntegration

variable {A : Type u} {B : Type v} [Group A] [Group B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]
  [T2Space A] [LocallyCompactSpace A] [LocallyCompactSpace B]

/-- Transport through a continuous isomorphism onto an actual closed normal subgroup. -/
theorem modularCharacter_subgroupEquiv (H : Subgroup A) (hH : IsClosed (H : Set A))
    [H.Normal] (e : B ≃ₜ* H) (b : B) :
    modularCharacter (e b : A) = modularCharacter b := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient H) := borel (LeftQuotient H)
  let : BorelSpace (LeftQuotient H) := ⟨rfl⟩
  let : MeasurableSpace (A ⧸ H) := borel (A ⧸ H)
  let : BorelSpace (A ⧸ H) := ⟨rfl⟩
  exact (modularCharacter_normalSubgroup H hH (e b)).symm.trans
    (Langlands.Aubert.General.modularCharacter_continuousMulEquiv e b)

end Langlands.QuotientIntegration

namespace Langlands.ProductMeasure

section Binary

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]

private def firstFactor : Subgroup (G × H) where
  carrier := {x | x.2 = 1}
  one_mem' := rfl
  mul_mem' {a b} hx hy := by
    change a.2 = 1 at hx
    change b.2 = 1 at hy
    change a.2 * b.2 = 1
    rw [hx, hy, mul_one]
  inv_mem' {a} hx := by
    change a.2 = 1 at hx
    change a.2⁻¹ = 1
    rw [hx, inv_one]

private instance firstFactor_normal : (firstFactor (G := G) (H := H)).Normal where
  conj_mem x hx y := by
    change x.2 = 1 at hx
    change y.2 * x.2 * y.2⁻¹ = 1
    simp [hx]

private def firstFactorEquiv : G ≃ₜ* firstFactor (G := G) (H := H) where
  toFun g := ⟨(g, 1), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_mul' g h := by apply Subtype.ext; simp
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

/-- The first factor's modular character agrees with that of its insertion in the product. -/
theorem modularCharacter_prod_one (g : G) :
    modularCharacter (g, (1 : H)) = modularCharacter g := by
  exact Langlands.QuotientIntegration.modularCharacter_subgroupEquiv
    (firstFactor (G := G) (H := H))
    (isClosed_eq continuous_snd continuous_const) firstFactorEquiv g

private def swapEquiv : (G × H) ≃ₜ* (H × G) :=
  ContinuousMulEquiv.mk' (Homeomorph.prodComm G H) (fun _ _ => rfl)

/-- The second factor's modular character agrees with that of its insertion in the product. -/
theorem modularCharacter_one_prod (h : H) :
    modularCharacter ((1 : G), h) = modularCharacter h := by
  exact (Langlands.Aubert.General.modularCharacter_continuousMulEquiv
    (swapEquiv (G := H) (H := G)) (h, (1 : G))).trans (modularCharacter_prod_one h)

/-- The intrinsic modular character of an actual binary product is the product of the two values. -/
theorem modularCharacter_prod (x : G × H) :
    modularCharacter x = modularCharacter x.1 * modularCharacter x.2 := by
  have hx : x = (x.1, (1 : H)) * ((1 : G), x.2) := by ext <;> simp
  calc
    modularCharacter x =
        modularCharacter (x.1, (1 : H)) * modularCharacter ((1 : G), x.2) := by
      conv_lhs => rw [hx, map_mul]
    _ = _ := by rw [modularCharacter_prod_one, modularCharacter_one_prod]

/-- Product of the two intrinsic modular characters as a homomorphism on the actual product. -/
def productModularCharacter : (G × H) →* ℝ≥0 where
  toFun x := modularCharacter x.1 * modularCharacter x.2
  map_one' := by simp
  map_mul' x y := by simp [map_mul, mul_mul_mul_comm]

@[simp] theorem productModularCharacter_apply (x : G × H) :
    productModularCharacter x = modularCharacter x := (modularCharacter_prod x).symm

/-- Positive right translation scales fixed product-group Haar by the product of local values. -/
theorem map_mul_right_haar_eq_prod [MeasurableSpace (G × H)] [BorelSpace (G × H)]
    (x : G × H) :
    Measure.map (· * x) (haar : Measure (G × H)) =
      (modularCharacter x.1 * modularCharacter x.2) • haar := by
  rw [Langlands.Induction.map_mul_right_haar_eq, modularCharacter_prod]

end Binary

section Finite

variable {ι : Type u} {G : ι → Type v} [Fintype ι] [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]

private def coordinateSubgroup (i : ι) : Subgroup (∀ j, G j) where
  carrier := {x | ∀ j, j ≠ i → x j = 1}
  one_mem' := by simp
  mul_mem' hx hy j hj := by simp [hx j hj, hy j hj]
  inv_mem' hx j hj := by simp [hx j hj]

private instance coordinateSubgroup_normal (i : ι) : (coordinateSubgroup (G := G) i).Normal where
  conj_mem x hx y j hj := by
    change y j * x j * (y j)⁻¹ = 1
    simp [hx j hj]

private def coordinateEquiv [DecidableEq ι] (i : ι) : G i ≃ₜ* coordinateSubgroup (G := G) i where
  toFun g := ⟨Pi.mulSingle i g, fun j hj => Pi.mulSingle_eq_of_ne hj g⟩
  invFun x := x.val i
  left_inv g := Pi.mulSingle_eq_same i g
  right_inv x := by
    apply Subtype.ext
    funext j
    change Pi.mulSingle i (x.val i) j = x.val j
    by_cases hji : j = i
    · subst j
      exact Pi.mulSingle_eq_same i _
    · rw [Pi.mulSingle_eq_of_ne hji, x.property j hji]
  map_mul' g h := Subtype.ext (Pi.mulSingle_mul i g h)
  continuous_toFun := (_root_.continuous_mulSingle i).subtype_mk _
  continuous_invFun := (continuous_apply i).comp continuous_subtype_val

/-- A single local coordinate has its original modular character in the finite product. -/
theorem modularCharacter_pi_mulSingle [DecidableEq ι] (i : ι) (g : G i) :
    modularCharacter (Pi.mulSingle i g) = modularCharacter g := by
  apply Langlands.QuotientIntegration.modularCharacter_subgroupEquiv
    (coordinateSubgroup (G := G) i) _ (coordinateEquiv i) g
  change IsClosed {x : ∀ j, G j | ∀ j, j ≠ i → x j = 1}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply j) continuous_const

private theorem modularCharacter_pi_eq_prod_support (s : Finset ι) (x : ∀ i, G i)
    (hx : ∀ i, i ∉ s → x i = 1) :
    modularCharacter x = ∏ i ∈ s, modularCharacter (x i) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    have hx1 : x = 1 := funext fun i => hx i (by simp)
    simp [hx1]
  | @insert a s ha ih =>
    let y := (Pi.mulSingle a (x a))⁻¹ * x
    have hy : ∀ i, i ∉ s → y i = 1 := by
      intro i hi
      by_cases hia : i = a
      · subst i
        simp [y]
      · simpa [y, Pi.mulSingle_eq_of_ne hia] using hx i (by simp [hia, hi])
    have hxy : x = Pi.mulSingle a (x a) * y := by simp [y]
    calc
      modularCharacter x =
          modularCharacter (Pi.mulSingle a (x a)) * modularCharacter y := by
        conv_lhs => rw [hxy, map_mul]
      _ = modularCharacter (x a) * ∏ i ∈ s, modularCharacter (y i) := by
        rw [modularCharacter_pi_mulSingle a (x a), ih y hy]
      _ = ∏ i ∈ insert a s, modularCharacter (x i) := by
        rw [Finset.prod_insert ha]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        simp [y, Pi.mulSingle_eq_of_ne hia]

/-- The intrinsic modular character of an actual finite dependent product is the local product. -/
theorem modularCharacter_pi (x : ∀ i, G i) :
    modularCharacter x = ∏ i, modularCharacter (x i) :=
  modularCharacter_pi_eq_prod_support Finset.univ x (by simp)

/-- The product of local intrinsic modular values as a homomorphism on a finite product. -/
def piModularCharacter : (∀ i, G i) →* ℝ≥0 where
  toFun x := ∏ i, modularCharacter (x i)
  map_one' := by simp
  map_mul' x y := by simp [map_mul, Finset.prod_mul_distrib]

@[simp] theorem piModularCharacter_apply (x : ∀ i, G i) :
    piModularCharacter x = modularCharacter x := (modularCharacter_pi x).symm

/-- Positive right translation scales fixed finite-product Haar by the local modular product. -/
theorem map_mul_right_haar_eq_pi [MeasurableSpace (∀ i, G i)] [BorelSpace (∀ i, G i)]
    (x : ∀ i, G i) :
    Measure.map (· * x) (haar : Measure (∀ i, G i)) =
      (∏ i, modularCharacter (x i)) • haar := by
  rw [Langlands.Induction.map_mul_right_haar_eq, modularCharacter_pi]

end Finite

end Langlands.ProductMeasure
