import Langlands.Representation.Aubert.ActualCutComplex
import Langlands.Representation.Jacquet.Parabolic

/-! Actual coinvariants and normalized Jacquet modules of finite products. -/

noncomputable section

namespace Langlands.Aubert.FiniteProduct

open GeneralLinear
open scoped BigOperators NNReal

universe uJ uG uM uF

variable {J : Type uJ} {G : Type uG} [Group G]
  {M : J → Type uM} [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]

/-- The actual quotient-to-product map, defined by the coordinate quotient maps. -/
def coinvariantsToProduct (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G) :
    Jacquet.Coinvariants (representation ρ) N →ₗ[ℂ] ∀ j, Jacquet.Coinvariants (ρ j) N :=
  Jacquet.lift (representation ρ) N
    (LinearMap.piMap (fun j => Jacquet.mk (ρ j) N)) (fun n => by
      ext x j
      exact Jacquet.mk_apply_subgroup (ρ j) N n (x j))

@[simp]
theorem coinvariantsToProduct_mk (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G)
    (x : ∀ j, M j) (j : J) :
    coinvariantsToProduct ρ N (Jacquet.mk (representation ρ) N x) j =
      Jacquet.mk (ρ j) N (x j) := rfl

section Insertion

variable [DecidableEq J]

theorem representation_single (ρ : ∀ j, Representation ℂ G (M j))
    (g : G) (j : J) (v : M j) :
    representation ρ g (Pi.single j v) = Pi.single j (ρ j g v) := by
  funext k
  by_cases hk : k = j
  · subst k
    simp only [representation_apply, Pi.single_eq_same]
  · simp only [representation_apply, Pi.single_eq_of_ne hk, map_zero]

/-- Descend one coordinate inclusion to the actual quotient. -/
def coordinateToCoinvariants (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G)
    (j : J) :
    Jacquet.Coinvariants (ρ j) N →ₗ[ℂ] Jacquet.Coinvariants (representation ρ) N :=
  Jacquet.lift (ρ j) N
    (Jacquet.mk (representation ρ) N ∘ₗ LinearMap.single ℂ M j) (fun n => by
      ext v
      change Jacquet.mk (representation ρ) N (Pi.single j (ρ j n v)) =
        Jacquet.mk (representation ρ) N (Pi.single j v)
      rw [← representation_single]
      exact Jacquet.mk_apply_subgroup (representation ρ) N n (Pi.single j v))

@[simp]
theorem coordinateToCoinvariants_mk (ρ : ∀ j, Representation ℂ G (M j))
    (N : Subgroup G) (j : J) (v : M j) :
    coordinateToCoinvariants ρ N j (Jacquet.mk (ρ j) N v) =
      Jacquet.mk (representation ρ) N (Pi.single j v) := rfl

variable [Fintype J]

/-- The inverse map sums the descended coordinate inclusions. -/
def productToCoinvariants (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G) :
    (∀ j, Jacquet.Coinvariants (ρ j) N) →ₗ[ℂ] Jacquet.Coinvariants (representation ρ) N :=
  ∑ j, coordinateToCoinvariants ρ N j ∘ₗ LinearMap.proj j

theorem productToCoinvariants_mk (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G)
    (x : ∀ j, M j) :
    productToCoinvariants ρ N (fun j => Jacquet.mk (ρ j) N (x j)) =
      Jacquet.mk (representation ρ) N x := by
  simp only [productToCoinvariants, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, coordinateToCoinvariants_mk]
  rw [← map_sum, LinearMap.sum_single_apply]

end Insertion

variable [Fintype J]

/-- Canonical actual finite-product coinvariant equivalence. -/
def coinvariantsEquiv (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G) :
    Jacquet.Coinvariants (representation ρ) N ≃ₗ[ℂ] ∀ j, Jacquet.Coinvariants (ρ j) N := by
  classical
  exact
    { __ := coinvariantsToProduct ρ N
      invFun := productToCoinvariants ρ N
      left_inv := fun x => by
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (representation ρ) N x
        exact productToCoinvariants_mk ρ N v
      right_inv := fun x => by
        choose v hv using fun j => Jacquet.mk_surjective (ρ j) N (x j)
        have hx : (fun j => Jacquet.mk (ρ j) N (v j)) = x := funext hv
        rw [← hx, productToCoinvariants_mk]
        rfl }

@[simp]
theorem coinvariantsEquiv_mk (ρ : ∀ j, Representation ℂ G (M j)) (N : Subgroup G)
    (x : ∀ j, M j) (j : J) :
    coinvariantsEquiv ρ N (Jacquet.mk (representation ρ) N x) j =
      Jacquet.mk (ρ j) N (x j) := rfl

section Jacquet

variable {F : Type uF} [CommRing F] {n : ℕ} (C : BlockShape n)

/-- The actual standard parabolic Jacquet quotient of a finite product. -/
def jacquetEquiv (ρ : ∀ j, Representation ℂ (GeneralLinear n F) (M j)) :
    C.JacquetModule (representation ρ) ≃ₗ[ℂ] ∀ j, C.JacquetModule (ρ j) :=
  (C.jacquetModuleEquiv (representation ρ)).trans
    ((coinvariantsEquiv ρ (C.unipotentSubgroup F)).trans
      (LinearEquiv.piCongrRight fun j => (C.jacquetModuleEquiv (ρ j)).symm))

@[simp]
theorem jacquetEquiv_mk (ρ : ∀ j, Representation ℂ (GeneralLinear n F) (M j))
    (x : ∀ j, M j) (j : J) :
    jacquetEquiv C ρ (C.jacquetMk (representation ρ) x) j =
      C.jacquetMk (ρ j) (x j) := by
  change (C.jacquetModuleEquiv (ρ j)).symm
    (coinvariantsEquiv ρ (C.unipotentSubgroup F)
      (C.jacquetModuleEquiv (representation ρ) (C.jacquetMk (representation ρ) x)) j) = _
  rw [BlockShape.jacquetModuleEquiv_mk, coinvariantsEquiv_mk]
  exact (C.jacquetModuleEquiv (ρ j)).symm_apply_apply (C.jacquetMk (ρ j) (x j))

/-- This equivalence respects the actual normalized Levi action. -/
theorem jacquetEquiv_intertwining (δ : C.Levi F →* ℝ≥0ˣ)
    (ρ : ∀ j, Representation ℂ (GeneralLinear n F) (M j))
    (m : C.Levi F) (x : C.JacquetModule (representation ρ)) :
    jacquetEquiv C ρ (C.normalizedJacquetOf δ (representation ρ) m x) =
      representation (fun j => C.normalizedJacquetOf δ (ρ j)) m (jacquetEquiv C ρ x) := by
  obtain ⟨v, rfl⟩ := C.jacquetMk_surjective (representation ρ) x
  rw [BlockShape.normalizedJacquetOf_mk, map_smul]
  funext j
  simp only [Pi.smul_apply, jacquetEquiv_mk, representation_apply,
    BlockShape.normalizedJacquetOf_mk]

end Jacquet
end Langlands.Aubert.FiniteProduct
