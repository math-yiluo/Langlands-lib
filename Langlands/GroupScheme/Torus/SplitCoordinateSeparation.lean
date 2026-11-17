import Langlands.GroupScheme.Torus.Split
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Separation of split-torus coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

/-- Every nonempty scheme has a relative affine test with a global unit different
from one, including in residue characteristic two. -/
theorem exists_test_unit_ne_one (S : Scheme.{u}) [Nonempty S] :
    ∃ (T : Over S) (a : (Γ(T.left, ⊤))ˣ), a ≠ 1 := by
  let s : S := Classical.choice inferInstance
  let k := S.residueField s
  let A := CommRingCat.of (DualNumber k)
  let f : Spec A ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ S.fromSpecResidueField s
  let a : (DualNumber k)ˣ :=
    ⟨1 + DualNumber.eps, 1 - DualNumber.eps,
      by ext <;> simp,
      by ext <;> simp⟩
  have ha : a ≠ 1 := by
    intro h
    have := congrArg (fun b : (DualNumber k)ˣ => TrivSqZeroExt.snd b.val) h
    simp [a] at this
  let e := Units.mapEquiv (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨Over.mk f, e.symm a, ?_⟩
  intro h
  apply ha
  simpa using congrArg e h

/-- Coordinates of a split torus over a nonempty base are distinguished by
their values on all relative test schemes. -/
theorem index_eq_of_points_eq {S : Scheme.{u}} [Nonempty S]
    {I : Type u} [Finite I] {i j : I}
    (h : ∀ (T : Over S) (x : T ⟶ (splitTorus S I).X),
      pointsEquiv I T x i = pointsEquiv I T x j) : i = j := by
  classical
  obtain ⟨T, a, ha⟩ := exists_test_unit_ne_one S
  by_contra hij
  let z : I → (Γ(T.left, ⊤))ˣ := Function.update 1 i a
  have hz := h T ((pointsEquiv I T).symm z)
  apply ha
  simpa [z, Function.update, hij, Ne.symm hij] using hz

/-- Two index maps inducing the same reindexing on all split-torus points
coincide over a nonempty base. -/
theorem indexMap_eq_of_points_eq {S : Scheme.{u}} [Nonempty S]
    {I J : Type u} [Finite I] (σ τ : J → I)
    (h : ∀ (T : Over S) (x : T ⟶ (splitTorus S I).X) (j : J),
      pointsEquiv I T x (σ j) = pointsEquiv I T x (τ j)) : σ = τ := by
  funext j
  exact index_eq_of_points_eq (fun T x => h T x j)

/-- Equal reindexings on all torus points induce equal reindexings of global
coefficient functions. On an empty base the coefficient ring is trivial. -/
theorem reindex_eq_of_points_eq {S : Scheme.{u}}
    {I J : Type u} [Finite I] (σ τ : J → I)
    (h : ∀ (T : Over S) (x : T ⟶ (splitTorus S I).X) (j : J),
      pointsEquiv I T x (σ j) = pointsEquiv I T x (τ j))
    (z : I → Γ(S, ⊤)) : z ∘ σ = z ∘ τ := by
  cases isEmpty_or_nonempty S with
  | inl hS => exact Subsingleton.elim _ _
  | inr hS => rw [indexMap_eq_of_points_eq σ τ h]

/-- Reindexing the finite split coefficient algebra by a coordinate equivalence. -/
def coefficientReindex (S : Scheme.{u}) {I J : Type u} (σ : J ≃ I) :
    (I → Γ(S, ⊤)) ≃ₐ[Γ(S, ⊤)] (J → Γ(S, ⊤)) where
  toFun z := z ∘ σ
  invFun z := z ∘ σ.symm
  left_inv z := by funext i; simp
  right_inv z := by funext j; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coefficientReindex_apply (S : Scheme.{u}) {I J : Type u}
    (σ : J ≃ I) (z : I → Γ(S, ⊤)) (j : J) :
    coefficientReindex S σ z j = z (σ j) := rfl

/-- Equality on all torus tests makes the associated coefficient-algebra
equivalences equal, even when the base is empty. -/
theorem coefficientReindex_eq_of_points_eq {S : Scheme.{u}}
    {I J : Type u} [Finite I] (σ τ : J ≃ I)
    (h : ∀ (T : Over S) (x : T ⟶ (splitTorus S I).X) (j : J),
      pointsEquiv I T x (σ j) = pointsEquiv I T x (τ j)) :
    coefficientReindex S σ = coefficientReindex S τ := by
  ext z j
  exact congrFun (reindex_eq_of_points_eq σ τ h z) j

end Langlands.GroupScheme.splitTorus
