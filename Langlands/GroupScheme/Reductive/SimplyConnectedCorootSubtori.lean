import Langlands.LinearAlgebra.SimplyConnectedCartanComponents
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Closed coordinate subtori from subsets of a simple-coroot basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedCorootSubtori

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents
open Langlands.RootDatumSimpleCorootEquiv

variable {I J : Type u} [Fintype I]
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
  (hspan : P.corootSpan ℤ = ⊤)

/-- The full character coordinates given by pairing with the integral
simple-coroot basis. -/
def simpleCorootCoordinates : (I → ℤ) ≃ₗ[ℤ] (b.support → ℤ) := by
  classical
  exact P.toPerfPair.trans (simpleCorootBasis b hspan).dualBasis.equivFun

omit [Fintype I] in
/-- Each new character coordinate is the actual root-datum pairing against
one simple coroot. -/
theorem simpleCorootCoordinates_apply (x : I → ℤ) (i : b.support) :
    simpleCorootCoordinates P b hspan x i = P.toLinearMap x (P.coroot i) := by
  classical
  rw [simpleCorootCoordinates, LinearEquiv.trans_apply, Basis.dualBasis_equivFun,
    simpleCorootBasis_apply]
  rfl

variable (s : Set b.support)

local instance : Fintype s := Fintype.ofFinite s

/-- Restrict full characters to the selected simple-coroot coordinates. -/
def restriction : (I → ℤ) →ₗ[ℤ] (s → ℤ) where
  toFun x i := simpleCorootCoordinates P b hspan x i
  map_add' x y := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' n x := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- Extend selected simple-coroot character coordinates by zero, and carry
them back to the original full character lattice. -/
def extension : (s → ℤ) →ₗ[ℤ] (I → ℤ) := by
  classical
  exact
    { toFun := fun x => (simpleCorootCoordinates P b hspan).symm
        (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 0)
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        ext i
        by_cases hi : i ∈ s <;> simp [hi]
      map_smul' := by
        intro n x
        rw [← map_smul]
        congr 1
        ext i
        by_cases hi : i ∈ s <;> simp [hi] }

omit [Fintype I] in
/-- Restriction has the specified integral right inverse. -/
theorem restriction_comp_extension :
    (restriction P b hspan s).comp (extension P b hspan s) = LinearMap.id := by
  classical
  ext x i
  change simpleCorootCoordinates P b hspan
    ((simpleCorootCoordinates P b hspan).symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  simp

/-- The actual split-torus inclusion determined by selected simple coroots,
over an arbitrary base scheme. -/
def inclusion (S : Scheme.{u}) :
    splitTorus.commGroupScheme S s ⟶ splitTorus.commGroupScheme S I := by
  classical
  let : Fintype s := Fintype.ofFinite s
  exact splitTorus.exponentHom S s I (restriction P b hspan s)

/-- The actual retraction supplied by extension of characters by zero. -/
def retraction (S : Scheme.{u}) :
    splitTorus.commGroupScheme S I ⟶ splitTorus.commGroupScheme S s := by
  classical
  let : Fintype s := Fintype.ofFinite s
  exact splitTorus.exponentHom S I s (extension P b hspan s)

/-- The integral right inverse is an actual global retraction. -/
theorem inclusion_comp_retraction (S : Scheme.{u}) :
    inclusion P b hspan s S ≫ retraction P b hspan s S = 𝟙 _ := by
  classical
  let : Fintype s := Fintype.ofFinite s
  change splitTorus.exponentHom S s I (restriction P b hspan s) ≫
    splitTorus.exponentHom S I s (extension P b hspan s) = _
  rw [splitTorus.exponentHom_comp, restriction_comp_extension, splitTorus.exponentHom_id]

/-- Every selected simple-coroot torus is an actual closed split subtorus of
the original coordinate torus. -/
theorem inclusion_closed (S : Scheme.{u}) :
    IsClosedSubgroup (CommGroupScheme.groupHom (inclusion P b hspan s S)) := by
  let σ := CommGroupScheme.groupHom (inclusion P b hspan s S)
  let q := CommGroupScheme.groupHom (retraction P b hspan s S)
  have h : σ ≫ q = 𝟙 (splitTorus S s) :=
    congrArg CommGroupScheme.groupHom (inclusion_comp_retraction P b hspan s S)
  have : IsAffineHom (splitTorus S I).X.hom := isAffineHom_splitTorus S I
  have : IsSeparated q.hom.hom.left := by
    have : IsSeparated (q.hom.hom.left ≫ (splitTorus S s).X.hom) := by
      rw [Over.w]
      infer_instance
    exact IsSeparated.of_comp _ (splitTorus S s).X.hom
  have : IsClosedImmersion (σ.hom.hom.left ≫ q.hom.hom.left) := by
    have he : σ.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, h]
      rfl
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ q.hom.hom.left

/-- Pullback of every fixed-exponent character is exactly restriction to the
selected simple-coroot coordinates. -/
theorem inclusion_comp_character (S : Scheme.{u}) (x : I → ℤ) :
    inclusion P b hspan s S ≫ splitTorus.exponentCharacter S I x =
      splitTorus.exponentCharacter S s
        (fun i => P.toLinearMap x (P.coroot i)) := by
  classical
  let : Fintype s := Fintype.ofFinite s
  change splitTorus.exponentHom S s I (restriction P b hspan s) ≫ _ = _
  rw [splitTorus.exponentHom_comp_exponentCharacter]
  apply congrArg (splitTorus.exponentCharacter S s)
  ext i
  exact simpleCorootCoordinates_apply P b hspan x i

variable [Finite J] [P.IsReduced]

omit [Fintype I] in
/-- A root is orthogonal to every simple coroot outside its component. -/
theorem root_pairing_eq_zero_of_component_ne (r : J) (i : b.support)
    (hi : component b i ≠ rootComponent b hspan r) :
    P.pairing r i = 0 := by
  apply P.pairing_eq_zero_iff.mpr
  rw [← P.root_coroot_eq_pairing]
  exact (corootSupported_rootComponent b hspan r).pairing_eq_zero i hi

omit [Fintype I] in
/-- Restricting a root to the complementary simple-coroot coordinates is zero
exactly when the root belongs to the selected Cartan component. -/
theorem restriction_root_complement_eq_zero_iff (c : Component b) (r : J) :
    restriction P b hspan {i | component b i ≠ c} (P.root r) = 0 ↔
      rootComponent b hspan r = c := by
  classical
  constructor
  · intro hr
    by_contra hrc
    have hzero : ∀ i : b.support, P.toLinearMap (P.root r) (P.coroot i) = 0 := by
      intro i
      by_cases hi : component b i = c
      · rw [P.root_coroot_eq_pairing]
        exact root_pairing_eq_zero_of_component_ne P b hspan r i (by
          rw [hi]
          exact Ne.symm hrc)
      · have he := congrFun hr ⟨i, hi⟩
        change simpleCorootCoordinates P b hspan (P.root r) i = 0 at he
        rwa [simpleCorootCoordinates_apply] at he
    have hz : simpleCorootCoordinates P b hspan (P.root r) = 0 := by
      ext i
      rw [simpleCorootCoordinates_apply, hzero]
      rfl
    exact P.ne_zero r ((simpleCorootCoordinates P b hspan).injective
      (hz.trans (map_zero _).symm))
  · intro hrc
    ext i
    change simpleCorootCoordinates P b hspan (P.root r) i = 0
    rw [simpleCorootCoordinates_apply, P.root_coroot_eq_pairing]
    exact root_pairing_eq_zero_of_component_ne P b hspan r i (by
      rw [hrc]
      exact i.property)

end Langlands.GroupScheme.SimplyConnectedCorootSubtori
