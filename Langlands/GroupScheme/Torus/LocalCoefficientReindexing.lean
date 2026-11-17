import Langlands.GroupScheme.Torus.SplitCoordinateSeparation
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing locally specified coefficient permutations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme
namespace LocalCoefficientReindexing

variable {S : Scheme.{u}} {I J : Type u}

/-- An open cover carrying permutations that agree whenever two members have a
nonempty intersection. Empty intersections impose no condition on the indices. -/
structure Datum (S : Scheme.{u}) (I J : Type u) where
  Index : Type u
  opens : Index → S.Opens
  covers : (⨆ a, opens a) = ⊤
  permutation : Index → (J ≃ I)
  agree : ∀ a b, Nonempty ((opens a ⊓ opens b : S.Opens) : Scheme.{u}) →
    permutation a = permutation b

/-- Two local permutations describing the same transformation on every relative
unit test agree if their opens meet. -/
theorem permutation_eq_of_unitTests
    (F : ∀ T : Over S, (I → (Γ(T.left, ⊤))ˣ) → (J → (Γ(T.left, ⊤))ˣ))
    {U V : S.Opens} (σ τ : J ≃ I)
    (hσ : ∀ (T : Over S), Set.range T.hom ⊆ U →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (σ j))
    (hτ : ∀ (T : Over S), Set.range T.hom ⊆ V →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (τ j))
    (hUV : Nonempty ((U ⊓ V : S.Opens) : Scheme.{u})) : σ = τ := by
  classical
  let W : S.Opens := U ⊓ V
  let : Nonempty (W : Scheme.{u}) := hUV
  obtain ⟨T, a, ha⟩ := splitTorus.exists_test_unit_ne_one (W : Scheme.{u})
  let Z : Over S := Over.mk (T.hom ≫ W.ι)
  have hU : Set.range Z.hom ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact (T.hom t).property.1
  have hV : Set.range Z.hom ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact (T.hom t).property.2
  apply Equiv.ext
  intro j
  by_contra hij
  let z : I → (Γ(T.left, ⊤))ˣ := Function.update 1 (σ j) a
  have h := (hσ Z hU z j).symm.trans (hτ Z hV z j)
  apply ha
  simpa [z, Function.update, hij, Ne.symm hij] using h

/-- Construct gluing data from local formulas for a single transformation on
families of units on all relative tests. No naturality premise is needed for
the uniqueness of the local permutations. -/
def ofUnitTransform {α : Type u} (U : α → S.Opens) (hU : (⨆ a, U a) = ⊤)
    (σ : α → (J ≃ I))
    (F : ∀ T : Over S, (I → (Γ(T.left, ⊤))ˣ) → (J → (Γ(T.left, ⊤))ˣ))
    (h : ∀ a (T : Over S), Set.range T.hom ⊆ U a →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (σ a j)) :
    Datum S I J where
  Index := α
  opens := U
  covers := hU
  permutation := σ
  agree a b := permutation_eq_of_unitTests F (σ a) (σ b) (h a) (h b)

namespace Datum

variable (D : Datum S I J)

/-- The same local permutations with their directions reversed. -/
def symm : Datum S J I where
  Index := D.Index
  opens := D.opens
  covers := D.covers
  permutation a := (D.permutation a).symm
  agree a b h := congrArg Equiv.symm (D.agree a b h)

/-- Restriction of a coefficient section along an inclusion of opens. -/
abbrev restrict {U V : S.Opens} (h : U ≤ V) : Γ(S, V) →+* Γ(S, U) :=
  (S.presheaf.map (homOfLE h).op).hom

theorem restrict_restrict {U V W : S.Opens} (h : U ≤ V) (k : V ≤ W) (z : Γ(S, W)) :
    restrict h (restrict k z) = restrict (h.trans k) z := by
  change (S.presheaf.map (homOfLE k).op ≫ S.presheaf.map (homOfLE h).op) z = _
  rw [← Functor.map_comp]
  rfl

/-- Local reindexed sections agree on overlaps, including empty overlaps. -/
theorem compatible (z : I → Γ(S, ⊤)) (j : J) :
    TopCat.Presheaf.IsCompatible S.sheaf.1 D.opens
      (fun a => restrict le_top (z (D.permutation a j))) := by
  intro a b
  change restrict inf_le_left (restrict le_top (z (D.permutation a j))) =
    restrict inf_le_right (restrict le_top (z (D.permutation b j)))
  rw [restrict_restrict, restrict_restrict]
  cases isEmpty_or_nonempty ((D.opens a ⊓ D.opens b : S.Opens) : Scheme.{u}) with
  | inl h =>
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    exact (h.false ⟨x, hx⟩).elim
  | inr h => rw [D.agree a b h]

theorem existsUnique_section (z : I → Γ(S, ⊤)) (j : J) :
    ∃! t : Γ(S, ⊤), ∀ a, restrict (show D.opens a ≤ ⊤ from le_top) t =
      restrict le_top (z (D.permutation a j)) :=
  S.sheaf.existsUnique_gluing' D.opens ⊤ (fun _ => homOfLE le_top)
    D.covers.ge _ (D.compatible z j)

/-- The global section obtained by locally reindexing one coordinate. -/
def sectionMap (z : I → Γ(S, ⊤)) (j : J) : Γ(S, ⊤) :=
  (D.existsUnique_section z j).choose

@[simp] theorem sectionMap_restrict (z : I → Γ(S, ⊤)) (j : J) (a : D.Index) :
    restrict (show D.opens a ≤ ⊤ from le_top) (D.sectionMap z j) =
      restrict le_top (z (D.permutation a j)) :=
  (D.existsUnique_section z j).choose_spec.1 a

theorem sections_ext (s t : Γ(S, ⊤))
    (h : ∀ a, restrict (show D.opens a ≤ ⊤ from le_top) s = restrict le_top t) : s = t :=
  S.sheaf.eq_of_locally_eq' D.opens ⊤ (fun _ => homOfLE le_top) D.covers.ge s t h

/-- The coefficient-algebra homomorphism glued from the local reindexings. -/
def hom : (I → Γ(S, ⊤)) →ₐ[Γ(S, ⊤)] (J → Γ(S, ⊤)) where
  toFun := D.sectionMap
  map_one' := by
    funext j
    apply D.sections_ext
    intro a
    simp only [sectionMap_restrict, Pi.one_apply, map_one]
  map_mul' z w := by
    funext j
    apply D.sections_ext
    intro a
    simp only [sectionMap_restrict, Pi.mul_apply, map_mul]
  map_zero' := by
    funext j
    apply D.sections_ext
    intro a
    simp only [sectionMap_restrict, Pi.zero_apply, map_zero]
  map_add' z w := by
    funext j
    apply D.sections_ext
    intro a
    simp only [sectionMap_restrict, Pi.add_apply, map_add]
  commutes' r := by
    funext j
    apply D.sections_ext
    intro a
    change restrict le_top (D.sectionMap (algebraMap _ _ r) j) =
      restrict le_top r
    rw [sectionMap_restrict]
    rfl

@[simp] theorem hom_restrict (z : I → Γ(S, ⊤)) (j : J) (a : D.Index) :
    restrict (show D.opens a ≤ ⊤ from le_top) (D.hom z j) =
      restrict le_top (z (D.permutation a j)) :=
  D.sectionMap_restrict z j a

theorem left_inverse (z : I → Γ(S, ⊤)) : D.symm.hom (D.hom z) = z := by
  funext i
  apply D.sections_ext
  intro a
  calc
    _ = restrict (show D.opens a ≤ ⊤ from le_top)
        (D.hom z ((D.permutation a).symm i)) :=
      D.symm.hom_restrict (D.hom z) i a
    _ = restrict (show D.opens a ≤ ⊤ from le_top)
        (z (D.permutation a ((D.permutation a).symm i))) :=
      D.hom_restrict z ((D.permutation a).symm i) a
    _ = _ := by rw [Equiv.apply_symm_apply]

theorem right_inverse (z : J → Γ(S, ⊤)) : D.hom (D.symm.hom z) = z := by
  funext j
  apply D.sections_ext
  intro a
  rw [D.hom_restrict _ _ a]
  calc
    _ = restrict (show D.opens a ≤ ⊤ from le_top)
        (z ((D.permutation a).symm (D.permutation a j))) :=
      D.symm.hom_restrict z (D.permutation a j) a
    _ = _ := by rw [Equiv.symm_apply_apply]

/-- The actual global algebra equivalence induced by the locally constant
permutations. No affineness or nonemptiness of the base is needed. -/
def equiv : (I → Γ(S, ⊤)) ≃ₐ[Γ(S, ⊤)] (J → Γ(S, ⊤)) :=
  AlgEquiv.ofAlgHom D.hom D.symm.hom
    (AlgHom.ext D.right_inverse) (AlgHom.ext D.left_inverse)

@[simp] theorem equiv_restrict (z : I → Γ(S, ⊤)) (j : J) (a : D.Index) :
    restrict (show D.opens a ≤ ⊤ from le_top) (D.equiv z j) =
      restrict le_top (z (D.permutation a j)) :=
  D.hom_restrict z j a

end Datum
end LocalCoefficientReindexing
end Langlands.GroupScheme
