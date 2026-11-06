import Langlands.GroupScheme.SpecialLinearBinaryRootGroups
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Closed additive root subgroups of the binary special linear scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

section Matrices

variable {A : Type u} [CommRing A] {i j : Fin 2} (hij : i ≠ j)

/-- A transvection is determined by its off-diagonal coefficient. -/
theorem transvectionHom_injective :
    Function.Injective (transvectionHom (A := A) hij) := by
  intro a b h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) A => g i j) h
  simpa [transvectionHom, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.single_apply, Matrix.one_apply, hij] using h'

/-- The root subgroup on matrices is characterized by its complementary entries. -/
theorem mem_transvection_range (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    g ∈ (transvectionHom hij).range ↔
      ∀ r s, (r ≠ i ∨ s ≠ j) → g r s = (1 : Matrix (Fin 2) (Fin 2) A) r s := by
  constructor
  · rintro ⟨a, rfl⟩ r s h
    simp only [transvectionHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply]
    rw [Matrix.single_apply, ite_eq_right (by tauto), add_zero]
  · intro h
    refine ⟨Multiplicative.ofAdd (g i j), ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro r s
    by_cases hr : r = i
    · subst r
      by_cases hs : s = j
      · subst s
        simp [transvectionHom, Matrix.SpecialLinearGroup.transvection_coe, hij]
      · simpa [transvectionHom, Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.single_apply, Ne.symm hs] using (h i s (Or.inr hs)).symm
    · simpa [transvectionHom, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.single_apply, Ne.symm hr] using (h r s (Or.inl hr)).symm

end Matrices

section ClosedRepresentatives

variable (R : CommRingCat.{u}) {i j : Fin 2} (hij : i ≠ j)

/-- The ideal imposing the identity entries away from the root position. -/
def rootIdeal (i j : Fin 2) : Ideal (CoordinateRing (Fin 2) R) :=
  Ideal.span {b | ∃ r s : Fin 2, (r ≠ i ∨ s ≠ j) ∧
    quotient (Fin 2) R (X (r, s)) -
      algebraMap R (CoordinateRing (Fin 2) R) ((1 : Matrix (Fin 2) (Fin 2) R) r s) = b}

/-- The transvection range is cut out by the complementary entry equations. -/
theorem isCutOutBy_rootIdeal :
    Corepresented.IsCutOutBy (corepresentableBy (Fin 2) R)
      (fun A => (transvectionHom (A := A) hij).range) (rootIdeal R i j) := by
  intro A g
  change Matrix.SpecialLinearGroup (Fin 2) A at g
  change g ∈ (transvectionHom hij).range ↔
    ∀ b ∈ rootIdeal R i j, classify (R := R) g b = 0
  rw [mem_transvection_range]
  have h1 : ∀ r s : Fin 2,
      algebraMap R A ((1 : Matrix (Fin 2) (Fin 2) R) r s) =
        (1 : Matrix (Fin 2) (Fin 2) A) r s := by
    intro r s
    exact congrFun (congrFun (map_one (algebraMap R A).mapMatrix) r) s
  constructor
  · intro hg b hb
    have hle : rootIdeal R i j ≤ RingHom.ker (classify (R := R) g) := by
      rw [rootIdeal, Ideal.span_le]
      rintro _ ⟨r, s, hrs, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, classify_entry,
        AlgHom.commutes, h1, hg r s hrs, sub_self]
    exact hle hb
  · intro h r s hrs
    have hz := h _ (Ideal.subset_span ⟨r, s, hrs, rfl⟩)
    rwa [map_sub, classify_entry, AlgHom.commutes, h1, sub_eq_zero] at hz

/-- The affine closed representative of a transvection root subgroup. -/
abbrev closedScheme : GroupScheme (Spec R) :=
  Corepresented.cutGroupScheme (isCutOutBy_rootIdeal R hij)

/-- Its closed inclusion into the binary special linear scheme. -/
abbrev closedInclusion : closedScheme R hij ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  Corepresented.cutHom (isCutOutBy_rootIdeal R hij)

/-- Test points of the closed representative are precisely the transvection range. -/
def closedPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (closedScheme R hij).X) ≃*
      (transvectionHom (A := Γ(T.left, ⊤)) hij).range :=
  Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_rootIdeal R hij)) T

theorem pointsEquiv_closedInclusion (T : Over (Spec R))
    (x : T ⟶ (closedScheme R hij).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (closedInclusion R hij).hom.hom) =
      (closedPointsEquiv R hij T x).val :=
  Corepresented.groupSchemeMap_points _ _ _ x

/-- The sole coordinate identifies points of the affine line with its coefficient group. -/
def coefficientEquiv (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R 1).X) ≃* Multiplicative Γ(T.left, ⊤) :=
  (VectorGroup.coordinates R 1 T).trans
    { toFun := fun a => Multiplicative.ofAdd (a.toAdd 0)
      invFun := fun a => Multiplicative.ofAdd (fun _ => a.toAdd)
      left_inv := by
        intro a
        apply Multiplicative.ext
        funext r
        exact congrArg a.toAdd (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

/-- The closed representative has exactly the points of the actual additive root group. -/
def rootClosedPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R 1).X) ≃* (T ⟶ (closedScheme R hij).X) :=
  ((coefficientEquiv R T).trans (MonoidHom.ofInjective
    (transvectionHom_injective (A := Γ(T.left, ⊤)) hij))).trans
      (closedPointsEquiv R hij T).symm

theorem rootClosedPointsEquiv_inclusion (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    rootClosedPointsEquiv R hij T x ≫ (closedInclusion R hij).hom.hom =
      x ≫ (rootMap R hij).hom.hom := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
  rw [pointsEquiv_closedInclusion, pointsEquiv_rootMap]
  simp only [rootClosedPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem rootClosedPointsEquiv_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    rootClosedPointsEquiv R hij T' (a ≫ x) =
      a ≫ rootClosedPointsEquiv R hij T x := by
  apply (cancel_mono (closedInclusion R hij).hom.hom).mp
  simp only [Category.assoc, rootClosedPointsEquiv_inclusion]

/-- The actual affine-line root group is isomorphic to its closed representative. -/
def rootClosedIso : VectorGroup.groupScheme R 1 ≅ closedScheme R hij :=
  isoOfPoints (rootClosedPointsEquiv R hij) (rootClosedPointsEquiv_naturality R hij)

/-- The actual root map is the closed inclusion after this explicit isomorphism. -/
theorem rootClosedIso_hom_comp :
    (rootClosedIso R hij).hom ≫ closedInclusion R hij = rootMap R hij := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, rootClosedIso, comp_isoOfPoints_hom,
    rootClosedPointsEquiv_inclusion]

/-- Each actual additive root homomorphism is a closed subgroup inclusion. -/
theorem isClosedSubgroup_rootMap : IsClosedSubgroup (rootMap R hij) := by
  rw [← rootClosedIso_hom_comp]
  change IsClosedImmersion
    (((rootClosedIso R hij).hom ≫ closedInclusion R hij).hom.hom.left)
  rw [Grp.comp_hom_hom, Over.comp_left]
  infer_instance

/-- On every test scheme, factoring through a root map is an entrywise condition. -/
theorem mem_range_rootMap {T : Over (Spec R)}
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :
    x ∈ (SubgroupFunctor.range (rootMap R hij)).carrier T ↔
      ∀ r s, (r ≠ i ∨ s ≠ j) →
        SpecialLinear.pointsEquiv (Fin 2) R T x r s =
          (1 : Matrix (Fin 2) (Fin 2) Γ(T.left, ⊤)) r s := by
  rw [← rootClosedIso_hom_comp, SubgroupFunctor.range_iso_comp,
    Corepresented.range_cutHom]
  exact mem_transvection_range hij _

end ClosedRepresentatives

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
