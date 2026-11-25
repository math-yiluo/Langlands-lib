/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafSingletonRetraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafInsertionIdentities

/-! # Ordered insertion contracts the alternating Čech augmentation locally

Source: Stacks Project, Tags 02FU (local insertion) and 01FM (alternating comparison);
the ordered local insertion argument in
lem-pc-s3-alternating-cech-sheaf-local-contraction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-homotopy).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem localSource_isZero
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) (hk : k ≠ 0) :
    CategoryTheory.Limits.IsZero
      ((((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((CochainComplex.single₀ X.Modules).obj G).extend
            ComplexShape.embeddingUpNat)).X k) := by
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let S := (CochainComplex.single₀ X.Modules).obj G
  change CategoryTheory.Limits.IsZero (F.obj ((S.extend _).X k))
  apply F.map_isZero
  by_cases h : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = k
  · obtain ⟨n, hn⟩ := h
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 G n
      (by intro h; subst n; exact hk hn.symm)).of_iso (S.extendXIso _ hn)
  · exact S.isZero_extend_X _ k (by simpa using h)

private theorem localTarget_isZero_neg
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) (hk : k < 0) :
    CategoryTheory.Limits.IsZero
      ((((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)).X k) := by
  apply (Scheme.Modules.restrictFunctor (U i).ι).map_isZero
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  change (n : ℤ) = k at hn
  omega

private noncomputable def retractionToSupported
    {V : Type*} [Category V] [Preadditive V]
    (C S : CochainComplex V ℤ)
    (hC : CategoryTheory.Limits.IsZero (C.X (-1)))
    (hS : ∀ k : ℤ, k ≠ 0 → CategoryTheory.Limits.IsZero (S.X k))
    (π : C.X 0 ⟶ S.X 0) : C ⟶ S where
  f k := if hk : k = 0 then (C.XIsoOfEq hk).hom ≫ π ≫ (S.XIsoOfEq hk).inv else 0
  comm' j k hjk := by
    by_cases hk : k = 0
    · subst hk
      have hj : j = -1 := by change j + 1 = 0 at hjk; omega
      subst hj
      exact hC.eq_of_src _ _
    · exact (hS k hk).eq_of_tgt _ _

private theorem retractionToSupported_f_zero
    {V : Type*} [Category V] [Preadditive V]
    (C S : CochainComplex V ℤ)
    (hC : CategoryTheory.Limits.IsZero (C.X (-1)))
    (hS : ∀ k : ℤ, k ≠ 0 → CategoryTheory.Limits.IsZero (S.X k))
    (π : C.X 0 ⟶ S.X 0) :
    (retractionToSupported C S hC hS π).f 0 = π := by
  simp [retractionToSupported]

private noncomputable def homotopyOfInsertionIdentities
    {V : Type*} [Category V] [Preadditive V]
    {C : CochainComplex V ℤ} (f : C ⟶ C)
    (h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k)
    (hh : ∀ k : ℤ, f.f k + C.d k (k + 1) ≫ h k +
      (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
        h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k)) : Homotopy (𝟙 C) f where
  hom j k := if hjk : k + 1 = j then (C.XIsoOfEq hjk).inv ≫ h k else 0
  zero j k hjk := by
    change (if h : k + 1 = j then (C.XIsoOfEq h).inv ≫ _ else 0) = 0
    rw [dite_eq_right (by simpa using hjk)]
  comm k := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (k - 1) k from by change k - 1 + 1 = k; omega)]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp]
    simp only [dite_eq_left (show k - 1 + 1 = k by omega)]
    have ht : (C.XIsoOfEq (show k - 1 + 1 = k by omega)).inv =
        (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom := by
      simp only [HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToIso.hom]
    rw [ht]
    simp only [Category.assoc, HomologicalComplex.id_f, dite_true]
    rw [← hh k]
    abel

/-- On a member of the family, the extended augmentation is a homotopy equivalence.
Source: Stacks Project, Tag 02FU (insertion contraction), adapted to increasing
tuples as in Tag 01FM, and the local contraction paragraph of
lem-pc-s3-alternating-cech-sheaf-local-contraction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-homotopy).

Proof: On an open contained in U_i, project degree zero to the singleton i to define
the inverse of the augmentation. For a tuple t not containing i, insert i in its
unique increasing position a and take that coordinate with coefficient (-1)^a;
use zero when i already occurs. Since the test open lies in U_i, adjoining i does
not change its intersection with t, so the two section modules are canonically
identified. These operators are
linear and commute with restrictions, hence define morphisms of module presheaves.
In dh+hd the face deleting the inserted i is the identity; every other face cancels
with the same composite restriction bearing the opposite sign. When i is already
present, its deletion is the sole nonzero insertion contribution. The degree-zero
identity includes the singleton projection and the augmentation, whose reverse
composite is the identity. Sheafification and restriction are additive and preserve
these identities. This gives the inverse and the two homotopies for the augmentation
restricted to U_i. Extending by zero to integer degrees extends the inverse and both
homotopies and leaves the identities intact. No cover condition is used; if r=0
there is no index i and the assertion has no instances. -/
theorem alternatingCechSheafAugmentation_restrict_homotopyEquivalence
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    HomologicalComplex.homotopyEquivalences (U i).toScheme.Modules (ComplexShape.up ℤ)
      (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap
          (alternatingCechSheafAugmentation U G) ComplexShape.embeddingUpNat)) := by
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let S := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
  let a : S ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
      ComplexShape.embeddingUpNat)
  obtain ⟨π, hπ⟩ := alternatingCechSheafAugmentation_restrict_degreeZero_retraction U G i
  let q : C ⟶ S := retractionToSupported C S
    (localTarget_isZero_neg U G i (-1) (by omega)) (localSource_isZero U G i) π
  have haq : a ≫ q = 𝟙 S := by
    apply HomologicalComplex.Hom.ext
    funext k
    by_cases hk : k = 0
    · subst hk
      change a.f 0 ≫ (retractionToSupported C S _ _ π).f 0 = 𝟙 _
      rw [retractionToSupported_f_zero]
      exact hπ
    · exact (localSource_isZero U G i k hk).eq_of_src _ _
  obtain ⟨h, hh⟩ := alternatingCechSheafAugmentation_restrict_insertion_identities U G i q haq
  exact ⟨⟨a, q, Homotopy.ofEq haq, (homotopyOfInsertionIdentities (q ≫ a) h hh).symm⟩,
    rfl⟩

end AlgebraicGeometry
