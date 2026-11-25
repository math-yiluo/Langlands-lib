/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafSingletonContraction

/-! # Signed insertion identities on the local alternating complex

Source: Stacks Project, Tag 02FU, the insertion cancellation computation;
Tag 01FM for the ordered alternating convention.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-identities).
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

private theorem transportHomotopySource
    {V : Type*} [Category V] [Preadditive V] {C : CochainComplex V ℤ}
    {f g : C ⟶ C} (H : Homotopy f g) (i j k : ℤ) (h : i = j) :
    (C.XIsoOfEq h).hom ≫ H.hom j k = H.hom i k := by
  subst j
  simp

private theorem identitiesOfSupportedContraction
    {V : Type*} [Category V] [Preadditive V] (A C : CochainComplex V ℤ)
    (a : A ⟶ C) (hA : ∀ k : ℤ, k ≠ 0 → Limits.IsZero (A.X k))
    (hC : ∀ k : ℤ, k < 0 → Limits.IsZero (C.X k))
    (π : C.X 0 ⟶ A.X 0) (h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k)
    (hzero : C.d 0 (0 + 1) ≫ h 0 + π ≫ a.f 0 = 𝟙 (C.X 0))
    (hpos : ∀ k : ℤ, 0 < k → C.d k (k + 1) ≫ h k +
      (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
        h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k))
    (q : C ⟶ A) (haq : a ≫ q = 𝟙 A) :
    ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
      ∀ k : ℤ, (q ≫ a).f k + C.d k (k + 1) ≫ h k +
        (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
          h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
  let p : C ⟶ A := retractionToSupported C A
    (hC (-1) (by omega)) hA π
  have hh : ∀ k : ℤ, (p ≫ a).f k + C.d k (k + 1) ≫ h k +
      (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
        h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
    intro k
    rcases lt_trichotomy k 0 with hk | hk | hk
    · exact (hC k hk).eq_of_src _ _
    · subst k
      have hd : C.d (-1) 0 = 0 :=
        (hC (-1) (by omega)).eq_of_src _ _
      have hp : p.f 0 = π := retractionToSupported_f_zero C A _ _ π
      have hz : (C.XIsoOfEq (show (0 : ℤ) = 0 - 1 + 1 by omega)).hom ≫
          h (0 - 1) ≫ C.d (0 - 1) 0 = 0 := by
        change _ ≫ _ ≫ C.d (-1) 0 = 0
        rw [hd, Limits.comp_zero, Limits.comp_zero]
      rw [hz, add_zero, HomologicalComplex.comp_f, hp]
      exact (add_comm _ _).trans hzero
    · have hp : p.f k = 0 := (hA k (by omega)).eq_of_tgt _ _
      simpa only [HomologicalComplex.comp_f, hp, Limits.zero_comp, zero_add] using hpos k hk
  let H := homotopyOfInsertionIdentities (p ≫ a) h hh
  have heq : (p ≫ a) ≫ (q ≫ a) = p ≫ a := by
    rw [Category.assoc p a (q ≫ a), ← Category.assoc a q a, haq, Category.id_comp]
  let K := H.trans ((H.compRight (q ≫ a)).trans (Homotopy.ofEq heq)).symm
  refine ⟨fun k ↦ K.hom (k + 1) k, ?_⟩
  intro k
  have hk := K.comm k
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (k - 1) k from by
      change k - 1 + 1 = k
      omega)] at hk
  simpa only [← Category.assoc, transportHomotopySource, Category.id_comp,
    HomologicalComplex.id_f, add_comm, add_left_comm, add_assoc] using hk.symm

/-- Signed insertion contracts the complement of any chain retraction.
Source: Stacks Project, Tag 02FU, insertion and cancellation, adapted to increasing
indices as in Tag 01FM. The adjustment to an arbitrary retraction is elementary.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-identities).

Proof: First use the singleton projection p₀. On an open V contained in U i,
insert i in the increasing target tuple in its unique position b and multiply
by (-1)^b, or use zero if i already occurs. V intersect U i equals V, so insertion
uses the canonical identification of sections on equal intersections. The maps
are linear and natural. In dh+hd, deleting the inserted index gives the identity;
each other deletion pairs with insertion after deletion, with the same restriction
and opposite sign. If i was already present, only its deletion contributes.
In degree zero the identity is d₀h₀ = id - p₀a₀. Sheafification and restriction
are additive, so these equations remain valid for the constructed sheaf complex.
Extension by zero gives the same equations in integer degrees, with zero maps
in negative degrees. Now let q be any chain retraction and put p=q.f 0 and
δ=p-p₀. The retraction identities imply a₀δ=0. Therefore
δ=(id-p₀a₀)δ=d₀h₀δ. Replace h₀ by h₀-h₀δa₀, keeping every other h unchanged.
Then d₀h₀ becomes id-pa₀; h₀d₀ is unchanged because a₀d₀=0. Outside degree zero
q has zero components since its target is supported in degree zero. These are
exactly the displayed identities for all integer k. Empty intersections and an
empty U i cause no exception: the same linear identities hold in zero modules;
when r=0 there is no index i. -/
theorem alternatingCechSheafAugmentation_restrict_insertion_identities
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∀ q : C ⟶ A, a ≫ q = 𝟙 A →
      ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
        ∀ k : ℤ, (q ≫ a).f k + C.d k (k + 1) ≫ h k +
          (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
            h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
  dsimp only
  intro q haq
  obtain ⟨π, h, hzero, hpos⟩ :=
    alternatingCechSheafAugmentation_restrict_singleton_contraction U G i
  exact identitiesOfSupportedContraction _ _ _ (localSource_isZero U G i)
    (localTarget_isZero_neg U G i) π h hzero hpos q haq

end AlgebraicGeometry
