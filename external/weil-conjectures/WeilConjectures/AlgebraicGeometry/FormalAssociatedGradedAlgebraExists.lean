/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedMultiplication
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # The associated graded ideal algebra

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem graded_projection_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((formalAssociatedGradedπ I n).val.app (op U.1)) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have h := Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (SheafOfModules.unit X.ringCatSheaf)
  have : (Scheme.idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
    cases n with
    | zero => exact inferInstanceAs
        (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent
    | succ n => exact h.2.2.1 (n + 1) (Nat.succ_pos n)
  exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections I
    (Scheme.idealSheafPower I.toModulesι n).1).2.2.2.1 U).2.1

private theorem graded_heq_of_affine {X : Scheme.{u}} (B : ℕ → X.Modules)
    {m n : ℕ} (hmn : m = n) (U : X.Opens)
    (a : (B m).val.obj (op U)) (b : (B n).val.obj (op U))
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      HEq ((B m).val.map (homOfLE hVU).op a) ((B n).val.map (homOfLE hVU).op b)) :
    HEq a b := by
  subst n
  apply heq_of_eq
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(B m).presheaf, (B m).isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  · intro i
    exact eq_of_heq (h i.1 i.2)

private theorem power_injective {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (U : X.Opens) :
    Function.Injective ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U)) := by
  have hm : Mono (Scheme.idealSheafPower I.toModulesι n).2 := by
    induction n using Nat.twoStepInduction with
    | zero => simp only [Scheme.idealSheafPower]; infer_instance
    | one => simp only [Scheme.idealSheafPower]; infer_instance
    | more n _ ih =>
      change Mono (Scheme.idealModuleProductι I.toModulesι _ ≫ _)
      have : Mono (Scheme.idealModuleProductι I.toModulesι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).1) := by
        dsimp [Scheme.idealModuleProductι]
        infer_instance
      have := ih
      infer_instance
  have : Mono (Scheme.idealSheafPower I.toModulesι n).2.val :=
    (SheafOfModules.forget _).map_mono _
  exact (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U))))

private theorem quotient_heq_of_inclusion_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    {m n : ℕ} (hmn : m = n) (U : X.Opens)
    (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
    (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U))
    (h : (Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a =
      (Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b) :
    HEq ((formalAssociatedGradedπ I m).val.app (op U) a)
      ((formalAssociatedGradedπ I n).val.app (op U) b) := by
  subst n
  exact heq_of_eq (congrArg _ (power_injective I m U h))

/-- The associated graded ideal pieces carry the multiplication induced by representatives.
Source: Stacks Project, Lemma 087Z and Section 0EHN,
https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-associated-graded-algebra-exists).

Proof: On affine opens the ideal-power range formula identifies the inclusion of I^r
with I(U)^r; the quotient projection identifies B_r with I(U)^r/I(U)^(r+1).
Multiplication sends I(U)^m times I(U)^n into I(U)^(m+n). Changing either representative
changes the result by I(U)^(m+n+1), so it descends to a bilinear multiplication of the
quotients. For r=0 the power inclusion is the identity, and its quotient projection is
the unit. On smaller affine opens these maps commute with restrictions because the
inclusions and quotient projections do. The affine basis sheaf condition therefore
glues the maps to all opens: lift both quotient sections locally, multiply their
representatives, and glue the independent results. The unit and algebra laws are
checked after further local lifting of all the sections involved, where they are the
ring identities 1a=a, a1=a, (ab)c=a(bc), and ab=ba. The degree identifications give the
required HEq laws. For actual sections a and b of power ideals on any open, their
products locally lift uniquely through the monic inclusion of I^(m+n). Uniqueness
makes these lifts glue to the section c, and the constructed multiplication gives its
quotient class. This includes the empty open, the zero and unit ideals, and degree zero.
No finite-generation assertion or formal module is used. -/
theorem formalAssociatedGraded_algebra_exists {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    ∃ A : GradedSheafAlgebra (formalAssociatedGradedPiece I),
      A.unit = formalAssociatedGradedπ I 0 ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) := by
  obtain ⟨mu, hnat, hrep⟩ := formalAssociatedGraded_multiplication_exists I
  have hassoc : ∀ (l m n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I l).val.obj (op U))
      (b : (formalAssociatedGradedPiece I m).val.obj (op U))
      (c : (formalAssociatedGradedPiece I n).val.obj (op U)),
      HEq (mu (l + m) n U (mu l m U a b) c)
        (mu l (m + n) U a (mu m n U b c)) := by
    intro l m n U a b c
    apply graded_heq_of_affine (formalAssociatedGradedPiece I) (Nat.add_assoc l m n) U
    intro V hVU
    rw [hnat, hnat, hnat, hnat]
    obtain ⟨a', ha⟩ := graded_projection_surjective I l V
      ((formalAssociatedGradedPiece I l).val.map (homOfLE hVU).op a)
    obtain ⟨b', hb⟩ := graded_projection_surjective I m V
      ((formalAssociatedGradedPiece I m).val.map (homOfLE hVU).op b)
    obtain ⟨c', hc⟩ := graded_projection_surjective I n V
      ((formalAssociatedGradedPiece I n).val.map (homOfLE hVU).op c)
    rw [← ha, ← hb, ← hc]
    obtain ⟨ab, hab, hqab⟩ := hrep l m V.1 a' b'
    obtain ⟨bc, hbc, hqbc⟩ := hrep m n V.1 b' c'
    rw [hqab, hqbc]
    obtain ⟨abc, habc, hqabc⟩ := hrep (l + m) n V.1 ab c'
    obtain ⟨abc', habc', hqabc'⟩ := hrep l (m + n) V.1 a' bc
    rw [hqabc, hqabc']
    apply quotient_heq_of_inclusion_eq I (Nat.add_assoc l m n) V.1
    simp only [habc, habc', hab, hbc, id_eq, mul_assoc]
  have hcomm : ∀ (m n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I m).val.obj (op U))
      (b : (formalAssociatedGradedPiece I n).val.obj (op U)),
      HEq (mu m n U a b) (mu n m U b a) := by
    intro m n U a b
    apply graded_heq_of_affine (formalAssociatedGradedPiece I) (Nat.add_comm m n) U
    intro V hVU
    rw [hnat, hnat]
    obtain ⟨a', ha⟩ := graded_projection_surjective I m V
      ((formalAssociatedGradedPiece I m).val.map (homOfLE hVU).op a)
    obtain ⟨b', hb⟩ := graded_projection_surjective I n V
      ((formalAssociatedGradedPiece I n).val.map (homOfLE hVU).op b)
    rw [← ha, ← hb]
    obtain ⟨ab, hab, hqab⟩ := hrep m n V.1 a' b'
    obtain ⟨ba, hba, hqba⟩ := hrep n m V.1 b' a'
    rw [hqab, hqba]
    apply quotient_heq_of_inclusion_eq I (Nat.add_comm m n) V.1
    rw [hab, hba]
    change (@id Γ(X, V.1) _) * (@id Γ(X, V.1) _) = _
    exact mul_comm _ _
  have hone : ∀ (n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I n).val.obj (op U)),
      HEq (mu 0 n U ((formalAssociatedGradedπ I 0).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U))) a) a := by
    intro n U a
    apply graded_heq_of_affine (formalAssociatedGradedPiece I) (Nat.zero_add n) U
    intro V hVU
    rw [hnat]
    have hp := (formalAssociatedGradedπ I 0).val.naturality (homOfLE hVU).op
    have hp' := congrArg (fun f ↦ f (1 : X.ringCatSheaf.obj.obj (op U))) hp
    change (formalAssociatedGradedπ I 0).val.app (op V.1)
        ((Scheme.idealSheafPower I.toModulesι 0).1.val.map (homOfLE hVU).op
          (1 : X.ringCatSheaf.obj.obj (op U))) =
      (formalAssociatedGradedPiece I 0).val.map (homOfLE hVU).op
        ((formalAssociatedGradedπ I 0).val.app (op U)
          (1 : X.ringCatSheaf.obj.obj (op U))) at hp'
    rw [← hp']
    have hmap : (Scheme.idealSheafPower I.toModulesι 0).1.val.map (homOfLE hVU).op
        (1 : X.ringCatSheaf.obj.obj (op U)) =
        (1 : X.ringCatSheaf.obj.obj (op V.1)) := by
      change (X.presheaf.map (homOfLE hVU).op).hom 1 = 1
      exact map_one _
    rw [hmap]
    obtain ⟨a', ha⟩ := graded_projection_surjective I n V
      ((formalAssociatedGradedPiece I n).val.map (homOfLE hVU).op a)
    rw [← ha]
    obtain ⟨c, hc, hqc⟩ := hrep 0 n V.1 (1 : X.ringCatSheaf.obj.obj (op V.1)) a'
    rw [hqc]
    apply quotient_heq_of_inclusion_eq I (Nat.zero_add n) V.1
    change (Scheme.idealSheafPower I.toModulesι (0 + n)).2.val.app (op V.1) c =
      (1 : Γ(X, V.1)) *
        (@id Γ(X, V.1)
          ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op V.1) a')) at hc
    simpa only [one_mul, id_eq] using hc
  have hmulone : ∀ (n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I n).val.obj (op U)),
      HEq (mu n 0 U a ((formalAssociatedGradedπ I 0).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U)))) a := by
    intro n U a
    exact (hcomm n 0 U a _).trans (hone n U a)
  let A : GradedSheafAlgebra (formalAssociatedGradedPiece I) :=
    { mul := mu
      unit := formalAssociatedGradedπ I 0
      naturality := hnat
      assoc := hassoc
      comm := hcomm
      one_mul := hone
      mul_one := hmulone }
  exact ⟨A, rfl, hrep⟩

end AlgebraicGeometry
