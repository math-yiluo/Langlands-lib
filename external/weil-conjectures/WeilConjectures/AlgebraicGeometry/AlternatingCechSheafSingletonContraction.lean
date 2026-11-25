/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafPositiveContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafDegreeZeroFactorization

/-! # The singleton signed insertion contraction

Source: Stacks Project, Tags 02FU and 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-contraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The singleton projection admits the signed insertion contraction.
Source: Stacks Project, Tag 02FU, insertion cancellation, with the increasing
convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-singleton-contraction).

Proof: On a test open V contained in U i, project degree zero onto the singleton i.
Since V intersect U i equals V, this gives a map to G on V. In all other degrees
use zero. For an increasing tuple not containing i, insert i in its unique
increasing position b and take the corresponding
coordinate with sign (-1)^b; for a tuple already containing i, use zero. Intersection
with U i does not change the test-open intersection, giving a canonical linear map.
These maps commute with restrictions. In the differential-insertion sum, deletion
of the inserted i contributes the identity, while every other deletion pairs with
insertion after deletion, with identical restriction and opposite sign. For tuples
containing i, only deleting that i contributes. In degree zero the remaining term
is singleton projection followed by augmentation. Restriction and module
sheafification commute by the canonical local
sheafification identification: the same compatible germs and their local gluing
compute both sides. Thus sheafify these natural linear maps on the restricted
site; additivity retains the equations. The sheafification
unit on G is inverse to the counit, so the augmented degree-zero term agrees with
the specified augmentation. Transport the nonnegative-degree maps across extendXIso. The degree-zero
equation includes the singleton projection and augmentation. In positive degrees
the two insertion terms sum to the identity; no equation in negative degree and
no adjustment to an arbitrary retraction is asserted here. Empty test opens have
zero modules; r=0 admits no i. -/
theorem alternatingCechSheafAugmentation_restrict_singleton_contraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∃ π : C.X 0 ⟶ A.X 0,
      ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
        (C.d (0 : ℤ) (0 + 1) ≫ h 0 + π ≫ a.f 0 = 𝟙 (C.X 0)) ∧
        ∀ k : ℤ, 0 < k → C.d k (k + 1) ≫ h k +
          (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
            h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
  let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
      ComplexShape.embeddingUpNat)
  obtain ⟨h, hpos⟩ := alternatingCechSheaf_restrict_positive_contraction U G i
  change ∀ k : ℤ, C.X (k + 1) ⟶ C.X k at h
  let d₀ := C.d 0 (0 + 1)
  let d₁ := C.d (0 + 1) ((0 + 1) + 1)
  have h1 : d₁ ≫ h (0 + 1) + h 0 ≫ d₀ = 𝟙 (C.X (0 + 1)) := by
    simpa [d₀, d₁, C, F] using hpos 1 (by norm_num)
  have hd : (𝟙 (C.X 0) - d₀ ≫ h 0) ≫ d₀ = 0 := by
    have he := congrArg (fun f ↦ d₀ ≫ f) h1
    have hs : d₀ ≫ d₁ = 0 := C.d_comp_d _ _ _
    simp only [Preadditive.comp_add, ← Category.assoc, hs,
      Limits.zero_comp, zero_add, Category.comp_id] at he
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
    rw [Category.assoc] at he
    exact sub_eq_zero.mpr he.symm
  obtain ⟨π, hπ⟩ := alternatingCechSheafAugmentation_restrict_degreeZero_factorization
    U G i (𝟙 (C.X 0) - d₀ ≫ h 0) (by simpa [d₀, C, F] using hd)
  refine ⟨π, h, ?_, hpos⟩
  change d₀ ≫ h 0 + π ≫ a.f 0 = 𝟙 (C.X 0)
  rw [hπ]
  abel

end AlgebraicGeometry
