/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Natural identifications from multiplication triangles. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard

/-- The kernel, signed triangle, and transition property as a folded proposition.
This definition chooses no objects or morphisms. -/
@[irreducible] def KernelTriangleData
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (ℓ : ℕ) (M : A) (R : ℕᵒᵖ ⥤ A) (P : ℕ → A)
    (rootMap : ∀ n, R.obj (op n) ⟶ P n)
    (q : ∀ n, ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj (P n))⟦(2 : ℤ)⟧) : Prop :=
  ∃ (r : ∀ n, R.obj (op n) ≅ P n) (i : ∀ n, P n ⟶ M),
    (∀ n, (r n).hom = rootMap n) ∧ (∀ n, Mono (i n)) ∧
    (∀ n, Pretriangulated.Triangle.mk
      (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)) (q n)
      (((DerivedCategory.singleFunctor A 0).map (-i n))⟦(2 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M)) ∈ distTriang (DerivedCategory A)) ∧
    ∀ n, R.map (homOfLE (Nat.le_succ n)).op ≫ (r n).hom ≫ i n =
      (r (n + 1)).hom ≫ i (n + 1) ≫ (ℓ • 𝟙 M)

/-- The ordinary coefficient lift and its normalization, as a folded proposition.
No derived category or choice of data occurs in this definition. -/
@[irreducible] def FiniteKernelLift
    {A B : Type*} [Category A] [Category B] (U : B ⥤ A) (R : ℕᵒᵖ ⥤ A)
    (C : ℕ → Type*) [∀ n, Category (C n)]
    (TateF : ∀ n, C n ⥤ B) (V : ∀ n, C n ⥤ A) (P : ∀ n, C n)
    (σ : ∀ n, V n ≅ TateF n ⋙ U)
    (rootMap : ∀ n, R.obj (op n) ⟶ (V n).obj (P n))
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ R) →
      ∀ n, (H.obj (op n) ≅ (TateF n).obj (P n)) → Prop) : Prop :=
  ∀ (r : ∀ n, R.obj (op n) ≅ (V n).obj (P n)),
    (∀ n, (r n).hom = rootMap n) → ∀ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ U ≅ R)
    (a : ∀ n, U.obj (H.obj (op n)) ≅ (V n).obj (P n)),
    (∀ n, roots.hom.app (op n) ≫ (r n).hom = (a n).hom) →
    ∃ t : ∀ n, H.obj (op n) ≅ (TateF n).obj (P n),
      (∀ n, rootNorm H roots n (t n)) ∧
      ∀ n, U.map (t n).hom ≫ (σ n).inv.app (P n) = (a n).hom

/-- Comparing two multiplication triangles gives a genuine sheaf isomorphism,
with both the unit and the abelian boundary fixed. -/
private theorem pure_triangle_comparison
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (F : A ⥤ DerivedCategory A) [F.Full] [F.Faithful]
    {X : DerivedCategory A} (m : X ⟶ X) {N P M : A}
    (a : X ⟶ F.obj N) (q : X ⟶ F.obj P)
    (d : N ⟶ M) (j : P ⟶ M) (c : F.obj M ≅ X⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk m a (F.map d ≫ c.hom) ∈
      distTriang (DerivedCategory A))
    (hK : Pretriangulated.Triangle.mk m q (F.map j ≫ c.hom) ∈
      distTriang (DerivedCategory A)) :
    ∃ e : N ≅ P, a ≫ F.map e.hom = q ∧ e.hom ≫ j = d := by
  let T := Pretriangulated.Triangle.mk m a (F.map d ≫ c.hom)
  let K := Pretriangulated.Triangle.mk m q (F.map j ≫ c.hom)
  let z : T ≅ K := Pretriangulated.isoTriangleOfIso₁₂ T K hT hK
    (Iso.refl X) (Iso.refl X) (by
      dsimp only [T, K, Pretriangulated.Triangle.mk, Iso.refl_hom]
      simp only [Category.comp_id, Category.id_comp])
  have hz₁ : z.hom.hom₁ = 𝟙 X := by rfl
  have hz₂ : z.hom.hom₂ = 𝟙 X := by rfl
  let e := F.preimageIso (Pretriangulated.Triangle.π₃.mapIso z)
  have he : F.map e.hom = z.hom.hom₃ := F.map_preimage _
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    have h := z.hom.comm₂
    dsimp only [T, K, Pretriangulated.Triangle.mk] at h
    simpa only [hz₂,
      Category.id_comp] using h
  · apply F.map_injective
    rw [F.map_comp, he]
    apply (cancel_mono c.hom).1
    have h := z.hom.comm₃
    dsimp only [T, K, Pretriangulated.Triangle.mk] at h
    refine (Category.assoc _ _ _).trans ?_
    simpa only [hz₁,
      (shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id, Category.comp_id,
      Category.assoc] using h.symm

/-- Two multiplication triangles with monic kernel inclusions determine a
natural roots comparison and fix the second arrow at every level. -/
theorem pure_kernel_triangle_comparison
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A] [Category B]
    (U : B ⥤ A) (H : ℕᵒᵖ ⥤ B) (M : A) (R : ℕᵒᵖ ⥤ A) (P : ℕ → A)
    (r : ∀ n, R.obj (op n) ≅ P n) (i : ∀ n, P n ⟶ M) (hi : ∀ n, Mono (i n))
    (ℓ : ℕ)
    (hrt : ∀ n, R.map (homOfLE (Nat.le_succ n)).op ≫ (r n).hom ≫ i n =
      (r (n + 1)).hom ≫ i (n + 1) ≫ (ℓ • 𝟙 M))
    (F : A ⥤ DerivedCategory A) [F.Full] [F.Faithful]
    (X : DerivedCategory A) (c : F.obj M ≅ X⟦(1 : ℤ)⟧)
    (m : ℕ → (X ⟶ X))
    (α : ∀ n, X ⟶ F.obj (U.obj (H.obj (op n))))
    (q : ∀ n, X ⟶ F.obj (P n)) (d : ∀ n, U.obj (H.obj (op n)) ⟶ M)
    (hd : ∀ n, Pretriangulated.Triangle.mk (m n) (α n) (F.map (d n) ≫ c.hom) ∈
      distTriang (DerivedCategory A))
    (hK : ∀ n, Pretriangulated.Triangle.mk (m n) (q n) (F.map (-i n) ≫ c.hom) ∈
      distTriang (DerivedCategory A))
    (hdt : ∀ n, U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ d n =
      d (n + 1) ≫ (ℓ • 𝟙 M)) :
    ∃ (roots : H ⋙ U ≅ R) (a : ∀ n, U.obj (H.obj (op n)) ≅ P n),
      (∀ n, roots.hom.app (op n) ≫ (r n).hom = (a n).hom) ∧
      ∀ n, α n ≫ F.map (a n).hom = q n := by
  have hcomp (n : ℕ) : ∃ a : U.obj (H.obj (op n)) ≅ P n,
      α n ≫ F.map a.hom = q n ∧ a.hom ≫ i n = -d n := by
    obtain ⟨a, ha, hb⟩ := pure_triangle_comparison F (m n) (α n) (q n)
      (d n) (-i n) c (hd n) (hK n)
    refine ⟨a, ha, ?_⟩
    simpa only [Preadditive.comp_neg, neg_neg] using congrArg Neg.neg hb
  choose a hau hai using hcomp
  let e (n : ℕ) : U.obj (H.obj (op n)) ≅ R.obj (op n) := a n ≪≫ (r n).symm
  let j (n : ℕ) : R.obj (op n) ⟶ M := (r n).hom ≫ i n
  have hej (n : ℕ) : (e n).hom ≫ j n = -d n := by
    dsimp only [e, j, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Iso.inv_hom_id_assoc, hai]
  have hen (n : ℕ) : (H ⋙ U).map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ R.map (homOfLE (Nat.le_succ n)).op := by
    let := hi n
    have : Mono (j n) := by dsimp only [j]; infer_instance
    apply (cancel_mono (j n)).1
    rw [Category.assoc, hej]
    change U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ (-d n) = _
    rw [Preadditive.comp_neg, hdt]
    have hj : R.map (homOfLE (Nat.le_succ n)).op ≫ j n =
        j (n + 1) ≫ (ℓ • 𝟙 M) := by
      simpa only [j, Category.assoc] using hrt n
    rw [Category.assoc, hj, ← Category.assoc, hej, Preadditive.neg_comp]
  let φ : H ⋙ U ⟶ R := NatTrans.ofOpSequence (fun n ↦ (e n).hom) hen
  have : ∀ x : ℕᵒᵖ, IsIso (φ.app x) := fun x ↦ by
    change IsIso (e x.unop).hom
    infer_instance
  have : IsIso φ := NatIso.isIso_of_isIso_app φ
  let roots : H ⋙ U ≅ R := asIso φ
  refine ⟨roots, a, ?_, hau⟩
  intro n
  change ((a n).hom ≫ (r n).inv) ≫ (r n).hom = (a n).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.ProEtale
