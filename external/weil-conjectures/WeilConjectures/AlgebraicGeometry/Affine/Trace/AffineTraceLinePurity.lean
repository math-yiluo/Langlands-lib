/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLineLocalization
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# AffineTraceLinePurity
Source: blueprint proposition-purity-vector-bundles, Steps 5(b) and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem splitTraceIsIso {C : Type u} [Category.{v} C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasZeroObject C] [Pretriangulated C]
    {X Y B K : C} (a : X ⟶ Y) (r : Y ⟶ B) (w : B ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a r w ∈ distTriang C) (b : B ⊞ K ≅ Y) (t : Y ⟶ K)
    (hr : b.hom ≫ r = biprod.fst) (ht : b.hom ≫ t = biprod.snd) :
    IsIso (a ≫ t) := by
  have hr' : b.inv ≫ biprod.fst = r := by
    rw [← hr, Iso.inv_hom_id_assoc]
  have ht' : b.inv ≫ biprod.snd = t := by
    rw [← ht, Iso.inv_hom_id_assoc]
  have ha : a ≫ b.inv ≫ biprod.fst = 0 := by
    rw [hr']
    exact comp_distTriang_mor_zero₁₂ _ hT
  have hrw : r ≫ w = 0 := comp_distTriang_mor_zero₂₃ _ hT
  have hw : w = 0 := by
    calc
      w = (biprod.inl ≫ (b.hom ≫ r)) ≫ w := by rw [hr]; simp
      _ = biprod.inl ≫ b.hom ≫ (r ≫ w) := by simp only [Category.assoc]
      _ = 0 := by rw [hrw]; simp
  let φ : Triangle.mk a r w ⟶ binaryBiproductTriangle K B :=
    { hom₁ := a ≫ t
      hom₂ := b.inv ≫ (biprod.braiding B K).hom
      hom₃ := 𝟙 B
      comm₁ := by
        apply biprod.hom_ext
        · simp [Category.assoc, ht']
        · simp [Category.assoc, ha]
      comm₂ := by
        change r ≫ 𝟙 B = (b.inv ≫ (biprod.braiding B K).hom) ≫ biprod.snd
        simp only [Category.comp_id, Category.assoc, biprod.braiding_hom, biprod.lift_snd, hr']
      comm₃ := by simp [hw] }
  exact isIso₁_of_isIso₂₃ φ hT (binaryBiproductTriangle_distinguished K B)
    (by change IsIso (b.inv ≫ (biprod.braiding B K).hom); infer_instance)
    (by change IsIso (𝟙 B); infer_instance)
private theorem splitTraceIsIsoOfSection {C : Type u} [Category.{v} C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasZeroObject C] [Pretriangulated C]
    {X Y B K : C} (a : X ⟶ Y) (r : Y ⟶ B) (w : B ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a r w ∈ distTriang C) (b : B ⊞ K ≅ Y) (t : Y ⟶ K)
    (hr : biprod.inl ≫ b.hom ≫ r = 𝟙 B) (ht : b.hom ≫ t = biprod.snd) :
    IsIso (a ≫ t) := by
  let q : K ⟶ B := biprod.inr ≫ b.hom ≫ r
  have hformula : b.hom ≫ r = biprod.fst + biprod.snd ≫ q := by
    apply biprod.hom_ext'
    · simpa [Category.assoc] using hr
    · simp [q]
  let e : B ⊞ K ≅ B ⊞ K :=
    { hom := biprod.lift (biprod.fst - biprod.snd ≫ q) biprod.snd
      inv := biprod.lift (biprod.fst + biprod.snd ≫ q) biprod.snd
      hom_inv_id := by
        apply biprod.hom_ext <;>
          simp [Category.assoc, comp_add]
      inv_hom_id := by
        apply biprod.hom_ext <;>
          simp [Category.assoc, comp_sub] }
  apply splitTraceIsIso a r w hT (e ≪≫ b) t
  · dsimp only [Iso.trans_hom]
    rw [Category.assoc, hformula]
    simp [e, comp_add, sub_add_cancel]
  · dsimp only [Iso.trans_hom]
    rw [Category.assoc, ht]
    simp [e]

/-- The affine-line counit is invertible on every coefficient complex.
Source: blueprint lemma-integral-linear-character--1, proof steps 2--6
(blueprint: lem-amb-affine-trace-line-counit-iso).

Proof: apply open-closed localization to the shifted Tate line on the projective
line, then apply proper direct image. The closed vertex is the shifted Tate line
on the base, because the infinity section is finite and its composite with the
projection is identity. In the normalized projective-line decomposition the map
to this vertex has first component identity. The trace is second projection.
An elementary triangular change of the two summands makes restriction first
projection while leaving trace second projection. A morphism to the split
distinguished triangle then makes the restricted trace an isomorphism.
The composite adjunction identifies this map
with its counit at the tensor unit. For arbitrary K, open tensor comparison and
the proper projection formula identify the counit with K tensor this trace.
The open comparison commutes with counits by the adjunction triangle identity;
proper projection naturality gives the remaining square. Tensoring preserves
isomorphisms. This also covers unbounded K, the empty base, and the zero ring. -/
theorem affineTraceLineCounit_isIso (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (D : OrdinaryFiniteP1Datum A N hA t S hS) (K : DerivedCategoryModule A S) :
    IsIso ((affineTraceLineAdjunction A N hA t S hS D).counit.app K) := by
  obtain ⟨B, r, w, b, hT, hr, ht⟩ := affineTraceLine_localization A N hN hA t S hS D K
  unfold affineTraceLineAdjunction
  rw [affineTraceComposeAdjunction_counit]
  exact splitTraceIsIsoOfSection _ r w hT b (D.adjunction.counit.app K) hr ht

end AlgebraicGeometry.Etale
