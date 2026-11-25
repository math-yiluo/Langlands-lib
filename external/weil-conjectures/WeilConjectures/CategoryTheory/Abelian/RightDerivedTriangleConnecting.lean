/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDerivedTriangleComparison

/-!
# Right-derived connecting maps and the derived triangle

Source: Stacks Project, Derived Categories, Tags 05TE and 015B
(blueprint: lem-sc-p1-right-derived-triangle-connecting).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The horseshoe connecting morphisms for a left exact functor agree, under the
canonical single-object identifications, with the connecting morphisms in the
homology sequence of the image of the distinguished triangle of a short exact
sequence.

Source: Stacks Project, Derived Categories, Tags 05TE and 015B
(blueprint: lem-sc-p1-right-derived-triangle-connecting).

The first conjunct specifies that `G.delta` is the horseshoe boundary, using exactly
all the compatible resolutions and the comparison of
`exists_horseshoe_rightDerived_deltaFunctor`; it does not leave `G` arbitrary.
The second conjunct compares these same boundary maps with the derived triangle.

Proof:
1. Choose a horseshoe resolution using lem-weil-pbc-horseshoe-delta-functor and
lem-weil-pbc-injective-resolution-ses. Split each row because its first term is
injective. By lem-weil-pbc-degreewise-split-connecting-morphism its chain boundary
is π d s; lem-weil-pbc-complex-ses-homology-long-exact constructs the horseshoe maps.
2. Use lem-weil-pbc-degreewise-split-derived-triangle to identify the split triangle
with the cone triangle, with third cone map -p, fixing the sign. By
lem-weil-pbc-complex-ses-connecting-formula the boundary on a cocycle z is π d s z.
3. The horseshoe augmentations are compatible quasi-isomorphisms, by
def-sp-injective-resolutions and lem-weil-pbc-horseshoe-delta-functor. Transport
its distinguished triangle through them. The group Hom(A[0][1], C[0]) vanishes:
lem-weil-pbc-bounded-below-injectives-kinjective and lem-weil-pbc-kinjective-hom-derived
compute it in the homotopy category, where all chain maps are zero by degree bounds.
By lem-weil-pbc-triangle-morphism-extension(3), the transported third map is the
unique boundary of lem-sf-derived-ses-triangle, with no additional sign.
4. Compute the triangulated functor of lem-weil-pbc-derived-direct-image-triangulated
on these bounded-below injective resolutions. The shifted resolution has differential
-d, so its comparison shift isomorphism is the identity, and the third map is v(π d s).
The boundary of lem-sf-derived-homology-long-exact therefore agrees on cocycles with
the horseshoe boundary. Transport along the canonical identifications of
lem-sp-derived-functor-single-identification to obtain the displayed equality.
-/
theorem rightDerived_triangle_connecting
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] :
    ∃ (G : CohomologicalDeltaFunctor A B)
      (hF : G.F = (fun n : ℕ ↦ v.rightDerived n)),
      (∀ (S : ShortComplex A) (hS : S.ShortExact)
        (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
        (IC : InjectiveResolution S.X₃)
        (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
        (hαβ : α ≫ β = 0)
        (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
        (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
        (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact),
        ∃ hvH : ((ShortComplex.mk α β hαβ).map
          (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact,
          ∀ n : ℕ,
            G.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) =
              eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫
                (IC.isoRightDerivedObj v n).hom ≫ hvH.δ n (n + 1) rfl ≫
                  (IA.isoRightDerivedObj v (n + 1)).inv) ∧
      (∀ (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ),
        G.delta S hS n ≫
            eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) ≫
            (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₁ (n + 1)).inv =
          eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫
            (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₃ n).inv ≫
            DerivedCategory.HomologySequence.δ
              ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
                hS.singleTrianglePlus)
              (n : ℤ) (n + 1) (by omega)) := by
  obtain ⟨G, hF, hG⟩ := exists_horseshoe_rightDerived_deltaFunctor v
  refine ⟨G, hF, hG, ?_⟩
  intro S hS n
  obtain ⟨IA, IB, IC, α, β, hιA, hιB, hαβ, hrows⟩ :=
    InjectiveResolution.exists_horseshoe_resolutions S hS
  have hH k := (hrows k).1
  obtain ⟨hvH, hδ⟩ := hG S hS IA IB IC α β hαβ hιA hιB hH
  obtain ⟨hExt, hboundary⟩ := natComplex_boundary_derived _ hvH
  obtain ⟨τ, hτ₁, hτ₃⟩ := horseshoe_derived_triangle_comparison v S hS
    IA IB IC α β hαβ hιA hιB hH hvH hExt
  have hnat := (DerivedCategory.homologyFunctor B 0).homologySequenceδ_naturality
    τ (n : ℤ) (n + 1) (by omega)
  symm at hnat
  change DerivedCategory.HomologySequence.δ _ (n : ℤ) (n + 1) rfl ≫
      (DerivedCategory.homologyFunctor B (n + 1)).map τ.hom₁ =
    (DerivedCategory.homologyFunctor B (n : ℤ)).map τ.hom₃ ≫
      DerivedCategory.HomologySequence.δ _ (n : ℤ) (n + 1) rfl at hnat
  have hτ₁n := hτ₁ (n + 1)
  have hcompare := congrArg
    (fun f ↦ f ≫ (natComplexDerivedHomologyIso
      ((v.mapHomologicalComplex _).obj IA.cocomplex) (n + 1)).hom) hnat
  simp only [Category.assoc] at hcompare ⊢
  erw [hτ₁n, hboundary n] at hcompare
  erw [← Category.assoc ((DerivedCategory.homologyFunctor B (n : ℤ)).map τ.hom₃),
    hτ₃ n] at hcompare
  rw [← Category.assoc, hδ n]
  apply (cancel_mono (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso
    S.X₁ (n + 1)).hom).1
  apply (cancel_mono (IA.isoRightDerivedObj v (n + 1)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc] at hcompare
  erw [hcompare]
  simp only [Iso.inv_hom_id_assoc]

end CategoryTheory
