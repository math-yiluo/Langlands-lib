/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.KFlatTensorModelNaturalComparison
import WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence

/-! # Coherent tensor-model comparisons under open restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-sc-tensor-model-restriction-comparisons).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transport_model_comparisons
    {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory D] [MonoidalCategory E]
    (Q B : C ⥤ D) (R : D ⥤ E) (K A : D)
    (H : Dᵒᵖ × D ⥤ D) (HU : Eᵒᵖ × E ⥤ E)
    (eX : ∀ L N M : D, (L ⟶ H.obj (op N, M)) ≃ (L ⊗ N ⟶ M))
    (eU : ∀ L N M : E, (L ⟶ HU.obj (op N, M)) ≃ (L ⊗ N ⟶ M))
    (a : K ≅ A) (hm : Nonempty (Q ⋙ (curriedTensor D).obj K ≅ B))
    (hs : ∃ s : ∀ L N : D, L ⊗ N ≅ N ⊗ L,
      ∀ L L' N N' (f : L ⟶ L') (g : N ⟶ N'),
        (f ⊗ₘ g) ≫ (s L' N').hom = (s L N).hom ≫ (g ⊗ₘ f))
    (hr : ∃ (t : ∀ L N : D, R.obj (L ⊗ N) ≅ R.obj L ⊗ R.obj N)
      (h : ∀ N M, R.obj (H.obj (op N, M)) ≅ HU.obj (op (R.obj N), R.obj M)),
      (∀ L L' N N' (f : L ⟶ L') (g : N ⟶ N'),
        R.map (f ⊗ₘ g) ≫ (t L' N').hom =
          (t L N).hom ≫ (R.map f ⊗ₘ R.map g)) ∧
      (∀ L N M (ξ : L ⟶ H.obj (op N, M)),
        (t L N).hom ≫ eU (R.obj L) (R.obj N) (R.obj M)
          (R.map ξ ≫ (h N M).hom) = R.map (eX L N M ξ))) :
    ∃ (c : ∀ J, B.obj J ≅ Q.obj J ⊗ A)
      (d : ∀ J, R.obj (B.obj J) ≅ R.obj (Q.obj J) ⊗ R.obj A)
      (h : ∀ M, R.obj (H.obj (op A, M)) ≅ HU.obj (op (R.obj A), R.obj M)),
      (∀ J J' (u : J ⟶ J'), R.map (B.map u) ≫ (d J').hom =
        (d J).hom ≫ (R.map (Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ J M (ξ : Q.obj J ⟶ H.obj (op A, M)),
        (d J).hom ≫ eU (R.obj (Q.obj J)) (R.obj A) (R.obj M)
          (R.map ξ ≫ (h M).hom) = R.map ((c J).hom ≫ eX (Q.obj J) A M ξ)) := by
  obtain ⟨m⟩ := hm
  obtain ⟨s, hs⟩ := hs
  let c := fun J ↦ (m.app J).symm ≪≫ tensorIso a (Iso.refl (Q.obj J)) ≪≫ s A (Q.obj J)
  have hc (J J' : C) (u : J ⟶ J') :
      B.map u ≫ (c J').hom = (c J).hom ≫ (Q.map u ⊗ₘ 𝟙 A) := by
    have hn := m.inv.naturality u
    change B.map u ≫ (m.app J').inv = (m.app J).inv ≫ (K ◁ Q.map u) at hn
    simp only [← id_tensorHom] at hn
    simp only [c, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
    rw [← Category.assoc, hn, Category.assoc]
    have he : (𝟙 K ⊗ₘ Q.map u) ≫ (a.hom ⊗ₘ 𝟙 (Q.obj J')) =
        (a.hom ⊗ₘ 𝟙 (Q.obj J)) ≫ (𝟙 A ⊗ₘ Q.map u) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [← Category.assoc (𝟙 K ⊗ₘ Q.map u) (a.hom ⊗ₘ 𝟙 (Q.obj J'))
      (s A (Q.obj J')).hom, he, Category.assoc,
      hs A A (Q.obj J) (Q.obj J') (𝟙 A) (Q.map u)]
  obtain ⟨t, h, ht, hh⟩ := hr
  let d := fun J ↦ R.mapIso (c J) ≪≫ t (Q.obj J) A
  refine ⟨c, d, h A, ?_, ?_⟩
  · intro J J' u
    change R.map (B.map u) ≫ (R.map (c J').hom ≫ (t (Q.obj J') A).hom) =
      (R.map (c J).hom ≫ (t (Q.obj J) A).hom) ≫ (R.map (Q.map u) ⊗ₘ 𝟙 (R.obj A))
    rw [← Category.assoc, ← R.map_comp, hc, R.map_comp, Category.assoc, ht]
    simp only [R.map_id, Category.assoc]
  · intro J M ξ
    change (R.map (c J).hom ≫ (t (Q.obj J) A).hom) ≫
      eU (R.obj (Q.obj J)) (R.obj A) (R.obj M) (R.map ξ ≫ (h A M).hom) = _
    rw [Category.assoc, hh, ← R.map_comp]

-- Canonical representative coherence requires substantial elaboration.
/-- Coherent tensor-model and RHom object comparisons under open restriction.
Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL, and Tag 06YH.
(blueprint: lem-sc-tensor-model-restriction-comparisons).

Proof: compute tensor with the K-flat P using the natural localization tensor
comparison. Apply tensor symmetry and eA to obtain c. Restrict P, which remains
K-flat, and use the total-tensor restriction comparison and the localization
factorization of restriction to obtain d. Naturality of those comparisons and
symmetry gives the first equation. For h, resolve E by the fixed K-injective
resolution, restrict it, and identify the Hom complexes termwise; transport the
result through the over-site equivalence to U.toScheme. On each tensor summand,
restriction of the evaluation map is evaluation of the restricted local map.
This proves the second equation for chain maps into Hom(P,I). That Hom complex
is K-injective, since P is K-flat and I is K-injective. Its restriction is also
K-injective. Every morphism from Q(J) is represented by a chain map modulo
homotopy, without requiring J to be K-flat. Uncurrying respects homotopy, so the
equation holds for every derived morphism. All comparisons are defined for zero
complexes and the empty open as well. -/
theorem exists_tensorModel_restriction_comparisons
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := fun E ↦ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    let B := fun J ↦ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P J (curriedTensor _))
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (c : ∀ J, B J ≅ DerivedCategory.Q.obj J ⊗ A)
      (d : ∀ J, R.obj (B J) ≅ R.obj (DerivedCategory.Q.obj J) ⊗ R.obj A)
      (h : ∀ E, R.obj (H E) ≅ HU.obj (op (R.obj A), R.obj E)),
      (∀ J J' (u : J ⟶ J'),
        R.map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
            (ComplexShape.up ℤ))) ≫ (d J').hom =
          (d J).hom ≫ (R.map (DerivedCategory.Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        (d J).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj (DerivedCategory.Q.obj J)) (R.obj A) (R.obj E)
          (R.map ξ ≫ (h E).hom) =
        R.map ((c J).hom ≫ schemeDerivedTensorHomEquiv X
          (DerivedCategory.Q.obj J) A E ξ)) := by
  classical
  have := SheafOfModules.isMonoidal_W X.sheaf
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q (C := C)
  let := schemeDerivedTensorMonoidal.{uX, wD} X
  let := schemeDerivedTensorMonoidal.{uX, wD} U.toScheme
  let R : schemeDerivedCategory X ⥤ schemeDerivedCategory U.toScheme := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory
  let B : CochainComplex C ℤ ⥤ schemeDerivedCategory X :=
    ((curriedTensor C).map₂CochainComplex.obj P) ⋙ Q
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact transport_model_comparisons Q B R (Q.obj P) A
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf)
    (derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf)
    (schemeDerivedTensorHomEquiv X) (schemeDerivedTensorHomEquiv U.toScheme) eA
    (kFlat_tensorModel_naturalComparison.{uX, wD} X P hP)
    (exists_schemeDerivedTensorSymmetry.{uX, wD} X)
    (exists_derivedRestriction_tensorHom_coherence.{uX, wD} X U)

end AlgebraicGeometry.Scheme
