/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.TensorModelRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

/-! # Tensor-model adjunction and restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-sc-tensor-model-restriction-adjunction).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem tensorHom_precomp
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (e : ∀ K L E, (K ⟶ H.obj (op L, E)) ≃ (K ⊗ L ⟶ E))
    (hn : ∀ K K' L L' E E' (a : K' ⟶ K) (b : L' ⟶ L) (c : E ⟶ E')
      (f : K ⟶ H.obj (op L, E)),
      e K' L' E' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e K L E f ≫ c)
    (K K' L E : D) (a : K' ⟶ K) (f : K ⟶ H.obj (op L, E)) :
    e K' L E (a ≫ f) = (a ⊗ₘ 𝟙 L) ≫ e K L E f := by
  have h := hn K K' L L E E a (𝟙 L) (𝟙 E) f
  have hid : H.map ((𝟙 L).op, 𝟙 E) = 𝟙 (H.obj (op L, E)) :=
    H.map_id (op L, E)
  simpa only [hid, Category.comp_id] using h

private theorem transport_tensor_adjunction
    {I C D : Type*} [Category I] [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : I ⥤ C) (B : I → C) (b : ∀ {i j : I}, (i ⟶ j) → (B i ⟶ B j))
    (R : C ⥤ D) (A : C) (H : C → C) (HU : C → D)
    (eX : ∀ i E, (Q.obj i ⟶ H E) ≃ (Q.obj i ⊗ A ⟶ E))
    (eU : ∀ K E, (K ⟶ HU E) ≃ (K ⊗ R.obj A ⟶ R.obj E))
    (hn : ∀ K K' E (a : K' ⟶ K) (f : K ⟶ HU E),
      eU K' E (a ≫ f) = (a ⊗ₘ 𝟙 (R.obj A)) ≫ eU K E f)
    (c : ∀ i, B i ≅ Q.obj i ⊗ A)
    (d : ∀ i, R.obj (B i) ≅ R.obj (Q.obj i) ⊗ R.obj A)
    (h : ∀ E, R.obj (H E) ≅ HU E)
    (hd : ∀ i j (u : i ⟶ j), R.map (b u) ≫ (d j).hom =
      (d i).hom ≫ (R.map (Q.map u) ⊗ₘ 𝟙 (R.obj A)))
    (hh : ∀ i E (f : Q.obj i ⟶ H E),
      (d i).hom ≫ eU (R.obj (Q.obj i)) E (R.map f ≫ (h E).hom) =
        R.map ((c i).hom ≫ eX i E f)) :
    ∃ (t : ∀ i E, (Q.obj i ⟶ H E) ≃ (B i ⟶ E))
      (r : ∀ i E, (R.obj (Q.obj i) ⟶ R.obj (H E)) ≃ (R.obj (B i) ⟶ R.obj E)),
      (∀ i E (f : Q.obj i ⟶ H E), r i E (R.map f) = R.map (t i E f)) ∧
      (∀ i j E (u : i ⟶ j) (f : R.obj (Q.obj j) ⟶ R.obj (H E)),
        r i E (R.map (Q.map u) ≫ f) = R.map (b u) ≫ r j E f) := by
  let t := fun i E ↦ (eX i E).trans (Iso.homCongr (c i).symm (Iso.refl E))
  let r := fun i E ↦ (Iso.homCongr (Iso.refl (R.obj (Q.obj i))) (h E)).trans
    ((eU (R.obj (Q.obj i)) E).trans (Iso.homCongr (d i).symm (Iso.refl (R.obj E))))
  refine ⟨t, r, ?_, ?_⟩
  · intro i E f
    simpa [t, r, Iso.homCongr] using hh i E f
  · intro i j E u f
    simp only [r, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
      Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Category.assoc]
    rw [hn, ← Category.assoc, ← hd i j u]
    simp only [Category.assoc]

private theorem transport_tensor_adjunction_of_comparisons
    {I C D : Type*} [Category I] [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : I ⥤ C) (B : I → C) (b : ∀ {i j : I}, (i ⟶ j) → (B i ⟶ B j))
    (R : C ⥤ D) (A : C) (H : C → C) (HU : C → D)
    (eX : ∀ i E, (Q.obj i ⟶ H E) ≃ (Q.obj i ⊗ A ⟶ E))
    (eU : ∀ K E, (K ⟶ HU E) ≃ (K ⊗ R.obj A ⟶ R.obj E))
    (hn : ∀ K K' E (a : K' ⟶ K) (f : K ⟶ HU E),
      eU K' E (a ≫ f) = (a ⊗ₘ 𝟙 (R.obj A)) ≫ eU K E f)
    (hc : ∃ (c : ∀ i, B i ≅ Q.obj i ⊗ A)
      (d : ∀ i, R.obj (B i) ≅ R.obj (Q.obj i) ⊗ R.obj A)
      (h : ∀ E, R.obj (H E) ≅ HU E),
      (∀ i j (u : i ⟶ j), R.map (b u) ≫ (d j).hom =
        (d i).hom ≫ (R.map (Q.map u) ⊗ₘ 𝟙 (R.obj A))) ∧
      (∀ i E (f : Q.obj i ⟶ H E),
        (d i).hom ≫ eU (R.obj (Q.obj i)) E (R.map f ≫ (h E).hom) =
          R.map ((c i).hom ≫ eX i E f))) :
    ∃ (t : ∀ i E, (Q.obj i ⟶ H E) ≃ (B i ⟶ E))
      (r : ∀ i E, (R.obj (Q.obj i) ⟶ R.obj (H E)) ≃ (R.obj (B i) ⟶ R.obj E)),
      (∀ i E (f : Q.obj i ⟶ H E), r i E (R.map f) = R.map (t i E f)) ∧
      (∀ i j E (u : i ⟶ j) (f : R.obj (Q.obj j) ⟶ R.obj (H E)),
        r i E (R.map (Q.map u) ≫ f) = R.map (b u) ≫ r j E f) := by
  obtain ⟨c, d, h, hd, hh⟩ := hc
  exact transport_tensor_adjunction Q B b R A H HU eX eU hn c d h hd hh

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 512 in
/-- The adjunction on a fixed K-flat first model gives global and restricted
transposition families. They commute with restriction and are natural in the
second complex, without any K-flatness requirement on that complex.

Source: Stacks Project, cohomology.tex, Tag 08DJ, equation-internal-hom and
lemma-internal-hom; Tag 08DL, lemma-restriction-RHom-to-U.
(blueprint: lem-sc-tensor-model-restriction-adjunction).

Proof:
1. Compute tensor with the fixed K-flat P by the total tensor complex, and
transport its first argument through eA. The canonical tensor-Hom adjunction,
with the tensor symmetry to order P first, gives t for every J and E.
2. Restriction is exact, preserves P's K-flatness, and commutes with direct-sum
signed total tensors. Restrict P and transport eA by restriction. The canonical
RHom restriction comparison and the same adjunction on U give r.
3. Resolve E by a K-injective complex. Its restriction is K-injective. The Hom
restriction comparison restricts each local component, and tensor evaluation
on each summand restricts the same local map. Thus r applied to the restriction
of a morphism is the restriction of t applied to that morphism. Localizing the
component equations gives the first displayed identity. Since P is K-flat and
I is K-injective, Hom(P,I) is K-injective, both globally and after restriction.
Every derived map from Q(J) into these Hom objects is therefore represented by
a chain map modulo homotopy, even for non-K-flat J. Uncurrying respects homotopy;
the component calculation consequently proves compatibility for every derived
morphism, not just for an assumed chain representative.
4. Precomposition by a chain map u in J commutes with evaluation on every
summand. The canonical adjunction is natural, as are the localization tensor
comparison and restriction comparison. Hence r sends precomposition by R(Q(u))
to precomposition by R(Q(id_P tensor u)), the second displayed identity.
The zero model and the empty open satisfy the same equations, since all the
comparisons and summand maps are defined there too. -/
theorem exists_tensorModel_restriction_adjunction
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
    ∃ (t : ∀ J E, (DerivedCategory.Q.obj J ⟶ H E) ≃ (B J ⟶ E))
      (r : ∀ J E, (R.obj (DerivedCategory.Q.obj J) ⟶ R.obj (H E)) ≃
        (R.obj (B J) ⟶ R.obj E)),
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        r J E (R.map ξ) = R.map (t J E ξ)) ∧
      (∀ J J' E (u : J ⟶ J')
        (s : R.obj (DerivedCategory.Q.obj J') ⟶ R.obj (H E)),
        r J E (R.map (DerivedCategory.Q.map u) ≫ s) =
          R.map (DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
              (ComplexShape.up ℤ))) ≫ r J' E s) := by
  classical
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := (SheafOfModules.tensorClosed X.sheaf).1.some
  let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  letI := schemeDerivedTensorMonoidal X
  letI := schemeDerivedTensorMonoidal U.toScheme
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    refine transport_tensor_adjunction_of_comparisons DerivedCategory.Q _
      (fun u ↦ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (.up ℤ)))
      R A _ _ (fun J E ↦ schemeDerivedTensorHomEquiv X (DerivedCategory.Q.obj J) A E)
      (fun K E ↦ schemeDerivedTensorHomEquiv U.toScheme K (R.obj A) (R.obj E))
      ?_ (exists_tensorModel_restriction_comparisons X U A P hP eA)
    intro K K' E a f
    exact tensorHom_precomp
      (derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
        U.toScheme.toRingedSpace.sheaf)
      (schemeDerivedTensorHomEquiv U.toScheme)
      (Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)).1
      K K' (R.obj A) (R.obj E) a f

end AlgebraicGeometry.Scheme
