/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.CanonicalTensorModelInputNaturality

/-! # Comparison of normalized derived evaluation maps

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-uncurry-normalized-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Keep the component algebra independent of the chosen Hom-complex projections.
private theorem component_input {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] [BraidedCategory C] {A B H I : C}
    (f : A ⟶ H) (g : H ⟶ (ihom B).obj I) :
    (β_ A B).hom ≫ MonoidalClosed.uncurry (f ≫ g) =
      ((curriedTensor C).map f).app B ≫ ((curriedTensor C).obj H).map (𝟙 B) ≫
        (β_ H B).hom ≫ MonoidalClosed.uncurry g := by
  dsimp only [curriedTensor]
  rw [whiskerLeft_id, Category.id_comp]
  rw [MonoidalClosed.uncurry_natural_left,
    ← BraidedCategory.braiding_naturality_left_assoc]

private theorem uncurry_input (X : Scheme.{u})
    (P L M : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    schemeTensorHomUncurry X P L M φ =
      HomologicalComplex.mapBifunctorMap φ (𝟙 L) (curriedTensor _) (.up ℤ) ≫
        schemeTensorHomUncurry X _ L M (𝟙 _) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let := SheafOfModules.monoidalClosed (R := X.sheaf)
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
  intro p q hpq
  change p + q = n at hpq
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f]
  rw [schemeTensorHomUncurry_component X P L M φ p q n hpq (by omega),
    schemeTensorHomUncurry_component X _ L M (𝟙 _) p q n hpq (by omega)]
  dsimp only [schemeTensorHomUncurryComponent]
  simp only [HomologicalComplex.id_f, Category.id_comp,
    ← SheafOfModules.uncurry_eq_tensorHomEquiv_symm (R := X.sheaf)]
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types true in
      exact component_input (φ.f p) _

private theorem localized_factor {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory D] (Q : C ⥤ D)
    {P L H T T' I M : C} {HD : D}
    (φ : P ⟶ H) (u : T ⟶ I) (v : T' ⟶ I) (t : T ⟶ T')
    (j : HD ≅ Q.obj H) (r : Q.obj I ⟶ Q.obj M)
    (μ : Q.obj P ⊗ Q.obj L ⟶ Q.obj T)
    (μ' : Q.obj H ⊗ Q.obj L ⟶ Q.obj T')
    (hu : u = t ≫ v)
    (hn : (Q.map φ ⊗ₘ 𝟙 (Q.obj L)) ≫ μ' = μ ≫ Q.map t) :
    μ ≫ Q.map u ≫ r =
      ((Q.map φ ≫ j.inv) ⊗ₘ 𝟙 (Q.obj L)) ≫
        (j.hom ⊗ₘ 𝟙 (Q.obj L)) ≫ μ' ≫ Q.map v ≫ r := by
  rw [hu, Q.map_comp]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, j.inv_hom_id, Category.comp_id]
  rw [← Category.assoc _ _ (Q.map v ≫ r), ← hn]
  simp only [Category.assoc]

-- Factor a normalized representative through evaluation at the identity.
private theorem localized_uncurry_input (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      ((DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X _ L ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
            schemeHomResolutionInverse X M := by
  let := schemeDerivedTensorMonoidal X
  set_option backward.isDefEq.respectTransparency.types true in
    exact localized_factor DerivedCategory.Q φ _ _ _
      (schemeDerivedInternalHomResolutionIso X L M) (schemeHomResolutionInverse X M)
      (pullbackTensorModelMap X P L) (pullbackTensorModelMap X _ L)
      (uncurry_input X P L M φ) (tensorModelMap_input_natural X P _ L φ)

-- The comparison follows formally from the square for evaluation itself.
private theorem evaluation_comparison {C : Type*} [Category* C] [MonoidalCategory C]
    {K K' L L' M M' H H' : C}
    (a : K ⟶ K') (b : L ⟶ L') (c : M' ⟶ M)
    (f : K ⟶ H) (f' : K' ⟶ H') (d : H' ⟶ H)
    (E : H ⊗ L ⟶ M) (E' : H' ⊗ L' ⟶ M')
    (h : f = a ≫ f' ≫ d)
    (hn : (d ⊗ₘ 𝟙 L) ≫ E = (𝟙 H' ⊗ₘ b) ≫ E' ≫ c) :
    (f ⊗ₘ 𝟙 L) ≫ E = (a ⊗ₘ b) ≫ (f' ⊗ₘ 𝟙 L') ≫ E' ≫ c := by
  rw [h]
  calc
    _ = (a ⊗ₘ 𝟙 L) ≫ (f' ⊗ₘ 𝟙 L) ≫ (d ⊗ₘ 𝟙 L) ≫ E := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (a ⊗ₘ 𝟙 L) ≫ (f' ⊗ₘ 𝟙 L) ≫ (𝟙 H' ⊗ₘ b) ≫ E' ≫ c := by
      rw [hn]
    _ = _ := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

private theorem comparison_of_factorizations {C : Type*} [Category* C]
    [MonoidalCategory C] {K K' L L' M M' H H' : C}
    (a : K ⟶ K') (b : L ⟶ L') (c : M' ⟶ M)
    (f : K ⟶ H) (f' : K' ⟶ H') (d : H' ⟶ H)
    (E : H ⊗ L ⟶ M) (E' : H' ⊗ L' ⟶ M')
    (g : K ⊗ L ⟶ M) (g' : K' ⊗ L' ⟶ M')
    (hg : g = (f ⊗ₘ 𝟙 L) ≫ E) (hg' : g' = (f' ⊗ₘ 𝟙 L') ≫ E')
    (h : f = a ≫ f' ≫ d)
    (hn : (d ⊗ₘ 𝟙 L) ≫ E = (𝟙 H' ⊗ₘ b) ≫ E' ≫ c) :
    g = (a ⊗ₘ b) ≫ g' ≫ c := by
  rw [hg, hg', Category.assoc]
  exact evaluation_comparison a b c f f' d E E' h hn

private theorem assoc_four {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G) :
    a ≫ (b ≫ c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

/-- Localized evaluation respects comparisons between normalized representatives.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90
and 0A96. (blueprint: lem-pc-tensor-hom-uncurry-normalized-comparison).

Proof: Replace L and L' by K-flat resolutions, and replace both targets by their
fixed K-injective resolutions. Hom from a K-flat complex into a K-injective is
K-injective, so the displayed equality of derived inputs is an equality of
homotopy classes after computing the comparison roofs on common K-flat sources.
Uncurrying carries a chain homotopy to a chain homotopy: uncurry its degree-minus-one
components on every tensor summand, and use the Hom differential formula to
identify the boundary with the difference of evaluations. On chain maps,
precomposition in P and L and postcomposition in the target commute with evaluation
by naturality of the sheaf tensor-Hom adjunction and of the Hom projections.
Coproduct extensionality promotes the summand identities to identities of chain
maps. Localize those identities. Naturality of the tensor model comparison, of the
internal-Hom resolution comparison, and of the resolution augmentation identifies
the resulting composites with the displayed outputs. Cancel the localized
quasi-isomorphisms of the chosen resolutions. For arbitrary L, K-flatness of P
makes P tensor - invert its resolution, while Hom(-,I(M)) also inverts it; hence
the same cancellation applies. This proves the implication without any hypothesis
on a family of values, and includes zero maps, zero complexes, and identity
comparisons. No boundedness is used. -/
theorem tensorHomUncurry_normalized_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M')
    (h : DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv =
      a.hom ≫ DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv ≫
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
            (b.hom.op, c.inv)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      (a.hom ⊗ₘ b.hom) ≫ pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M' ≫ c.inv := by
  have _ := hP
  have _ := hP'
  let := schemeDerivedTensorMonoidal X
  have hc := comparison_of_factorizations a.hom b.hom c.inv _ _ _ _ _ _ _
    (localized_uncurry_input X P L M φ) (localized_uncurry_input X P' L' M' φ')
    (h.trans (congrArg (fun f ↦ a.hom ≫ f)
      (Category.assoc (DerivedCategory.Q.map φ')
        (schemeDerivedInternalHomResolutionIso X L' M').inv _).symm))
    (tensorHomEvaluation_natural X L M L' M' b c)
  exact hc.trans (assoc_four _ _ _ _ _)

end AlgebraicGeometry
