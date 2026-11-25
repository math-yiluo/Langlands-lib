/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationUncurryCalculation

/-! # Localization of the ordinary evaluation equation
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- The ordinary-to-derived Hom map obtained from the fixed resolution augmentation.
This constructs a morphism without choosing any comparison witness.
Source: Stacks Project, Tag 08DJ.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization). -/
def schemeOrdinaryHomComparison (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (homComplex.{u, u, u, u} (R := Y.sheaf) P M) ⟶
      (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M) := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  exact DerivedCategory.Q.map (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map
    ((CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app M)) ≫
    (schemeDerivedInternalHomResolutionIso Y P M).inv

/-- Three-variable naturality of the canonical derived tensor-Hom family.
Source: Stacks Project, cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-scheme-derived-tensor-hom-naturality).
Proof: unfold the chosen family and apply the naturality conjunct of its
characterizing predicate. -/
theorem schemeDerivedTensorHomEquiv_naturality (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K K' L L' M M' : schemeDerivedCategory Y)
    (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
    (g : K ⟶ (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
      (op L, M)) :
    schemeDerivedTensorHomEquiv Y K' L' M'
        (a ≫ g ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).map
          (b.op, c)) =
      (a ⊗ₘ b) ≫ schemeDerivedTensorHomEquiv Y K L M g ≫ c := by
  simpa only [schemeDerivedTensorHomEquiv] using
    (Classical.choose_spec (exists_canonicalDerivedTensorHom Y)).1
      K K' L L' M M' a b c g

private theorem uncurry_representative (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (A P M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (φ : A ⟶ homComplex.{u, u, u, u} (R := Y.sheaf) P
      ((schemeHomKInjectiveResolution Y).obj M)) :
    schemeDerivedTensorHomEquiv Y (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj M)
        (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso Y P M).inv) =
      pullbackTensorModelMap Y A P ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry Y A P M φ) ≫
          schemeHomResolutionInverse Y M := by
  classical
  obtain ⟨B, b, hB, _, hb, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := Y.sheaf) A
  have : IsIso (DerivedCategory.Q.map b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ b).2 hb
  have hn := schemeDerivedTensorHomEquiv_naturality Y
    (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj M)
    (DerivedCategory.Q.map b) (𝟙 _) (𝟙 _)
    (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso Y P M).inv)
  have hc := (Classical.choose_spec (exists_canonicalDerivedTensorHom Y)).2
    B P M hB (b ≫ φ)
  obtain ⟨ψ, hψ, hc⟩ := hc
  have he : ψ = schemeTensorHomUncurry Y B P M (b ≫ φ) := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := B) (K₂ := P) (F := curriedTensor _) (c := .up ℤ)
    intro p q h
    have h' : q + p = n := by change p + q = n at h; omega
    exact (hψ p q n h h').trans
      (schemeTensorHomUncurry_component Y B P M (b ≫ φ) p q n h h').symm
  have hc' := hc.trans (congrArg (fun ψ ↦ pullbackTensorModelMap Y B P ≫
    DerivedCategory.Q.map ψ ≫ schemeHomResolutionInverse Y M) he)
  have hl := schemeTensorHomUncurry_localized_evaluation Y A B P P M M
    b (𝟙 _) (𝟙 _) φ
  have hidH := (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).map_id
    (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)
  simp only [prod_id'] at hidH
  have hidC := (Functor.uncurry.obj (homComplexFunctor (R := Y.sheaf))).map_id
    (op P, (schemeHomKInjectiveResolution Y).obj M)
  simp only [prod_id'] at hidC
  simp only [(schemeHomKInjectiveResolution Y).map_id] at hl
  simp only [op_id, hidH, Category.comp_id] at hn
  simp only [op_id, hidC] at hl
  erw [Category.comp_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at hl
  simp only [← Functor.map_comp, ← Category.assoc] at hn
  exact (cancel_epi (DerivedCategory.Q.map b ⊗ₘ 𝟙 (DerivedCategory.Q.obj P))).1
    (hn.symm.trans (hc'.trans hl))

private theorem evaluation_transport {C : Type*} [Category* C] [MonoidalCategory C]
    {A V P T N K : C} (a : A ≅ N) (b : P ≅ K)
    (m : A ⊗ V ⟶ T) (t : T ⊗ P ⟶ A) (v : V ⊗ P ⟶ 𝟙_ C)
    (h : (m ▷ P) ≫ t = (α_ A V P).hom ≫ A ◁ v ≫ (ρ_ A).hom) :
    (((a.inv ▷ V) ≫ m) ⊗ₘ b.inv) ≫ t ≫ a.hom =
      (α_ N V K).hom ≫ N ◁ ((𝟙 V ⊗ₘ b.inv) ≫ v) ≫ (ρ_ N).hom := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc, reassoc_of% h]
  rw [← tensorHom_id a.inv V, associator_naturality_assoc]
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_def']
  simp only [Category.assoc]
  rw [← Category.assoc (a.inv ▷ 𝟙_ C), rightUnitor_naturality]
  simp only [Category.assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Localizing the componentwise ordinary evaluation gives its uncurried derived map.
No Hom-exactness, K-flatness, or invertibility of the comparison maps is asserted.
Source: Stacks Project, Tags 08DJ, 08DM and 08DQ; representative calculation.
(blueprint: lem-pc-scheme-ordinary-evaluation-localization).

Proof: resolve both tensor inputs by K-flat complexes and the coefficient by the
fixed K-injective functor. Apply the canonical tensor-Hom representative equation.
Precompose with each total-tensor summand and postcompose with each Hom projection.
Naturality of evaluation with the coefficient augmentation and the resolution maps
reduces the equation to hf: the unit is supported in degree zero, so the component
is the unit action when r+q=0 and zero otherwise. The coproduct inclusions and product
projections detect equality. Localize and cancel the quasi-isomorphisms of the
K-flat resolutions and coefficient resolution. The unit identification is the
quotient comparison at the single complex. Finally apply three-variable naturality
of the canonical family along eK and eN. This proves a morphism equation without
inverting the ordinary Hom or tensor comparisons. For zero complexes or the empty
scheme the same component equations hold, with all maps zero. -/
theorem schemeOrdinaryEvaluation_localization (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K N : schemeDerivedCategory Y)
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj F ≅ N)
    (f : pullbackTensorTotal Y F
        (homComplex.{u, u, u, u} (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex.{u, u, u, u} (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) :
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex.{u, u, u, u} (R := Y.sheaf) P O
    let c := schemeOrdinaryHomComparison Y P F ≫ H.map (eK.inv.op, eN.hom)
    let d := schemeOrdinaryHomComparison Y P O ≫
      H.map (eK.inv.op, ((DerivedCategory.quotientCompQhIso _).app O).inv)
    schemeDerivedTensorHomEquiv Y (N ⊗ DerivedCategory.Q.obj V) K N
        ((eN.inv ▷ DerivedCategory.Q.obj V) ≫ pullbackTensorModelMap Y F V ≫
          DerivedCategory.Q.map f ≫ c) =
      (α_ N (DerivedCategory.Q.obj V) K).hom ≫ N ◁
        (schemeDerivedTensorHomEquiv Y (DerivedCategory.Q.obj V) K
          (𝟙_ (schemeDerivedCategory Y)) d) ≫ (ρ_ N).hom := by
  classical
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex.{u, u, u, u} (R := Y.sheaf) P O
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let phiF := f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F)
  let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
  let z := ((DerivedCategory.quotientCompQhIso _).app O).inv
  have hF := uncurry_representative Y (pullbackTensorTotal Y F V) P F phiF
  have hO := uncurry_representative Y V P O phiO
  have hc := schemeOrdinaryEvaluation_uncurry_calculation Y P F f hf
  have hn := schemeDerivedTensorHomEquiv_naturality Y
    (DerivedCategory.Q.obj (pullbackTensorTotal Y F V)) (N ⊗ DerivedCategory.Q.obj V)
    (DerivedCategory.Q.obj P) K (DerivedCategory.Q.obj F) N
    ((eN.inv ▷ DerivedCategory.Q.obj V) ≫ pullbackTensorModelMap Y F V)
    eK.inv eN.hom
    (DerivedCategory.Q.map f ≫ schemeOrdinaryHomComparison Y P F)
  have hd := schemeDerivedTensorHomEquiv_naturality Y
    (DerivedCategory.Q.obj V) (DerivedCategory.Q.obj V)
    (DerivedCategory.Q.obj P) K (DerivedCategory.Q.obj O)
    (𝟙_ (schemeDerivedCategory Y)) (𝟙 _) eK.inv z
    (schemeOrdinaryHomComparison Y P O)
  have hF' : schemeDerivedTensorHomEquiv Y
      (DerivedCategory.Q.obj (pullbackTensorTotal Y F V)) (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.map f ≫ schemeOrdinaryHomComparison Y P F) =
    pullbackTensorModelMap Y (pullbackTensorTotal Y F V) P ≫
      DerivedCategory.Q.map
        (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F phiF) ≫
      schemeHomResolutionInverse Y F := by
    simpa only [phiF, schemeOrdinaryHomComparison, Functor.map_comp, Category.assoc]
      using hF
  have hO' : schemeDerivedTensorHomEquiv Y (DerivedCategory.Q.obj V)
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)
      (schemeOrdinaryHomComparison Y P O) =
    pullbackTensorModelMap Y V P ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry Y V P O phiO) ≫
      schemeHomResolutionInverse Y O := by
    exact hO
  change schemeDerivedTensorHomEquiv Y _ _ _ _ = _
  simp only [Category.assoc] at hn
  simp only [Category.id_comp] at hd
  have hleft := congrArg (fun t ↦
    (((eN.inv ▷ DerivedCategory.Q.obj V) ≫ pullbackTensorModelMap Y F V) ⊗ₘ eK.inv) ≫
      t ≫ eN.hom) hF'
  have hright := congrArg (fun t ↦
    (α_ N (DerivedCategory.Q.obj V) K).hom ≫ N ◁ t ≫ (ρ_ N).hom)
      (hd.trans (congrArg (fun t ↦ (𝟙 (DerivedCategory.Q.obj V) ⊗ₘ eK.inv) ≫ t ≫ z) hO'))
  have ht := evaluation_transport eN eK
    (pullbackTensorModelMap Y F V)
    (pullbackTensorModelMap Y (pullbackTensorTotal Y F V) P ≫
      DerivedCategory.Q.map
        (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F phiF) ≫
      schemeHomResolutionInverse Y F)
    (pullbackTensorModelMap Y V P ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry Y V P O phiO) ≫
      schemeHomResolutionInverse Y O ≫ z) hc
  refine hn.trans (hleft.trans (Eq.trans ?_ hright.symm))
  simpa only [Category.assoc] using ht

end AlgebraicGeometry
