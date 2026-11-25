/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTermwiseComparison

/-! # Open transport of the normalized tensor comparison

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-normalized-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange


private theorem composite_naturality
    {C D : Type*} [Category C] [Category D]
    {F₀ F₁ F₂ F₃ F₄ F₅ F₆ : C ⥤ D}
    (a₁ : F₀ ⟶ F₁) (a₂ : F₁ ⟶ F₂) (a₃ : F₂ ⟶ F₃)
    (a₄ : F₃ ⟶ F₄) (a₅ : F₄ ⟶ F₅) (a₆ : F₅ ⟶ F₆)
    {K L : C} (t : K ⟶ L) :
    F₀.map t ≫ a₁.app L ≫ a₂.app L ≫ a₃.app L ≫ a₄.app L ≫ a₅.app L ≫ a₆.app L =
      a₁.app K ≫ a₂.app K ≫ a₃.app K ≫ a₄.app K ≫ a₅.app K ≫ a₆.app K ≫ F₆.map t := by
  simp only [NatTrans.naturality_assoc, NatTrans.naturality]

-- Naturality of the composite pullback comparison expands several functor isomorphisms.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem restricted_identity_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    {K L : schemeDerivedCategory X} (t : K ⟶ L) :
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategory.map t) ≫
        singleComplexRestrictedCoefficient g' L ((derivedPullback g').obj L) (𝟙 _)
          U U' j hj =
      singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
          U U' j hj ≫
        (schemeOpenRestriction X' U').mapDerivedCategory.map ((derivedPullback g').map t) := by
  let c : ∀ {Y Z W : Scheme.{u}} (k : Y ⟶ Z) (l : Z ⟶ W),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun {Y Z W} k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  have h := composite_naturality
    (Functor.whiskerRight (singleComplexOpenPullbackIso X U).inv (derivedPullback j))
    (c j U.ι).hom
    (eqToHom (congrArg (fun k : U'.toScheme ⟶ X ↦ derivedPullback.{u, w} k) hj))
    (c U'.ι g').inv
    (Functor.whiskerLeft (derivedPullback g') (singleComplexOpenPullbackIso X' U').hom)
    (Functor.whiskerRight (𝟙 (derivedPullback g'))
      (schemeOpenRestriction X' U').mapDerivedCategory) t
  simpa only [c, singleComplexRestrictedCoefficient, NatTrans.id_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app,
    Functor.comp_map, Category.assoc] using h

-- Pinning the stalk scalar actions avoids repeating the tensor-model elaboration downstream.
open scoped TensorProduct in
set_option synthInstance.maxSize 2048 in
private theorem additive_representative_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' z i
    ∃ d : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
        F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z Q hcQ i)).left,
      F.map (comparisonIntoPullback f f' g g' sq z P hcP i) ≫
          F.map (H.map ((derivedPullback g').map a.hom)) =
        d.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z Q hcQ i) := by
  classical
  dsimp only
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  obtain ⟨s, hs, _⟩ := exists_comparisonSourceIso f f' g g' sq z P Q a i
  let T := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (A g' z ⊗[SingleComplexBaseChange.R f g' z] B f' z) (C z))
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  refine ⟨F.mapIso (T.mapIso s), ?_⟩
  have hn := comparisonIntoPullback_naturality f f' g g' sq z P Q
    hP hQ hcP hcQ a i s hs
  simpa only [Functor.map_comp, Functor.mapIso_hom, T, F] using congrArg F.map hn

set_option synthInstance.maxSize 2048 in
private theorem combine_transport_squares
    {C₀ C A : Type*} [Category C₀] [Category C] [Category A]
    (F₀ : C₀ ⥤ A) (F : C ⥤ A) (R : C ⥤ C₀) (ν : R ⋙ F₀ ≅ F)
    {U₀ UQ : C₀} {Y₀ Y : C} {S₀ SQ S : A}
    (q : SQ ⟶ F₀.obj UQ) (p : S₀ ⟶ F₀.obj U₀) (r : S ⟶ F.obj Y₀)
    (b : UQ ⟶ U₀) (β : U₀ ⟶ R.obj Y₀) (βK : U₀ ⟶ R.obj Y)
    (α : UQ ⟶ R.obj Y) (t : Y₀ ⟶ Y) (d : SQ ≅ S₀) (l : S₀ ≅ S)
    (hn : q ≫ F₀.map b = d.hom ≫ p)
    (hl : p ≫ F₀.map β ≫ ν.hom.app Y₀ = l.hom ≫ r)
    (hβ : βK = β ≫ R.map t) (hb : b ≫ βK = α) :
    q ≫ F₀.map α ≫ ν.hom.app Y = (d ≪≫ l).hom ≫ r ≫ F.map t := by
  rw [← hb, F₀.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, hβ, F₀.map_comp]
  have hν : F₀.map (R.map t) ≫ ν.hom.app Y = ν.hom.app Y₀ ≫ F.map t :=
    ν.hom.naturality t
  simp only [Category.assoc]
  rw [hν]
  have h := congrArg (fun k ↦ d.hom ≫ k ≫ F.map t) hl
  simpa only [Iso.trans_hom, Category.assoc] using h

private theorem map_comp_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {W V : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : F.obj Z ⟶ W) (k : F.obj Y ⟶ V) (t : V ⟶ W)
    (hn : F.map g ≫ h = k ≫ t) :
    F.map (f ≫ g) ≫ h = (F.map f ≫ k) ≫ t := by
  rw [Functor.map_comp, Category.assoc, hn, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two tensor-cohomology transports require a larger elaboration budget.
set_option synthInstance.maxSize 2048 in
/-- Transport the tensor comparison into derived pullback under open restriction.
This statement concerns the source complex and the pullback counit only; it has no
coefficient morphism and no target representative.

Proof: construct the natural additive derived-stalk comparison from exact
restriction and restrictStalkNatIso. Put P0 equal to the actual termwise restriction
of P. The termwise comparison lemma supplies K-flatness, the invertible pinned
counit on P0, and the normalized square
for P, P0, K=Q(P), and restriction's canonical localization factor.

Compose naturality of the six restriction/pullback comparison factors to prove
naturality of the restricted identity coefficient. Its naturality in e and that of the
additive derived-stalk comparison transport this square from Q(P) to K. Let E be
restriction's localization factor followed by restriction(e), and let b=a then
E inverse. This identifies Q(Q) with Q(P0). Apply exists_comparisonSourceIso to b
in the restricted square, extend its tensor-algebra source isomorphism to the
final stalk ring, and forget scalars, obtaining d. The proved pullback comparison
naturality gives its square. Since b then E equals a, compose this square with
the canonical termwise square, using naturality and functoriality. The composite
source isomorphism is d then l. Empty opens have no z; the argument uses neither
base flatness nor boundedness and applies to zero complexes and zero rings.

Source: Stacks Project, perfect.tex, Tag 0DJ9 first paragraph and equation-bc
preceding Tag 0DJ8; cohomology.tex, Tags 08HY and 08FE.
(blueprint: lem-pc-single-complex-open-normalized-transport). -/
theorem exists_singleComplexOpen_normalized_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (Q : CochainComplex
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (a : DerivedCategory.Q.obj Q ≅
      (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let R := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    ∃ (ν : R ⋙ H₀ ⋙ F₀ ≅ H ⋙ F)
      (l : F₀.obj ((Arrow.mk (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q hcQ i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoPullback f f' g g' sq z.val P hcP i)).left)),
      F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q hcQ i ≫
        H₀.map ((derivedPullback j).map a.hom ≫ θ)) ≫
          ν.hom.app ((derivedPullback g').obj K) =
      l.hom ≫ F.map (comparisonIntoPullback f f' g g' sq z.val P hcP i ≫
        H.map ((derivedPullback g').map e.hom)) := by
  classical
  dsimp only
  let RX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let RX' := schemeOpenRestriction X' (f' ⁻¹ᵁ V')
  have : RX.Additive := schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  have : RX.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive _
  let P₀ := (RX.mapHomologicalComplex (.up ℤ)).obj P
  let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
  -- Projections avoid rechecking the large stalk models during existential elimination.
  have htermwise := exists_singleComplexOpen_termwise_comparison
    f f' g g' sq V V' hV' j hj sq₀ P hP hcP z i
  have hP₀ := htermwise.choose
  have hcP₀ := htermwise.choose_spec.choose
  let l := htermwise.choose_spec.choose_spec.choose
  have hl := htermwise.choose_spec.choose_spec.choose_spec
  let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
    AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
  let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
  let H := comparisonStalkCohomology X' z.val i
  let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
  let θP := singleComplexRestrictedCoefficient g' (DerivedCategory.Q.obj P)
    ((derivedPullback g').obj (DerivedCategory.Q.obj P)) (𝟙 _)
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
  let a₀ := RX.mapDerivedCategoryFactors.symm.app P
  let E : DerivedCategory.Q.obj P₀ ≅ RX.mapDerivedCategory.obj K :=
    a₀ ≪≫ RX.mapDerivedCategory.mapIso e
  let b : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj P₀ := a ≪≫ E.symm
  let β := (derivedPullback j).map a₀.hom ≫ θP
  let βK := (derivedPullback j).map E.hom ≫ θ
  let cP := comparisonIntoPullback f f' g g' sq z.val P hcP i
  let cP₀ := comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
    (g.resLE V V' hV') j sq₀ z P₀ hcP₀ i
  let cQ := comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
    (g.resLE V V' hV') j sq₀ z Q hcQ i
  have hβ : βK = β ≫ RX'.mapDerivedCategory.map ((derivedPullback g').map e.hom) := by
    have hn := restricted_identity_naturality g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj e.hom
    change (derivedPullback j).map
        (a₀.hom ≫ RX.mapDerivedCategory.map e.hom) ≫ θ =
      ((derivedPullback j).map a₀.hom ≫ θP) ≫
        RX'.mapDerivedCategory.map ((derivedPullback g').map e.hom)
    exact map_comp_square (derivedPullback j) a₀.hom
      (RX.mapDerivedCategory.map e.hom) θ θP
      (RX'.mapDerivedCategory.map ((derivedPullback g').map e.hom)) hn
  have hl₀ : F₀.map cP₀ ≫ (H₀ ⋙ F₀).map β ≫
        ν.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) =
      l.hom ≫ F.map cP := by
    change F₀.map (cP₀ ≫ H₀.map β) ≫
        ν.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) =
      l.hom ≫ F.map cP at hl
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using hl
  have hrepresentative := additive_representative_transport
    (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q P₀
    hQ hP₀ hcQ hcP₀ b i
  let d := hrepresentative.choose
  have hn := hrepresentative.choose_spec
  have hb : (derivedPullback j).map b.hom ≫ βK =
      (derivedPullback j).map a.hom ≫ θ := by
    dsimp only [βK, b, Iso.trans_hom, Iso.symm_hom]
    simp only [← Functor.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨ν, d ≪≫ l, ?_⟩
  have h := combine_transport_squares (H₀ ⋙ F₀) (H ⋙ F) RX'.mapDerivedCategory ν
    (F₀.map cQ) (F₀.map cP₀) (F.map cP)
    ((derivedPullback j).map b.hom) β βK
    ((derivedPullback j).map a.hom ≫ θ) ((derivedPullback g').map e.hom)
    d l hn hl₀ hβ hb
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using h

end AlgebraicGeometry
