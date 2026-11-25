/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulRoosComparison
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulConstantTransport
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Transport of completed quotient and Koszul presentations

Source: Stacks Tags 03CR, 05RR, 06YY and 0941.
(blueprint: lem-weil-pbc-completed-constant-presentation-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

@[irreducible]
private def completionComparison
    {D D' H H' : Type*} [Category* D] [Category* D'] [Category* H] [Category* H']
    (E : D ⥤ D') (G : H ⥤ H') (L : D ⥤ H) (L' : D' ⥤ H')
    (R : H ⥤ D) (R' : H' ⥤ D')
    (φ : L ⋙ G ≅ E ⋙ L') (ψ : R ⋙ E ≅ G ⋙ R') :
    (L ⋙ R) ⋙ E ≅ E ⋙ (L' ⋙ R') :=
  CategoryTheory.Functor.associator L R E ≪≫
    CategoryTheory.Functor.isoWhiskerLeft L ψ ≪≫
      (CategoryTheory.Functor.associator L G R').symm ≪≫
        CategoryTheory.Functor.isoWhiskerRight φ R' ≪≫
          CategoryTheory.Functor.associator E L' R'

private theorem completionComparison_hom_app
    {D D' H H' : Type*} [Category* D] [Category* D'] [Category* H] [Category* H']
    (E : D ⥤ D') (G : H ⥤ H') (L : D ⥤ H) (L' : D' ⥤ H')
    (R : H ⥤ D) (R' : H' ⥤ D')
    (φ : L ⋙ G ≅ E ⋙ L') (ψ : R ⋙ E ≅ G ⋙ R') (P : D) :
    (completionComparison E G L L' R R' φ ψ).hom.app P =
      ψ.hom.app (L.obj P) ≫ R'.map (φ.hom.app P) := by
  simp only [completionComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

private theorem completion_square_unit
    {D D' H H' : Type*} [Category* D] [Category* D'] [Category* H] [Category* H']
    (E : D ⥤ D') (G : H ⥤ H') (L : D ⥤ H) (L' : D' ⥤ H')
    (R : H ⥤ D) (R' : H' ⥤ D')
    (κ : 𝟭 D ⟶ L ⋙ R) (κ' : 𝟭 D' ⟶ L' ⋙ R')
    (φ : L ⋙ G ≅ E ⋙ L') (ψ : R ⋙ E ≅ G ⋙ R')
    (P : D) (P' : D') (χ : E.obj P ≅ P')
    (X : H) (Y : H') (ε : L.obj P ⟶ X) [IsIso ε]
    (ε' : L'.obj P' ⟶ Y) (ζ : G.obj X ≅ Y)
    (μ : P ⟶ R.obj X) (μ' : P' ⟶ R'.obj Y)
    (hφ : φ.hom.app P ≫ L'.map χ.hom ≫ ε' = G.map ε ≫ ζ.hom)
    (hκ : κ.app P ≫ R.map ε = μ)
    (hκ' : κ'.app P' ≫ R'.map ε' = μ')
    (hμ : E.map μ ≫ ψ.hom.app X ≫ R'.map ζ.hom = χ.hom ≫ μ') :
    E.map (κ.app P) ≫ (completionComparison E G L L' R R' φ ψ).hom.app P =
      κ'.app (E.obj P) := by
  rw [completionComparison_hom_app]
  have hε : IsIso (φ.hom.app P ≫ L'.map χ.hom ≫ ε') := by
    rw [hφ]
    infer_instance
  have : IsIso (L'.map χ.hom ≫ ε') := IsIso.of_isIso_comp_left (φ.hom.app P) _
  apply (cancel_mono (R'.map (L'.map χ.hom ≫ ε'))).mp
  simp only [Category.assoc, ← R'.map_comp]
  rw [hφ, R'.map_comp]
  have hψ := ψ.hom.naturality ε
  dsimp only [CategoryTheory.Functor.comp_map] at hψ
  rw [← reassoc_of% hψ, ← E.map_comp_assoc, hκ, hμ]
  have hn := κ'.naturality χ.hom
  dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hn
  rw [R'.map_comp, ← Category.assoc, ← hn, Category.assoc, hκ']

private theorem normalized_unit_square
    {C Z C' Z' D H D' H' : Type*}
    [Category* C] [Category* Z] [Category* C'] [Category* Z']
    [Category* D] [Category* H] [Category* D'] [Category* H']
    (Q : C ⥤ D) (QH : Z ⥤ H) (Q' : C' ⥤ D') (QH' : Z' ⥤ H')
    (Ec : C ⥤ C') (Gc : Z ⥤ Z') (ED : D ⥤ D') (GD : H ⥤ H')
    (Rc : Z ⥤ C) (Rc' : Z' ⥤ C') (R : H ⥤ D) (R' : H' ⥤ D')
    (χ : Q ⋙ ED ≅ Ec ⋙ Q') (γ : QH ⋙ GD ≅ Gc ⋙ QH')
    (ρ : Rc ⋙ Ec ≅ Gc ⋙ Rc')
    (η : Rc ⋙ Q ⟶ QH ⋙ R) (η' : Rc' ⋙ Q' ⟶ QH' ⋙ R')
    (ψ : R ⋙ ED ≅ GD ⋙ R')
    (P : C) (X : Z) (Y : Z') (e : Gc.obj X ⟶ Y)
    (ν : P ⟶ Rc.obj X) (ν' : Ec.obj P ⟶ Rc'.obj Y)
    (hψ : ED.map (η.app X) ≫ ψ.hom.app (QH.obj X) ≫ R'.map (γ.hom.app X) =
      χ.hom.app (Rc.obj X) ≫ Q'.map (ρ.hom.app X) ≫ η'.app (Gc.obj X))
    (hν : Ec.map ν ≫ ρ.hom.app X ≫ Rc'.map e = ν') :
    ED.map (Q.map ν ≫ η.app X) ≫ ψ.hom.app (QH.obj X) ≫
        R'.map (γ.hom.app X ≫ QH'.map e) =
      χ.hom.app P ≫ (Q'.map ν' ≫ η'.app Y) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hψ]
  have hχ := χ.hom.naturality ν
  dsimp only [Functor.comp_map] at hχ
  rw [reassoc_of% hχ]
  have hη := η'.naturality e
  dsimp only [Functor.comp_map] at hη
  rw [← hη]
  have hν' := congrArg Q'.map hν
  simp only [Functor.map_comp] at hν'
  rw [reassoc_of% hν']

private theorem completion_unit_transport_iso
    {D D' : Type*} [Category* D] [Category* D']
    (E : D ⥤ D') (T : D ⥤ D) (T' : D' ⥤ D')
    (κ : 𝟭 D ⟶ T) (κ' : 𝟭 D' ⟶ T')
    {P K : D} (e : P ≅ K)
    (q : E.obj (T.obj P) ≅ T'.obj (E.obj P))
    (hq : E.map (κ.app P) ≫ q.hom = κ'.app (E.obj P)) :
    ∃ k : E.obj (T.obj K) ≅ T'.obj (E.obj K),
      E.map (κ.app K) ≫ k.hom = κ'.app (E.obj K) := by
  refine ⟨(E.mapIso (T.mapIso e)).symm ≪≫ q ≪≫ T'.mapIso (E.mapIso e), ?_⟩
  change E.map (κ.app K) ≫ E.map (T.map e.inv) ≫ q.hom ≫ T'.map (E.map e.hom) = _
  have hn := κ.naturality e.inv
  dsimp only [Functor.id_map] at hn
  rw [← E.map_comp_assoc, ← hn, E.map_comp, Category.assoc, reassoc_of% hq]
  have hn' := κ'.naturality (E.map e.hom)
  dsimp only [Functor.id_map] at hn'
  rw [← hn', ← Category.assoc, ← E.map_comp, e.inv_hom_id]
  erw [E.map_id, Category.id_comp]

/-- Compatibility of normalized completion units descends along a representative. -/
private theorem normalized_completion_transport
    {C Z C' Z' D H D' H' : Type*}
    [Category* C] [Category* Z] [Category* C'] [Category* Z']
    [Category* D] [Category* H] [Category* D'] [Category* H']
    (Q : C ⥤ D) (QH : Z ⥤ H) (Q' : C' ⥤ D') (QH' : Z' ⥤ H')
    (Ec : C ⥤ C') (Gc : Z ⥤ Z') (ED : D ⥤ D') (GD : H ⥤ H')
    (Rc : Z ⥤ C) (Rc' : Z' ⥤ C')
    (L : D ⥤ H) (L' : D' ⥤ H') (R : H ⥤ D) (R' : H' ⥤ D')
    (κ : 𝟭 D ⟶ L ⋙ R) (κ' : 𝟭 D' ⟶ L' ⋙ R')
    (χ : Q ⋙ ED ≅ Ec ⋙ Q') (γ : QH ⋙ GD ≅ Gc ⋙ QH')
    (ρ : Rc ⋙ Ec ≅ Gc ⋙ Rc')
    (η : Rc ⋙ Q ⟶ QH ⋙ R) (η' : Rc' ⋙ Q' ⟶ QH' ⋙ R')
    (φ : L ⋙ GD ≅ ED ⋙ L') (ψ : R ⋙ ED ≅ GD ⋙ R')
    (P : C) (K : D) (eP : Q.obj P ≅ K)
    (X : Z) (Y : Z') (e : Gc.obj X ⟶ Y) [IsIso e]
    (ε : L.obj (Q.obj P) ⟶ QH.obj X) [IsIso ε]
    (ε' : L'.obj (Q'.obj (Ec.obj P)) ⟶ QH'.obj Y)
    (ν : P ⟶ Rc.obj X) (ν' : Ec.obj P ⟶ Rc'.obj Y)
    (hφ : φ.hom.app (Q.obj P) ≫ L'.map (χ.hom.app P) ≫ ε' =
      GD.map ε ≫ γ.hom.app X ≫ QH'.map e)
    (hκ : κ.app (Q.obj P) ≫ R.map ε = Q.map ν ≫ η.app X)
    (hκ' : κ'.app (Q'.obj (Ec.obj P)) ≫ R'.map ε' = Q'.map ν' ≫ η'.app Y)
    (hψ : ED.map (η.app X) ≫ ψ.hom.app (QH.obj X) ≫ R'.map (γ.hom.app X) =
      χ.hom.app (Rc.obj X) ≫ Q'.map (ρ.hom.app X) ≫ η'.app (Gc.obj X))
    (hν : Ec.map ν ≫ ρ.hom.app X ≫ Rc'.map e = ν') :
    ∃ q : ED.obj ((L ⋙ R).obj K) ≅ (L' ⋙ R').obj (ED.obj K),
      ED.map (κ.app K) ≫ q.hom = κ'.app (ED.obj K) := by
  have hμ := normalized_unit_square Q QH Q' QH' Ec Gc ED GD Rc Rc' R R'
    χ γ ρ η η' ψ P X Y e ν ν' hψ hν
  have hφ' : φ.hom.app (Q.obj P) ≫ L'.map (χ.hom.app P) ≫ ε' =
      GD.map ε ≫ (γ.app X ≪≫ QH'.mapIso (asIso e)).hom := by
    simpa only [Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, asIso_hom] using hφ
  have hμ' : ED.map (Q.map ν ≫ η.app X) ≫ ψ.hom.app (QH.obj X) ≫
      R'.map ((γ.app X ≪≫ QH'.mapIso (asIso e)).hom) =
        χ.hom.app P ≫ (Q'.map ν' ≫ η'.app Y) := by
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom] using hμ
  have hunit := completion_square_unit ED GD L L' R R' κ κ' φ ψ
    (Q.obj P) (Q'.obj (Ec.obj P)) (χ.app P) (QH.obj X) (QH'.obj Y) ε ε'
    (γ.app X ≪≫ QH'.mapIso (asIso e)) (Q.map ν ≫ η.app X) (Q'.map ν' ≫ η'.app Y)
    hφ' hκ hκ' hμ'
  exact completion_unit_transport_iso ED (L ⋙ R) (L' ⋙ R') κ κ' eP
    ((completionComparison ED GD L L' R R' φ ψ).app (Q.obj P)) hunit

/-- Universal derived squares preserve a completion whose unit is normalized on a
resolving class of complexes. All ordinary and derived functors remain abstract here. -/
private theorem normalized_derived_completion_equivalence
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (R : H ⥤ B) (R' : H' ⥤ B') [R.Additive] [R'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (RF : DerivedCategory H ⥤ DerivedCategory B)
    (RF' : DerivedCategory H' ⥤ DerivedCategory B')
    (ε : DerivedCategory.Q ⋙ LF ⟶
      L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ LF' ⟶
      L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (η' : R'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF')
    [LF.IsRightKanExtension ε] [LF'.IsRightKanExtension ε']
    [RF.IsLeftKanExtension η] [RF'.IsLeftKanExtension η']
    (eL : L ⋙ G.functor ≅ E.functor ⋙ L')
    (eR : R ⋙ E.functor ≅ G.functor ⋙ R')
    (κ : 𝟭 _ ⟶ LF ⋙ RF) (κ' : 𝟭 _ ⟶ LF' ⋙ RF')
    (good : CochainComplex B ℤ → Prop)
    (resolve : ∀ K : DerivedCategory B, ∃ P, good P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K))
    (ν : ∀ P : CochainComplex B ℤ,
      P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (ν' : ∀ P : CochainComplex B' ℤ,
      P ⟶ (R'.mapHomologicalComplex (.up ℤ)).obj ((L'.mapHomologicalComplex (.up ℤ)).obj P))
    (normalization : ∀ P, good P → IsIso (ε.app P) ∧
      κ.app (DerivedCategory.Q.obj P) ≫ RF.map (ε.app P) =
        DerivedCategory.Q.map (ν P) ≫ η.app ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (normalization' : ∀ P, κ'.app (DerivedCategory.Q.obj P) ≫ RF'.map (ε'.app P) =
      DerivedCategory.Q.map (ν' P) ≫ η'.app ((L'.mapHomologicalComplex (.up ℤ)).obj P))
    (ordinary : ∀ P,
      (E.functor.mapHomologicalComplex (.up ℤ)).map (ν P) ≫
        (NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app
          ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (R'.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex eL (.up ℤ)).hom.app P) =
        ν' ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ F : DerivedCategory B ≌ DerivedCategory B',
      Nonempty (F.functor ≅ E.mapDerivedCategory.functor) ∧
      ∀ K, ∃ q : F.functor.obj ((LF ⋙ RF).obj K) ≅ (LF' ⋙ RF').obj (F.functor.obj K),
        F.functor.map (κ.app K) ≫ q.hom = κ'.app (F.functor.obj K) := by
  obtain ⟨S⟩ := exactEquivalenceDerivedSquares E G L L' R R'
    LF LF' RF RF' ε ε' η η' eL eR
  obtain ⟨F, GD, α, χ, γ, φ, ψ, hφ, hψ⟩ := S
  refine ⟨F, ⟨α⟩, ?_⟩
  intro K
  obtain ⟨P, hP, ⟨eP⟩⟩ := resolve K
  let Ec := E.functor.mapHomologicalComplex (.up ℤ)
  let Gc := G.functor.mapHomologicalComplex (.up ℤ)
  let Lc := L.mapHomologicalComplex (.up ℤ)
  let Lc' := L'.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let Rc' := R'.mapHomologicalComplex (.up ℤ)
  let ρ := NatIso.mapHomologicalComplex eR (.up ℤ)
  let e := (NatIso.mapHomologicalComplex eL (.up ℤ)).hom.app P
  have : IsIso e := inferInstance
  obtain ⟨hε, ha⟩ := normalization P hP
  let := hε
  exact normalized_completion_transport DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q
    Ec Gc F.functor GD.functor Rc Rc' LF LF' RF RF' κ κ' χ γ ρ η η' φ ψ
    P K eP (Lc.obj P) (Lc'.obj (Ec.obj P)) e (ε.app P) (ε'.app (Ec.obj P))
    (ν P) (ν' (Ec.obj P)) (hφ P) ha (normalization' (Ec.obj P))
    (hψ (Lc.obj P)) (ordinary P)

private def limitFunctorComparison {B H : Type*} [Category* B] [Category* H]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ H]
    (F : B ⥤ H) [PreservesLimitsOfShape ℕᵒᵖ F] :
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B) ⋙ F ≅
      (CategoryTheory.Functor.whiskeringRight ℕᵒᵖ B H).obj F ⋙ lim :=
  preservesLimitNatIso F

@[reassoc]
private theorem limitFunctorComparison_hom_π {B H : Type*} [Category* B] [Category* H]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ H]
    (F : B ⥤ H) [PreservesLimitsOfShape ℕᵒᵖ F] (M : ℕᵒᵖ ⥤ B) (n : ℕᵒᵖ) :
    (limitFunctorComparison F).hom.app M ≫ limit.π (M ⋙ F) n =
      F.map (limit.π M n) :=
  preservesLimitIso_hom_π F M n

attribute [local irreducible] limitFunctorComparison

private theorem actualTowerPair (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsCompletedReductionTowerPair T d (completedReductionTower T d)
      (completedReductionTowerCounit d T) := by
  unfold completedReductionTower completedReductionTowerCounit
  exact (completedReductionTower_exists T d).choose_spec.choose_spec

attribute [local irreducible] completedReductionTower completedReductionTowerCounit
  completedReductionModuleUnit completedReductionTowerUnit
  ConstantCompletion.quotientPresentation ConstantCompletion.strictLimit
  ConstantCompletion.ordinaryUnit ConstantCompletion.rlim

private theorem comparisonOrdinaryCompletionUnit (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (E : reductionModules T (d.completedRing T) ≌ ConstantCompletion.Mod
      (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true))
    [E.functor.Additive]
    (e : completedReductionModuleTowerFunctor T d ⋙
      (CategoryTheory.Functor.whiskeringRight ℕᵒᵖ _ _).obj E.functor ≅
        E.functor ⋙ ConstantCompletion.reductionTower
          (completedCechTopology T) A d.ideal true)
    (hu : ∀ (M : reductionModules T (d.completedRing T)) (n : ℕ),
      E.functor.map (((completedReductionModuleUnit d T).app M).app (op n)) ≫
          (e.hom.app M).app (op n) =
        ((ConstantCompletion.reductionUnit
          (completedCechTopology T) A d.ideal true).app (E.functor.obj M)).app (op n))
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    let := completedReductionModuleTowerFunctor_additive T d
    let := ConstantCompletion.reductionTower_additive (completedCechTopology T) A d.ideal true
    let Ec := E.functor.mapHomologicalComplex (.up ℤ)
    let L := completedReductionModuleTowerFunctor T d
    let Lc := L.mapHomologicalComplex (.up ℤ)
    let lim' := ConstantCompletion.ordinaryLimit
      (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true)
    Ec.map (completedQuotientOrdinaryUnit T d P) ≫
        (NatIso.mapHomologicalComplex (limitFunctorComparison E.functor)
          (.up ℤ)).hom.app (Lc.obj P) ≫
        lim'.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
      ConstantCompletion.ordinaryUnit (completedCechTopology T) A d.ideal true (Ec.obj P) := by
  let := completedReductionModuleTowerFunctor_additive T d
  let := ConstantCompletion.reductionTower_additive (completedCechTopology T) A d.ideal true
  apply (ConstantCompletion.ordinaryUnit_existsUnique
    (completedCechTopology T) A d.ideal true
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)).unique ?_
    (by unfold ConstantCompletion.ordinaryUnit
        exact (ConstantCompletion.ordinaryUnit_existsUnique
          (completedCechTopology T) A d.ideal true
            ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)).exists.choose_spec)
  intro q n
  change E.functor.map ((completedQuotientOrdinaryUnit T d P).f q) ≫
    (limitFunctorComparison E.functor).hom.app
      ((completedReductionModuleTowerFunctor T d).obj (P.X q)) ≫
    limMap (e.hom.app (P.X q)) ≫ limit.π _ (op n) = _
  erw [limMap_π, limitFunctorComparison_hom_π_assoc, ← E.functor.map_comp_assoc,
    completedQuotientOrdinaryUnit_projection]
  exact hu (P.X q) n

set_option genSizeOf false in
set_option genInjectivity false in
/-- A common coefficient presentation of both completed objects and their fixed units.
Source: Stacks Tags 03CR, 05RR, 06YY, 099M and 0941.
(blueprint: def-weil-pbc-completed-constant-presentation-data). -/
structure CompletedConstantPresentationData
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) where
  equivalence : d.derived T ≌ ConstantCompletion.D
        (ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true)
  quotient : ∀ K : d.derived T,
        ∃ e : equivalence.functor.obj
            ((completedRlim T (d.completedRing T)).obj
              ((completedReductionTower T d).obj K)) ≅
            (ConstantCompletion.completion (completedCechTopology T) A d.ideal true).obj
              (equivalence.functor.obj K),
          equivalence.functor.map ((completedQuotientCompletionUnit T d).app K) ≫ e.hom =
            (ConstantCompletion.completionUnit
              (completedCechTopology T) A d.ideal true).app (equivalence.functor.obj K)
  koszul :
    let Q := @DerivedCategory.Q _ _ _
      (reductionModulesHasDerivedCategory T (d.completedRing T))
    ∀ (r : ℕ) (a : Fin r → A) (_ha : Ideal.span (Set.range a) = d.ideal)
          (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ),
        ∃ e : equivalence.functor.obj
            (Q.obj (intrinsicCompletionComplex T d r a C)) ≅
            (ConstantCompletion.completion
              (completedCechTopology T) A d.ideal true).obj
                (equivalence.functor.obj (Q.obj C)),
          equivalence.functor.map (Q.map
              (intrinsicCompletionComplexUnit T d r a C)) ≫ e.hom =
            (ConstantCompletion.completionUnit
              (completedCechTopology T) A d.ideal true).app
                (equivalence.functor.obj (Q.obj C))

-- Keep the fixed derived-category structures inlined at the published interfaces.
set_option linter.style.haveILetI false in
/-- The coefficient equivalence preserves the two completion objects and their specified units.
The Koszul clause uses an actual list generating the adic ideal.

Source: Stacks Tags 03CR, 05RR, 06YY, 099M and 0941.
(blueprint: lem-weil-pbc-completed-constant-presentation-transport).

Proof: use the scalar-preserving coefficient equivalence and its strict quotient-tower
comparison. Uniqueness of the left-derived reduction tower and the right-derived
inverse limit supplies compatible derived squares. On a K-flat representative the
actual augmentation and the quotient-completion unit have their specified normalized
formulas. The ordinary strict-limit units agree because all their finite projections
agree. The two derived squares then identify the normalized units. The actual reduction
counit is invertible on this representative, so cancellation gives the required unit
identity. Transport along a K-flat realization extends it to every derived object.
The Koszul clause is the scalar-preserving Koszul-to-constant-completion transport,
using the same derived equivalence through its localization factorization. -/
theorem completed_constant_presentation_transport
    (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    Nonempty (CompletedConstantPresentationData T d) := by
  classical
  let B := ConstantCompletion.coefficients (completedCechTopology T) A d.ideal true
  letI := reductionModulesHasDerivedCategory T (d.completedRing T)
  letI := reductionTowerHasDerivedCategory T (reductionModuleRing T (d.completedRing T))
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ ConstantCompletion.Mod B)
  obtain ⟨β, hβ, E, hE, ⟨δ⟩, eL, hu⟩ := completed_constant_coefficient_equivalence T d
  let := hE
  let Rb := ConstantCompletion.res β.inv
  let : PreservesFiniteLimits Rb := (siteRestrictScalars_exact β.inv).1
  let : PreservesFiniteColimits Rb := (siteRestrictScalars_exact β.inv).2
  let : Rb.Additive := Functor.additive_of_preserves_binary_products _
  let : (completedCechModulesEquiv T d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let := completedReductionModuleTowerFunctor_additive T d
  let G := E.congrRight (E := ℕᵒᵖ)
  let : G.functor.Additive := inferInstanceAs
    (((CategoryTheory.Functor.whiskeringRight ℕᵒᵖ _ _).obj E.functor).Additive)
  let L := completedReductionModuleTowerFunctor T d
  let L' := ConstantCompletion.reductionTower (completedCechTopology T) A d.ideal true
  let : L'.Additive := ConstantCompletion.reductionTower_additive _ _ _ true
  let R := completedTowerLimit T (d.completedRing T)
  let R' := (lim : (ℕᵒᵖ ⥤ ConstantCompletion.Mod B) ⥤ ConstantCompletion.Mod B)
  let : R'.Additive := Functor.additive_of_preserves_binary_products _
  let LF := completedReductionTower T d
  let LF' := (ConstantCompletion.quotientPresentation
    (completedCechTopology T) A d.ideal true).tower
  let RF := completedRlim T (d.completedRing T)
  let RF' := ConstantCompletion.rlim B
  let εh := completedReductionTowerCounit d T
  let ε := derivedCochainCounit L LF εh
  let ε' := (ConstantCompletion.quotientPresentation
    (completedCechTopology T) A d.ideal true).comparison
  let ηh := completedRlimUnit T (d.completedRing T)
  let η := derivedCochainRightUnit R RF ηh
  let η' := ConstantCompletion.limitComparison B
  have : LF.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (actualTowerPair T d).1
  have : LF.IsRightKanExtension ε := cochainCounit_universal L LF εh
  have : LF'.IsLeftDerivedFunctor ε' (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    (ConstantCompletion.quotientPresentation
      (completedCechTopology T) A d.ideal true).laws.1
  have : LF'.IsRightKanExtension ε' :=
    CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension LF' ε'
      (HomologicalComplex.quasiIso _ (.up ℤ))
  have : RF.IsRightDerivedFunctor ηh (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    dsimp only [RF, ηh, completedRlimUnit, completedRlim]
    infer_instance
  have : RF.IsLeftKanExtension η := cochainRightUnit_universal R RF ηh
  have : RF'.IsRightDerivedFunctor η' (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    dsimp only [RF', η', ConstantCompletion.limitComparison]
    delta ConstantCompletion.rlim
    exact (ConstantCompletion.strictLimit B).universal
  have : RF'.IsLeftKanExtension η' :=
    CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension RF' η'
      (HomologicalComplex.quasiIso _ (.up ℤ))
  let eR := limitFunctorComparison E.functor
  let κ := completedQuotientCompletionUnit T d
  let κ' := ConstantCompletion.completionUnit (completedCechTopology T) A d.ideal true
  let good := fun P : CochainComplex (reductionModules T (d.completedRing T)) ℤ ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing T) P
  have resolve : ∀ K : d.derived T, ∃ P, good P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
    intro K
    let Q : CochainComplex (reductionModules T (d.completedRing T)) ℤ ⥤ d.derived T :=
      DerivedCategory.Q
    let C := Q.objPreimage K
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := d.completedRing T) C
    let := hf
    exact ⟨P, hP, ⟨asIso (Q.map f) ≪≫ Q.objObjPreimageIso K⟩⟩
  obtain ⟨F, ⟨α⟩, hQ⟩ := normalized_derived_completion_equivalence
    E G L L' R R' LF LF' RF RF' ε ε' η η' eL eR κ κ' good resolve
    (completedQuotientOrdinaryUnit T d)
    (ConstantCompletion.ordinaryUnit (completedCechTopology T) A d.ideal true)
    (completedQuotientUnitNormalization T d)
    (ConstantCompletion.constantCompletionUnit_normalization_all
      (completedCechTopology T) A d.ideal true)
    (comparisonOrdinaryCompletionUnit T d E eL hu)
  let δD : F.functor ≅ (completedCechDerivedEquiv T d).functor ⋙
      ConstantCompletion.dres β.inv :=
    α ≪≫ CategoryTheory.Functor.mapDerivedCategoryNatIso δ ≪≫
      (CategoryTheory.Functor.mapDerivedCategoryCompIso
        (completedCechModulesEquiv T d).functor Rb).symm
  refine ⟨{
    equivalence := F
    quotient := hQ
    koszul := fun r a ha C ↦ completed_koszul_constant_transport
      T d β hβ F.functor δD r a ha C }⟩

end AlgebraicGeometry.Scheme
