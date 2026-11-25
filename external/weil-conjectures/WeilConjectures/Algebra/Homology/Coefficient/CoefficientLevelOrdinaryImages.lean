/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import all WeilConjectures.Algebra.Homology.CoefficientConstantImages.CoefficientConstantRingImages
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison
import all WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import all WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import all WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.LinearAlgebra.FreeModule.Basic
import all WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement

/-! # Ordinary geometric images of strict coefficient systems

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

/-- Levelwise ordinary lifts, before forming the category of strict systems.
Source: Stacks 03D7; Zheng Construction 4.1
(blueprint: lem-pur-coefficient-level-ordinary-images). -/
structure CoefficientLevelOrdinaryImage where
  singleton : L.obj ((constantSheaf J (Type w)).obj PUnit) ≅
    (constantSheaf K (Type w)).obj PUnit
  lift : ∀ n, AlgebraicInverseImage L
    (coefficientQuotientSheaf (J := J) O ell n)
    (coefficientQuotientSheaf (J := K) O ell n)
  constants : ∀ n x,
    L.map (coefficientConstantSection (J := J) O ell n x) ≫ (lift n).ringUnderlying.hom =
      singleton.hom ≫ coefficientConstantSection (J := K) O ell n x
  [inverseAdditive : ∀ n, (lift n).modules.Additive]
  inverseExact : ∀ n, PreservesFiniteLimits (lift n).modules ∧
    PreservesFiniteColimits (lift n).modules
  right : ∀ n, coefficientLevelModules (J := K) O ell n ⥤
    coefficientLevelModules (J := J) O ell n
  [rightAdditive : ∀ n, (right n).Additive]
  rightUnderlying : ∀ n, right n ⋙ coefficientUnderlying (J := J) O ell n ≅
    coefficientUnderlying (J := K) O ell n ⋙ V
  levelAdj : ∀ n, (lift n).modules ⊣ right n
  levelTranspose : ∀ n M N (f : (lift n).modules.obj M ⟶ N),
    (coefficientUnderlying (J := J) O ell n).map ((levelAdj n).homEquiv M N f) ≫
      (rightUnderlying n).hom.app N =
    adj.homEquiv _ _ ((lift n).moduleUnderlying.inv.app M ≫
      (coefficientUnderlying (J := K) O ell n).map f)
  restrictInverse : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := J) O ell h ⋙ (lift m).modules ≅
      (lift n).modules ⋙ coefficientRestriction (J := K) O ell h
  restrictInverseUnderlying : ∀ {m n : ℕ} (h : n ≤ m) M,
    (coefficientUnderlying (J := K) O ell m).map ((restrictInverse h).hom.app M) ≫
      (coefficientRestrictionUnderlying (J := K) O ell h).hom.app
        ((lift n).modules.obj M) ≫ (lift n).moduleUnderlying.hom.app M =
    (lift m).moduleUnderlying.hom.app ((coefficientRestriction (J := J) O ell h).obj M) ≫
      L.map ((coefficientRestrictionUnderlying (J := J) O ell h).hom.app M)
  restrictRight : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := K) O ell h ⋙ right m ≅
      right n ⋙ coefficientRestriction (J := J) O ell h
  restrictTranspose : ∀ {m n : ℕ} (h : n ≤ m) M N
    (f : (lift n).modules.obj M ⟶ N),
    (levelAdj m).homEquiv _ _
      ((restrictInverse h).hom.app M ≫ (coefficientRestriction (J := K) O ell h).map f) =
    (coefficientRestriction (J := J) O ell h).map ((levelAdj n).homEquiv _ _ f) ≫
      (restrictRight h).inv.app N

attribute [instance] CoefficientLevelOrdinaryImage.inverseAdditive
  CoefficientLevelOrdinaryImage.rightAdditive

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})] in
private theorem normalizedModuleAdjunction
    [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (I : AlgebraicInverseImage L R S) :
    ∃ (P : SheafOfModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⥤
        SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (e : P ⋙ toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}) ≅
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})) ⋙ V)
      (a : I.modules ⊣ P),
      ∀ M N (f : I.modules.obj M ⟶ N),
        (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
            (a.homEquiv M N f) ≫ e.hom.app N =
          adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫
            (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map f) := by
  let g : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)) :=
    ⟨L, V, adj, inferInstance⟩
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  obtain ⟨P, e, hops⟩ := CategoryTheory.SheafFreeModule.rawRight g I
  obtain ⟨E, hE⟩ := CategoryTheory.SheafFreeModule.rawHom g I P e hops
  let U := toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})
  let W := toSheaf ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⋙
    sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})
  have hleft {M' M} {N} (f : M' ⟶ M) (h : I.modules.obj M ⟶ N) :
      E M' N (I.modules.map f ≫ h) = f ≫ E M N h := by
    apply U.map_injective
    apply (cancel_mono (e.hom.app N)).mp
    rw [hE, U.map_comp, Category.assoc, hE, W.map_comp]
    have hn : I.moduleUnderlying.inv.app M' ≫ W.map (I.modules.map f) =
        L.map (U.map f) ≫ I.moduleUnderlying.inv.app M :=
      (I.moduleUnderlying.inv.naturality f).symm
    rw [← Category.assoc, hn, Category.assoc, adj.homEquiv_naturality_left]
  let core : Adjunction.CoreHomEquiv I.modules P :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro M' M N f h
        apply (E M' N).injective
        rw [Equiv.apply_symm_apply, hleft, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M N N' h f
        apply U.map_injective
        apply (cancel_mono (e.hom.app N')).mp
        have hn : U.map (P.map f) ≫ e.hom.app N' =
            e.hom.app N ≫ V.map (W.map f) := e.hom.naturality f
        rw [hE, U.map_comp, Category.assoc, hn, ← Category.assoc, hE, W.map_comp]
        simpa only [Category.assoc] using
          adj.homEquiv_naturality_right (I.moduleUnderlying.inv.app M ≫ W.map h) (W.map f) }
  refine ⟨P, e, Adjunction.mkOfHomEquiv core, ?_⟩
  intro M N f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact hE M N f

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [EssentiallySmall.{w} C] in
private theorem sheafifyLift_eval
    {P : Cᵒᵖ ⥤ Type w} (T : Sheaf J (Type w)) (eta : P ⟶ T.obj)
    (U : Cᵒᵖ) (x : P.obj U) :
    ((((sheafificationAdjunction J (Type w)).homEquiv P T).symm eta).hom.app U)
        ((toSheafify J P).app U x) = eta.app U x := by
  exact congrArg (fun f : P ⟶ T.obj ↦ f.app U x)
    (toSheafify_sheafifyLift J eta T.property)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem coefficientConstantSection_eval (n : ℕ)
    (x : O ⧸ (Ideal.span {ell}) ^ (n + 1)) (U : Cᵒᵖ)
    (y : ((constantSheaf J (Type w)).obj PUnit.{w + 1}).obj.obj U) :
    (coefficientConstantSection (J := J) O ell n x).hom.app U y =
      (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span {ell}) ^ (n + 1))))).app U x := by
  rw [CoefficientConstantImages.point_section.{w} J U y]
  exact sheafifyLift_eval (P := (Functor.const Cᵒᵖ).obj PUnit.{w + 1})
    ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj
      (coefficientQuotientSheaf (J := J) O ell n))
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{w + 1}) ↦ x)) ≫
      whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span {ell}) ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{w})) U PUnit.unit

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
include V adj in
private theorem algebraicInverseImage_exact [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (I : AlgebraicInverseImage L R S) :
    PreservesFiniteLimits I.modules ∧ PreservesFiniteColimits I.modules := by
  let g : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)) :=
    ⟨L, V, adj, inferInstance⟩
  have h := ((CategoryTheory.GeometricMorphism.geometric_inverse_image_exact J K g).2.2 R).2 S
    (CategoryTheory.GeometricMorphism.inverseImageUniverses
      (C := C) (D := D) (J := J) (K := K) (L := L) (R := R) (S := S) I)
  exact (exactFunctor_iff _).mp h.1

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
include V adj in
private theorem normalizedCoefficientLifts [PreservesFiniteLimits L] :
    ∃ (κ : constantSheaf J (Type w) ⋙ L ≅ constantSheaf K (Type w))
      (I : ∀ n : ℕ, AlgebraicInverseImage L
        (coefficientQuotientSheaf (J := J) O ell n)
        (coefficientQuotientSheaf (J := K) O ell n)),
      (∀ n (x : O ⧸ (Ideal.span {ell}) ^ (n + 1)),
        L.map (coefficientConstantSection (J := J) O ell n x) ≫
            (I n).ringUnderlying.hom =
          (κ.app PUnit).hom ≫ coefficientConstantSection (J := K) O ell n x) ∧
      ∀ {m n : ℕ} (h : n ≤ m),
        L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (coefficientQuotientMap (J := J) O ell h)) ≫ (I n).ringUnderlying.hom =
        (I m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (coefficientQuotientMap (J := K) O ell h) := by
  classical
  let : J.PreservesSheafification (CategoryTheory.forget CommRingCat.{w}) :=
    CoefficientConstantImages.ringForgetSheafification J
  let : K.PreservesSheafification (CategoryTheory.forget CommRingCat.{w}) :=
    CoefficientConstantImages.ringForgetSheafification K
  obtain ⟨κ, hκ⟩ :=
    CoefficientConstantImages.coefficientConstantRingImages.{w} J K L V adj
  let A (n : ℕ) := CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))
  have hquot (n : ℕ) :
      ∃ I : AlgebraicInverseImage L
          (coefficientQuotientSheaf (J := J) O ell n)
          (coefficientQuotientSheaf (J := K) O ell n),
        I.ringUnderlying =
          L.mapIso ((constantCommuteCompose J
            (CategoryTheory.forget CommRingCat.{w})).app (A n)) ≪≫
            κ.app (A n) ≪≫ ((constantCommuteCompose K
              (CategoryTheory.forget CommRingCat.{w})).app (A n)).symm := hκ (A n)
  choose I hI using hquot
  have hring {m n : ℕ} (h : n ≤ m) :
      L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
        (coefficientQuotientMap (J := J) O ell h)) ≫ (I n).ringUnderlying.hom =
      (I m).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
          (coefficientQuotientMap (J := K) O ell h) := by
    let φ : A m ⟶ A n := CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
    have hn := (CoefficientConstantImages.constantRingSetComparison.{w} J K L κ).hom.naturality φ
    simp only [Functor.comp_map,
      CoefficientConstantImages.constantRingSetComparison_hom_app] at hn
    conv_lhs => arg 2; rw [hI n]
    conv_rhs => arg 1; rw [hI m]
    exact hn
  refine ⟨κ, I, ?_, hring⟩
  · intro n x
    conv_lhs => arg 2; rw [hI n]
    ext W y
    have hs := CoefficientConstantImages.canonicalConstantSectionComparison.{w}
      J K L κ (A n) x _ (coefficientConstantSection (J := J) O ell n x)
      (fun U z ↦ coefficientConstantSection_eval O ell n x U z) W y
    have ht := coefficientConstantSection_eval (J := K) O ell n x W
      ((κ.app PUnit).hom.hom.app W y)
    rw [CoefficientConstantImages.constantRingSetComparison_hom_app] at hs
    (convert hs.trans ht.symm using 1; rfl)

private abbrev ordinaryRingModules
    {T : Type u} [Category.{v} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) :=
  SheafOfModules.{w} ((sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

private abbrev ordinaryRingSets
    {T : Type u} [Category.{v} T] {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [τ.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) : ordinaryRingModules R ⥤ Sheaf τ (Type w) :=
  toSheaf _ ⋙ sheafCompose τ (CategoryTheory.forget AddCommGrpCat.{w})

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [EssentiallySmall.{w} C] in
/-- Scalar restriction is the identity after forgetting the scalar action. -/
private theorem ordinaryScalarRestriction_hom_app
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) (M : ordinaryRingModules S) :
    (isoWhiskerRight (siteScalarUnderlyingIso φ)
      (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}))).hom.app M = 𝟙 _ := by
  rfl

-- Normalizing the mate across four module categories needs additional reductions.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)] in
private theorem normalizedRestrictionMates [PreservesFiniteLimits L]
    (R : ℕ → Sheaf J CommRingCat.{w}) (S : ℕ → Sheaf K CommRingCat.{w})
    (qJ : ∀ {m n : ℕ}, n ≤ m → (R m ⟶ R n))
    (qK : ∀ {m n : ℕ}, n ≤ m → (S m ⟶ S n))
    (I : ∀ n, AlgebraicInverseImage L (R n) (S n))
    (P : ∀ n, ordinaryRingModules (S n) ⥤ ordinaryRingModules (R n))
    (e : ∀ n, P n ⋙ ordinaryRingSets (R n) ≅ ordinaryRingSets (S n) ⋙ V)
    (a : ∀ n, (I n).modules ⊣ P n)
    (ha : ∀ n M N (f : (I n).modules.obj M ⟶ N),
      (ordinaryRingSets (R n)).map ((a n).homEquiv M N f) ≫ (e n).hom.app N =
        adj.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (ordinaryRingSets (S n)).map f))
    (hring : ∀ {m n : ℕ} (h : n ≤ m),
      L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map (qJ h)) ≫
          (I n).ringUnderlying.hom =
        (I m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (qK h)) :
    let resJ := fun {m n : ℕ} (h : n ≤ m) ↦ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (qJ h))
    let resK := fun {m n : ℕ} (h : n ≤ m) ↦ restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map (qK h))
    ∃ (r : ∀ {m n : ℕ} (h : n ≤ m), resJ h ⋙ (I m).modules ≅ (I n).modules ⋙ resK h)
      (t : ∀ {m n : ℕ} (h : n ≤ m), resK h ⋙ P m ≅ P n ⋙ resJ h),
      (∀ {m n : ℕ} (h : n ≤ m) M,
        (ordinaryRingSets (S m)).map ((r h).hom.app M) ≫
          (isoWhiskerRight (siteScalarUnderlyingIso (qK h))
            (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w}))).hom.app
              ((I n).modules.obj M) ≫ (I n).moduleUnderlying.hom.app M =
            (I m).moduleUnderlying.hom.app ((resJ h).obj M) ≫
              L.map ((isoWhiskerRight (siteScalarUnderlyingIso (qJ h))
                (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}))).hom.app M)) ∧
      ∀ {m n : ℕ} (h : n ≤ m) M N (f : (I n).modules.obj M ⟶ N),
        (a m).homEquiv _ _ ((r h).hom.app M ≫ (resK h).map f) =
          (resJ h).map ((a n).homEquiv M N f) ≫ (t h).inv.app N := by
  classical
  dsimp only
  let resJ := fun {m n : ℕ} (h : n ≤ m) ↦ restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map (qJ h))
  let resK := fun {m n : ℕ} (h : n ≤ m) ↦ restrictScalars
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map (qK h))
  have hres {m n : ℕ} (h : n ≤ m) :=
    InverseImageScalarRestriction.exists_comparison (I m) (I n)
      (qJ h)
      (qK h) (hring h)
  choose ρ hρ using fun {m n : ℕ} (h : n ≤ m) ↦ hres h
  let r {m n : ℕ} (h : n ≤ m) :
      resJ h ⋙ (I m).modules ≅
        (I n).modules ⋙ resK h := (ρ h).symm
  have hr {m n : ℕ} (h : n ≤ m)
      (M : ordinaryRingModules (R n)) :
      (ordinaryRingSets (S m)).map ((r h).hom.app M) ≫
          (I n).moduleUnderlying.hom.app M =
        (I m).moduleUnderlying.hom.app
          ((resJ h).obj M) := by
    apply (cancel_epi ((ordinaryRingSets (S m)).map
      ((ρ h).hom.app M))).mp
    change (ordinaryRingSets (S m)).map ((ρ h).hom.app M) ≫
        (ordinaryRingSets (S m)).map ((ρ h).inv.app M) ≫
          (I n).moduleUnderlying.hom.app M = _
    erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (hρ h M).symm
  have hri {m n : ℕ} (h : n ≤ m)
      (M : ordinaryRingModules (R n)) :
      (I m).moduleUnderlying.inv.app
          ((resJ h).obj M) ≫
        (ordinaryRingSets (S m)).map ((r h).hom.app M) =
      (I n).moduleUnderlying.inv.app M := by
    apply (cancel_mono ((I n).moduleUnderlying.hom.app M)).mp
    (erw [Category.assoc, hr h M, Iso.inv_hom_id_app, Iso.inv_hom_id_app]; rfl)
  let δ {m n : ℕ} (h : n ≤ m) :
      P n ⋙ resJ h ⟶
        resK h ⋙ P m :=
    whiskerLeft (P n ⋙ resJ h) (a m).unit ≫
      whiskerRight (whiskerLeft (P n) (r h).hom) (P m) ≫
      whiskerRight (whiskerRight (a n).counit
        (resK h)) (P m)
  have hδ {m n : ℕ} (h : n ≤ m)
      (N : ordinaryRingModules (S n)) :
      (δ h).app N = (a m).homEquiv _ _
        ((r h).hom.app ((P n).obj N) ≫
          (resK h).map ((a n).counit.app N)) := by
    simp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Adjunction.homEquiv_unit,
      Functor.map_comp]
  have heδ {m n : ℕ} (h : n ≤ m)
      (N : ordinaryRingModules (S n)) :
      (ordinaryRingSets (R m)).map ((δ h).app N) ≫
          (e m).hom.app ((resK h).obj N) =
        (e n).hom.app N := by
    erw [hδ h N, ha m]
    erw [Functor.map_comp, ← Category.assoc, hri h ((P n).obj N)]
    have hn := ha n ((P n).obj N) N ((a n).counit.app N)
    have hc : (a n).homEquiv ((P n).obj N) N ((a n).counit.app N) = 𝟙 _ := by
      rw [← (a n).homEquiv_symm_id N]
      exact Equiv.apply_symm_apply _ _
    rw [hc, CategoryTheory.Functor.map_id, Category.id_comp] at hn
    (convert hn.symm using 1; rfl)
  have hiδ {m n : ℕ} (h : n ≤ m)
      (N : ordinaryRingModules (S n)) : IsIso ((δ h).app N) := by
    have hf : (ordinaryRingSets (R m)).map ((δ h).app N) =
        (e n).hom.app N ≫
          (e m).inv.app ((resK h).obj N) := by
      apply (cancel_mono ((e m).hom.app _)).mp
      erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      exact heδ h N
    let ee :
        (ordinaryRingSets (R m)).obj
            ((P n ⋙ resJ h).obj N) ≅
          (ordinaryRingSets (R m)).obj
            ((resK h ⋙ P m).obj N) :=
      (e n).app N ≪≫ ((e m).app ((resK h).obj N)).symm
    have hee : (ordinaryRingSets (R m)).map ((δ h).app N) = ee.hom := hf
    have : IsIso ((ordinaryRingSets (R m)).map ((δ h).app N)) := by
      rw [hee]
      infer_instance
    exact isIso_of_reflects_iso _ (ordinaryRingSets (R m))
  let t {m n : ℕ} (h : n ≤ m) :
      resK h ⋙ P m ≅
        P n ⋙ resJ h :=
    let : ∀ N, IsIso ((δ h).app N) := hiδ h
    let : IsIso (δ h) := NatIso.isIso_of_isIso_app (δ h)
    (asIso (δ h)).symm
  refine ⟨r, t, ?_, ?_⟩
  · intro m n h M
    simp only [ordinaryScalarRestriction_hom_app]
    erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    exact hr h M
  · intro m n h M N f
    change (a m).homEquiv _ _ ((r h).hom.app M ≫
        (resK h).map f) =
      (resJ h).map ((a n).homEquiv M N f) ≫ (δ h).app N
    apply (ordinaryRingSets (R m)).map_injective
    apply (cancel_mono ((e m).hom.app
      ((resK h).obj N))).mp
    rw [ha m]
    simp only [Functor.map_comp, Category.assoc]
    rw [heδ h N]
    change adj.homEquiv _ _
        ((I m).moduleUnderlying.inv.app _ ≫
          ((ordinaryRingSets (S m)).map ((r h).hom.app M) ≫
            (ordinaryRingSets (S n)).map f)) =
      (ordinaryRingSets (R n)).map ((a n).homEquiv M N f) ≫
        (e n).hom.app N
    (erw [← Category.assoc, hri h M, ha n]; rfl)

/-- Constant-coefficient level lifts, coherent with scalar restriction.
Source: Stacks 00YV, 03D2, 03DA, 03DB and 03D7; Zheng Construction 4.1.

Proof: one natural comparison between the constant-set inverse images and the
constant sets, obtained from the global-section Hom equivalences and uniqueness of
left adjoints, carries algebraic lifts of every constant quotient ring
(`coefficientConstantRingImages`); its naturality in ring maps gives the quotient
squares, and evaluation on the constant singleton fixes every constant generator.
For each lift, the normalized module right adjoint over V restricts the sheaf
adjunction to linear maps, with the displayed underlying transpose. Geometric
inverse images are exact, hence additive, and the right adjoint is additive. For a
quotient map, the normalized inverse-image scalar-restriction comparison gives
restrictInverse; its mate under the level adjunctions is restrictRight, invertible
because its underlying map is the composite of the right-underlying isomorphisms
and forgetting reflects isomorphisms; faithfulness gives restrictTranspose. These
comparisons hold for every pair of indices, including equal indices and the zero
quotient ring.
(blueprint: lem-pur-coefficient-level-ordinary-images). -/
theorem coefficientLevelOrdinaryImage_exists [PreservesFiniteLimits L] :
    Nonempty (CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) := by
  classical
  obtain ⟨κ, I, hconst, hring⟩ := normalizedCoefficientLifts O ell L V adj
  choose P e a ha using fun n ↦ normalizedModuleAdjunction L V adj (I n)
  have hex (n : ℕ) : PreservesFiniteLimits (I n).modules ∧
      PreservesFiniteColimits (I n).modules := algebraicInverseImage_exact L V adj (I n)
  let (n : ℕ) : (I n).modules.Additive :=
    let := (hex n).1
    Functor.additive_of_preserves_binary_products (I n).modules
  let (n : ℕ) : (P n).Additive := (a n).right_adjoint_additive
  obtain ⟨r, t, hr, ht⟩ := normalizedRestrictionMates L V adj
    (fun n ↦ coefficientQuotientSheaf (J := J) O ell n)
    (fun n ↦ coefficientQuotientSheaf (J := K) O ell n)
    (fun h ↦ coefficientQuotientMap (J := J) O ell h)
    (fun h ↦ coefficientQuotientMap (J := K) O ell h) I P e a ha (@hring)
  refine ⟨{
    singleton := κ.app PUnit
    lift := I
    constants := hconst
    inverseAdditive := fun n ↦ inferInstance
    inverseExact := hex
    right := P
    rightAdditive := fun n ↦ inferInstance
    rightUnderlying := e
    levelAdj := a
    levelTranspose := ha
    restrictInverse := r
    restrictInverseUnderlying := ?_
    restrictRight := t
    restrictTranspose := ?_ }⟩
  · intro m n h M
    simpa only [coefficientRestrictionUnderlying] using hr h M
  · exact ht

end SheafOfModules
