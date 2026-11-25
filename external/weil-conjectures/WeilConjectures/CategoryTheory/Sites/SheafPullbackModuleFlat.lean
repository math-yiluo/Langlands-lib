/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-!
# Internal inverse image of module objects along a representably flat functor

Let `U : C ⥤ D` be a continuous and representably flat functor of sites, and let
`ρ : S ⟶ U^* R` be an isomorphism of commutative ring objects in abelian sheaves, where `U^*`
is the sheaf pullback `Functor.sheafPullbackConstruction.sheafPullback U`. We show:

* `exists_sectionModuleAlgebraicInverseImage`: the internal inverse image of module objects
  `Mod.mapModComap ρ`, transported to sheaves of modules over the section ring sheaves, is the
  module part of an algebraic inverse image along the set-valued sheaf pullback.
* `preservesFlat_mapModComap`: the internal inverse image `Mod.mapModComap ρ` preserves flat
  module objects.

This generalizes the pro-étale base change of
`WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage` and
`WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat`.

Source: Stacks Project, Tags 00YV, 03D2, 05VD.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct

namespace CategoryTheory.Functor.sheafPullbackConstruction

set_option backward.isDefEq.respectTransparency false

section Site

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}

private noncomputable def sheafUliftIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Type*} [Category A] (G : A ⥤ Type (u + 1))
    [J.HasSheafCompose G] [J.HasSheafCompose (G ⋙ uliftFunctor.{u + 1, u + 1})] :
    sheafCompose J (G ⋙ uliftFunctor.{u + 1, u + 1}) ≅ sheafCompose J G :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun W ↦ uliftTrivial (G.obj (M.obj.obj W)))
      (by intros; rfl))) (by intros; rfl)

private noncomputable def sectionRingUnderlyingIso
    (R : Sheaf K Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (sheafCompose K
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K R) ≅
    (sheafCompose K (CategoryTheory.forget Ab.{u + 1})).obj R :=
  (sheafUliftIso K (CategoryTheory.forget CommRingCat.{u + 1})).app _

private noncomputable def sumSections
    {T : Sheaf K (Type (u + 1))}
    (A : Sheaf K Ab.{u + 1})
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ (@id (A.obj.obj W) (a.hom.app W x)) +
       (@id (A.obj.obj W) (b.hom.app W x)))
     naturality := fun V W q ↦ by
       ext x
       change _ = (A.obj.map q).hom (_ + _)
       exact (congrArg₂ (fun (a b : A.obj.obj W) ↦ a + b)
         (ConcreteCategory.congr_hom (a.hom.naturality q) x)
         (ConcreteCategory.congr_hom (b.hom.naturality q) x)).trans
         (_root_.map_add (A.obj.map q).hom _ _).symm }⟩

private noncomputable def zeroSections
    (T : Sheaf K (Type (u + 1)))
    (A : Sheaf K Ab.{u + 1}) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : A.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       exact (_root_.map_zero (A.obj.map q).hom).symm }⟩

private theorem section_mul
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Dᵒᵖ) (a b : S.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj W
    @HMul.hMul RX RX RX inferInstance a b =
      (μ[S]).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf K Ab.{u + 1}) S S).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem section_one
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Dᵒᵖ) :
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj W
    (1 : RX) = (η[S]).hom.app W ((Functor.LaxMonoidal.ε
      (sheafToPresheaf K Ab.{u + 1})).app W (ULift.up 1)) := rfl

private theorem section_smul
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf K Ab.{u + 1}) S)
    (W : Dᵒᵖ) (a : S.obj.obj W) (b : M.X.obj.obj W) :
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      K S).obj M).val.obj W
    @HSMul.hSMul RX MX MX inferInstance a b =
      (Mod.act M.X).hom.app W ((Functor.LaxMonoidal.μ
        (sheafToPresheaf K Ab.{u + 1}) S M.X).app W
          (a ⊗ₜ[ℤ] b)) := rfl

private theorem section_comap_smul
    (R S : Sheaf K Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (M : Mod (Sheaf K Ab.{u + 1}) S)
    (W : Dᵒᵖ) (a : R.obj.obj W) (b : M.X.obj.obj W) :
    let RR := (InternalAbelianSheafModule.sectionRings K R).obj W
    let RS := (InternalAbelianSheafModule.sectionRings K S).obj W
    let MR := ((InternalAbelianSheafModule.sectionModuleFunctor
      K R).obj ((Mod.comap φ).obj M)).val.obj W
    let MS := ((InternalAbelianSheafModule.sectionModuleFunctor
      K S).obj M).val.obj W
    @HSMul.hSMul RR MR MR inferInstance a b =
      @HSMul.hSMul RS MS MS inferInstance (φ.hom.app W a) b := by
  let H := sheafToPresheaf K Ab.{u + 1}
  have he : Functor.LaxMonoidal.μ H R M.X ≫
      H.map (Mod.act ((Mod.comap φ).obj M).X) =
      H.map φ ▷ H.obj M.X ≫ Functor.LaxMonoidal.μ H S M.X ≫ H.map (Mod.act M.X) := by
    change _ ≫ H.map (φ ▷ M.X ≫ Mod.act M.X) = _
    rw [Functor.map_comp, Functor.LaxMonoidal.μ_natural_left_assoc]
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app he W) (a ⊗ₜ[ℤ] b)
  change (Mod.act ((Mod.comap φ).obj M).X).hom.app W
      ((Functor.LaxMonoidal.μ H R M.X).app W (a ⊗ₜ[ℤ] b)) =
    (Mod.act M.X).hom.app W ((Functor.LaxMonoidal.μ H S M.X).app W
      ((φ.hom.app W ▷ M.X.obj.obj W) (a ⊗ₜ[ℤ] b))) at ht
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul] at ht
  exact ht

private noncomputable def sectionRingMap
    {R S : Sheaf K Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (g : R ⟶ S) [IsMonHom g] (W : Dᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings K R).obj W →+*
      (InternalAbelianSheafModule.sectionRings K S).obj W := by
  let H := (sheafToPresheaf K Ab.{u + 1}).mapCommMon ⋙
    (Monoidal.commMonFunctorCategoryEquivalence Dᵒᵖ Ab.{u + 1}).functor
  exact InternalAbelianSheafModule.ringHom
    ((H.map (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) ⟨g⟩)).app W).hom.hom

private theorem sectionModuleCounit_smul
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R)))
      (W : Cᵒᵖ)
      (a : (InternalAbelianSheafModule.sectionRings J R).obj W)
      (b : M.val.obj W),
    let RR := (InternalAbelianSheafModule.sectionRings J R).obj W
    let NM := ((InternalAbelianSheafModule.sectionModuleFunctor
      J R).obj (eY.inverse.obj M)).val.obj W
    ((eY.counitIso.inv.app M).val.app W).hom (a • b) =
      @HSMul.hSMul RR NM NM inferInstance a
        (((eY.counitIso.inv.app M).val.app W).hom b) := by
  intro eY M W a b
  exact ((eY.counitIso.inv.app M).val.app W).hom.map_smul a b

private noncomputable def ringMulSections
    (R : Sheaf K CommRingCat.{u + 1})
    (T : Sheaf K (Type (u + 1)))
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) *
         (@id (R.obj.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = (R.obj.map q).hom (_ * _)
       exact (congrArg₂ (fun (a b : R.obj.obj W) ↦ a * b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (_root_.map_mul (R.obj.map q).hom _ _).symm }⟩
private noncomputable def moduleSMulSections
    (R : Sheaf K CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose K
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (T : Sheaf K (Type (u + 1)))
    (a : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R)
    (b : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj ((SheafOfModules.toSheaf _).obj M)) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj ((SheafOfModules.toSheaf _).obj M) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) •
         (@id (M.val.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = M.val.map q (_ • _)
       exact (congrArg₂ (fun (a : R.obj.obj W) (b : M.val.obj W) ↦ a • b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (M.val.map_smul q _ _).symm }⟩

private noncomputable def ringAddSections
    (R : Sheaf K CommRingCat.{u + 1})
    (T : Sheaf K (Type (u + 1)))
    (a b : T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ ULift.up
       ((@id (R.obj.obj W) (a.hom.app W x).down) +
         (@id (R.obj.obj W) (b.hom.app W x).down)))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       change _ = (R.obj.map q).hom (_ + _)
       exact (congrArg₂ (fun (a b : R.obj.obj W) ↦ a + b)
         (congrArg ULift.down (ConcreteCategory.congr_hom (a.hom.naturality q) x))
         (congrArg ULift.down (ConcreteCategory.congr_hom (b.hom.naturality q) x))).trans
         (_root_.map_add (R.obj.map q).hom _ _).symm }⟩
private noncomputable def ringNatSections
    (R : Sheaf K CommRingCat.{u + 1})
    (T : Sheaf K (Type (u + 1))) (n : ℕ) :
    T ⟶ (sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1} ⋙
      uliftFunctor.{u + 1, u + 1})).obj R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ ULift.up (n : R.obj.obj W))
     naturality := fun V W q ↦ by
       ext x
       apply ULift.ext
       exact (_root_.map_natCast (R.obj.map q).hom n).symm }⟩

/- Site-flatness of sheaves of modules is invariant under isomorphism, via the local
equational criterion. -/
private theorem isFlatOnSite_of_iso (R' : Sheaf K CommRingCat.{u + 1})
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')}
    (e : M ≅ N) (hN : SheafOfModules.IsFlatOnSite (J := K) (R := R') N) :
    SheafOfModules.IsFlatOnSite (J := K) (R := R') M := by
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
    R' M).mpr
  intro U n a s h
  let s' (i : Fin n) := e.hom.val.app (Opposite.op U) (s i)
  have hs : (∑ i, a i • s' i) = 0 := by
    change (∑ i, a i • (e.hom.val.app (Opposite.op U)) (s i)) = 0
    simpa only [_root_.map_sum, _root_.map_smul, _root_.map_zero] using
      congrArg (fun z ↦ e.hom.val.app (Opposite.op U) z) h
  obtain ⟨S, hS, hlocal⟩ :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      R' N).mp hN U n a s' hs
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, ht, hb⟩ := hlocal V f hf
  refine ⟨l, b, fun j ↦ e.inv.val.app (Opposite.op V) (t j), ?_, hb⟩
  intro i
  have hi := congrArg (fun z ↦ e.inv.val.app (Opposite.op V) z) (ht i)
  simp only [_root_.map_sum, _root_.map_smul] at hi
  have hinv : e.inv.val.app (Opposite.op V)
      (e.hom.val.app (Opposite.op V) (M.val.map f.op (s i))) =
      M.val.map f.op (s i) := by
    have h := congrArg (fun z ↦ z.val.app (Opposite.op V) (M.val.map f.op (s i))) e.hom_inv_id
    exact h
  rw [← PresheafOfModules.naturality_apply] at hi
  exact hinv.symm.trans hi

end Site

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
  (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]

section Comparison

/- The sheaf pullback is lax braided: the compatibility with the braiding is the mate of the
one of the lax braided pushforward. In particular it sends commutative ring objects to
commutative ring objects. -/
private noncomputable local instance laxBraided_sheafPullback :
    (sheafPullback U Ab.{u + 1} J K).LaxBraided where
  braided F G := by
    let adj := sheafAdjunctionContinuous U Ab.{u + 1} J K
    let P := sheafPullback U Ab.{u + 1} J K
    have h : Functor.OplaxMonoidal.δ P F G ≫ (β_ (P.obj F) (P.obj G)).hom =
        P.map (β_ F G).hom ≫ Functor.OplaxMonoidal.δ P G F := by
      change (adj.homEquiv _ _).symm ((adj.unit.app F ⊗ₘ adj.unit.app G) ≫
          Functor.LaxMonoidal.μ (U.sheafPushforwardContinuous Ab.{u + 1} J K) _ _) ≫ _ =
        _ ≫ (adj.homEquiv _ _).symm ((adj.unit.app G ⊗ₘ adj.unit.app F) ≫
          Functor.LaxMonoidal.μ (U.sheafPushforwardContinuous Ab.{u + 1} J K) _ _)
      rw [← Adjunction.homEquiv_naturality_right_symm]
      erw [← Adjunction.homEquiv_naturality_left_symm]
      rw [Category.assoc, Functor.LaxBraided.braided]
      erw [BraidedCategory.braiding_naturality_assoc]
      rfl
    rw [← cancel_epi (Functor.OplaxMonoidal.δ P F G), Functor.Monoidal.δ_μ_assoc,
      reassoc_of% h, Functor.Monoidal.δ_μ, Category.comp_id]

/- The concrete inverse image and its comparison after forgetting abelian groups. -/
private noncomputable def setPullback : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)) :=
  sheafPullback U (Type (u + 1)) J K
private noncomputable def pullbackForgetIso :
    (sheafPullback U Ab.{u + 1} J K) ⋙ sheafCompose K
        (CategoryTheory.forget Ab.{u + 1}) ≅
      sheafCompose J (CategoryTheory.forget Ab.{u + 1}) ⋙
        setPullback J K U := by
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Cᵒᵖ ⥤ Ab.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  let eLan := G.lanCompIsoOfPreserves U.op
  let eSh := sheafComposeNatIso K G
    (sheafificationAdjunction _ Ab.{u + 1})
    (sheafificationAdjunction _ (Type (u + 1)))
  exact Functor.isoWhiskerLeft
      (sheafToPresheaf J Ab.{u + 1} ⋙ U.op.lan) eSh.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J Ab.{u + 1})
      (Functor.isoWhiskerRight eLan
        (presheafToSheaf K (Type (u + 1))))

private noncomputable def sectionRingPullbackIso
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    let L := setPullback J K U
    L.obj ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R)) ≅
    (sheafCompose K
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S) :=
  (setPullback J K U).mapIso (sectionRingUnderlyingIso R) ≪≫
    ((pullbackForgetIso J K U).app R).symm ≪≫
    (sheafCompose K
      (CategoryTheory.forget Ab.{u + 1})).mapIso (asIso ρ).symm ≪≫
    (sectionRingUnderlyingIso S).symm

private noncomputable def sectionModulePullbackIso
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S
    (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor) ⋙ SheafOfModules.toSheaf _ ⋙
      sheafCompose K
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1}) ≅
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})) ⋙
        setPullback J K U := by
  dsimp only
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S
  let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
  let UX := sheafCompose K (CategoryTheory.forget Ab.{u + 1})
  let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
  let RY := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R)
  let F := SheafOfModules.toSheaf RY ⋙ UY
  let euX := sheafUliftIso K (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
  let e₁ : I ⋙ SheafOfModules.toSheaf _ ⋙ UX ≅
      eY.inverse ⋙ Mod.forget R ⋙ UY ⋙ setPullback J K U :=
    Functor.isoWhiskerLeft (eY.inverse ⋙ Mod.forget R) (pullbackForgetIso J K U)
  let e₂ : eY.inverse ⋙ Mod.forget R ⋙ UY ≅ F :=
    Functor.isoWhiskerRight eY.counitIso F
  exact Functor.isoWhiskerLeft (I ⋙ SheafOfModules.toSheaf _) euX ≪≫
    e₁ ≪≫ Functor.isoWhiskerRight e₂ (setPullback J K U) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.toSheaf _) euY.symm) (setPullback J K U)

private theorem sectionModulePullbackIso_inv_factor
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
    let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S
    let I := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
    let QY := SheafOfModules.toSheaf ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R))
    let QX := SheafOfModules.toSheaf ((sheafCompose K
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S))
    let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
    let euX := sheafUliftIso K (CategoryTheory.forget Ab.{u + 1})
    ∀ M, (sectionModulePullbackIso J K U R S ρ).inv.app M =
      (setPullback J K U).map ((euY.app (QY.obj M)).hom ≫
        (QY ⋙ UY).map (eY.counitIso.inv.app M)) ≫
      (pullbackForgetIso J K U).inv.app (eY.inverse.obj M).X ≫
      (euX.app (QX.obj (I.obj M))).inv := by
  intro eY eX I QY QX UY euY euX M
  rw [Functor.map_comp]
  dsimp only [sectionModulePullbackIso]
  simp only [Category.assoc]
  rfl

private theorem sectionModulePullbackIso_inv_apply
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
    let QY := SheafOfModules.toSheaf ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R))
    let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
    let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R)))
      (T : Sheaf J (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose J
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (V : Dᵒᵖ) (x : ((setPullback J K U).obj T).obj.obj V),
    (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app V
      (((setPullback J K U).map q).hom.app V x)).down =
      (((setPullback J K U).map (q ≫ (euY.app (QY.obj M)).hom ≫
          (QY ⋙ UY).map (eY.counitIso.inv.app M)) ≫
        (pullbackForgetIso J K U).inv.app (eY.inverse.obj M).X).hom.app V x) := by
  intro eY QY UY euY M T q V x
  rw [sectionModulePullbackIso_inv_factor]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/- Compatibility with the two adjunction units. -/
omit [RepresentablyFlat U] in
private theorem setPullback_unit_hom
    (G : Sheaf J (Type (u + 1))) :
    ((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify K (U.op.leftKanExtension G.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction (Type (u + 1))).comp
      (sheafificationAdjunction K (Type (u + 1))))
    (fullyFaithfulSheafToPresheaf J (Type (u + 1)))
    (Functor.FullyFaithful.id _)
    (L := sheafPullback U (Type (u + 1)) J K)
    (R := U.sheafPushforwardContinuous (Type (u + 1))
      J K)
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h
omit [RepresentablyFlat U] in
private theorem abelianPullback_unit_hom
    (G : Sheaf J Ab.{u + 1}) :
    ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app G).hom =
      U.op.leftKanExtensionUnit G.obj ≫ Functor.whiskerLeft U.op
        (toSheafify K (U.op.leftKanExtension G.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((U.op.lanAdjunction Ab.{u + 1}).comp
      (sheafificationAdjunction K Ab.{u + 1}))
    (fullyFaithfulSheafToPresheaf J Ab.{u + 1})
    (Functor.FullyFaithful.id _)
    (L := sheafPullback U Ab.{u + 1} J K)
    (R := U.sheafPushforwardContinuous Ab.{u + 1}
      J K)
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h

private theorem pullbackForgetIso_unit_hom
    (R : Sheaf J Ab.{u + 1}) :
    ((sheafAdjunctionContinuous U (Type (u + 1)) J K).unit.app
        ((sheafCompose J (CategoryTheory.forget Ab.{u + 1})).obj R)).hom ≫
      Functor.whiskerLeft U.op ((pullbackForgetIso J K U).inv.app R).hom =
    Functor.whiskerRight ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app R).hom
      (CategoryTheory.forget Ab.{u + 1}) := by
  let G := CategoryTheory.forget Ab.{u + 1}
  have (P : Cᵒᵖ ⥤ Ab.{u + 1}) :
      G.PreservesPointwiseLeftKanExtension P U.op := fun W ↦ by
    have : IsFiltered (CostructuredArrow U.op W) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
    have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
      have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
        preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
      have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
      infer_instance
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W
  rw [setPullback_unit_hom]
  dsimp only [pullbackForgetIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, ObjectProperty.FullSubcategory.comp_hom]
  simp only [← Functor.whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  erw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  simp only [Functor.associator]
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  erw [sheafComposeNatTrans_fac]
  erw [abelianPullback_unit_hom J K U R]
  ext W x
  rfl

/- The additive operation graphs follow by transposition through the set adjunction. -/
private theorem pullback_add_graph
    (A : Sheaf J Ab.{u + 1})
    (T : Sheaf J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, t.hom.app W x = (@id (A.obj.obj W) (a.hom.app W x)) +
      (@id (A.obj.obj W) (b.hom.app W x))) :
    (setPullback J K U).map t ≫ (pullbackForgetIso J K U).inv.app A =
      sumSections ((sheafPullback U Ab.{u + 1} J K).obj A)
        ((setPullback J K U).map a ≫ (pullbackForgetIso J K U).inv.app A)
        ((setPullback J K U).map b ≫ (pullbackForgetIso J K U).inv.app A) := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  have he : (adj.homEquiv _ _ ((pullbackForgetIso J K U).inv.app A)).hom =
      Functor.whiskerRight ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom J K U A
  have hq (q : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A) :
      (adj.homEquiv _ _ ((setPullback J K U).map q ≫
        (pullbackForgetIso J K U).inv.app A)).hom =
      q.hom ≫ Functor.whiskerRight
        ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := by
    erw [adj.homEquiv_naturality_left]
    exact congrArg (fun z ↦ q.hom ≫ z) he
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  have ha := ConcreteCategory.congr_hom (NatTrans.congr_app (hq a) W) x
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app (hq b) W) x
  change ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app A).hom.app W
      (t.hom.app W x) = _
  rw [h W x, _root_.map_add]
  change _ = (@id (((sheafPullback U Ab.{u + 1} J K).obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso J K U).inv.app A).hom.app (U.op.obj W)
      (((setPullback J K U).map a).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x)))) +
    (@id (((sheafPullback U Ab.{u + 1} J K).obj A).obj.obj (U.op.obj W))
    (((pullbackForgetIso J K U).inv.app A).hom.app (U.op.obj W)
      (((setPullback J K U).map b).hom.app (U.op.obj W) ((adj.unit.app T).hom.app W x))))
  exact congrArg₂
    (fun (a b : ((sheafPullback U Ab.{u + 1} J K).obj A).obj.obj (U.op.obj W)) ↦ a + b)
    ha.symm hb.symm
private theorem pullback_zero_graph
    (A : Sheaf J Ab.{u + 1})
    (T : Sheaf J (Type (u + 1)))
    (a : T ⟶ (sheafCompose _ (CategoryTheory.forget Ab.{u + 1})).obj A)
    (h : ∀ W x, a.hom.app W x = (0 : A.obj.obj W)) :
    (setPullback J K U).map a ≫ (pullbackForgetIso J K U).inv.app A =
      zeroSections ((setPullback J K U).obj T) ((sheafPullback U Ab.{u + 1} J K).obj A) := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  have he : (adj.homEquiv _ _ ((pullbackForgetIso J K U).inv.app A)).hom =
      Functor.whiskerRight ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app A).hom
        (CategoryTheory.forget Ab.{u + 1}) := pullbackForgetIso_unit_hom J K U A
  apply ObjectProperty.hom_ext _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  ext W x
  change ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app A).hom.app W
      (a.hom.app W x) = (0 : ((sheafPullback U Ab.{u + 1} J K).obj A).obj.obj (U.op.obj W))
  rw [h W x, _root_.map_zero]

omit [RepresentablyFlat U] in
private theorem pushforward_section_mul
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Cᵒᵖ)
    (a b : S.obj.obj (U.op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings J
      ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W)
    @HMul.hMul RY RY RY inferInstance a b =
      @HMul.hMul RX RX RX inferInstance a b := by
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} J K S S W
  refine (section_mul ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S) W a b).trans
    ((Eq.trans ?_ (section_mul S (U.op.obj W) a b).symm))
  have hmul : μ[((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)] =
      Functor.LaxMonoidal.μ (U.sheafPushforwardContinuous Ab.{u + 1} J K) S S ≫
        (U.sheafPushforwardContinuous Ab.{u + 1} J K).map μ[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf J Ab.{u + 1}).map hmul) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ S).obj.obj (U.op.obj W) ↦
    (μ[S]).hom.app (U.op.obj W) x) ht
  exact ht'

omit [RepresentablyFlat U] in
private theorem pushforward_section_one
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Cᵒᵖ) :
    let RY := (InternalAbelianSheafModule.sectionRings J
      ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W)
    @OfNat.ofNat RY 1 inferInstance = @OfNat.ofNat RX 1 inferInstance := by
  have h := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    U Ab.{u + 1} J K W
  refine (section_one ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S) W).trans
    ((Eq.trans ?_ (section_one S (U.op.obj W)).symm))
  have hunit : η[((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)] =
      Functor.LaxMonoidal.ε (U.sheafPushforwardContinuous Ab.{u + 1} J K) ≫
        (U.sheafPushforwardContinuous Ab.{u + 1} J K).map η[S] := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf J Ab.{u + 1}).map hunit) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (ULift.up 1)
  have ht' := congrArg (fun x : (𝟙_ (Sheaf K Ab.{u + 1})).obj.obj
      (U.op.obj W) ↦ (η[S]).hom.app (U.op.obj W) x) ht
  exact ht'
omit [RepresentablyFlat U] in
private theorem pushforward_section_smul
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (M : Mod (Sheaf K Ab.{u + 1}) S)
    (W : Cᵒᵖ)
    (a : S.obj.obj (U.op.obj W))
    (b : M.X.obj.obj (U.op.obj W)) :
    let RY := (InternalAbelianSheafModule.sectionRings J
      ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)).obj W
    let RX := (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      J ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)).obj
        (((U.sheafPushforwardContinuous Ab.{u + 1} J K).mapMod S).obj M)).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      K S).obj M).val.obj
        (U.op.obj W)
    @HSMul.hSMul RY MY MY inferInstance a b =
      @HSMul.hSMul RX MX MX inferInstance a b := by
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    U Ab.{u + 1} J K S M.X W
  refine (section_smul _
      (((U.sheafPushforwardContinuous Ab.{u + 1} J K).mapMod S).obj M) W a b).trans
    ((Eq.trans ?_ (section_smul S M (U.op.obj W) a b).symm))
  have hact : Mod.act ((((U.sheafPushforwardContinuous Ab.{u + 1} J K).mapMod S).obj M).X) =
      Functor.LaxMonoidal.μ (U.sheafPushforwardContinuous Ab.{u + 1} J K) S M.X ≫
        (U.sheafPushforwardContinuous Ab.{u + 1} J K).map (Mod.act M.X) := rfl
  have hc := NatTrans.congr_app
    (congrArg (sheafToPresheaf J Ab.{u + 1}).map hact) W
  refine (ConcreteCategory.congr_hom hc _).trans ?_
  have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
  have ht' := congrArg (fun x : (S ⊗ M.X).obj.obj (U.op.obj W) ↦
    (Mod.act M.X).hom.app (U.op.obj W) x) ht
  exact ht'
private noncomputable def pushforwardSectionRingHom
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (W : Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings J
      ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj S)).obj W →+*
    (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W) where
  toFun := fun a ↦ a
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := pushforward_section_one J K U S W
  map_mul' a b := pushforward_section_mul J K U S W a b

private noncomputable def inverseImageSectionRingUnit
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRings J R).obj W →+*
    (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W) :=
by
  haveI : IsMonHom ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app R) :=
    (sheafAdjunctionContinuous U Ab.{u + 1} J K).isMonHom_unitAlgHom R
  haveI : IsMonHom (asIso ρ).inv := inferInstance
  haveI : IsMonHom ((U.sheafPushforwardContinuous Ab.{u + 1} J K).map (asIso ρ).inv) :=
    Functor.map.instIsMonHom (F := (U.sheafPushforwardContinuous Ab.{u + 1} J K)) _ _ (asIso ρ).inv
  exact (pushforwardSectionRingHom J K U S W).comp
    (sectionRingMap ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app R ≫
      (U.sheafPushforwardContinuous Ab.{u + 1} J K).map (asIso ρ).inv) W)

private theorem inverseImageSectionModuleUnit_smul
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (N : Mod (Sheaf J Ab.{u + 1}) R)
    (W : Cᵒᵖ) (a : R.obj.obj W) (b : N.X.obj.obj W) :
    let RY := (InternalAbelianSheafModule.sectionRings J R).obj W
    let SX := (InternalAbelianSheafModule.sectionRings K S).obj
      (U.op.obj W)
    let MY := ((InternalAbelianSheafModule.sectionModuleFunctor
      J R).obj N).val.obj W
    let MX := ((InternalAbelianSheafModule.sectionModuleFunctor
      K S).obj ((Mod.mapModComap ρ).obj N)).val.obj (U.op.obj W)
    ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app N.X).hom.app W
      (@HSMul.hSMul RY MY MY inferInstance a b) =
      @HSMul.hSMul SX MX MX inferInstance (inverseImageSectionRingUnit J K U R S ρ W a)
        (((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app N.X).hom.app W b) := by
  let adj := sheafAdjunctionContinuous U Ab.{u + 1} J K
  let P := ((sheafPullback U Ab.{u + 1} J K).mapMod R).obj N
  let Z := ((U.sheafPushforwardContinuous Ab.{u + 1} J K).mapMod
    ((sheafPullback U Ab.{u + 1} J K).obj R)).obj P
  let j := (adj.mapModAdjunction R).unit.app N
  let H := InternalAbelianSheafModule.sectionModuleFunctor J R
  have hj := (((H.map j).val.app W).hom).map_smul
    (show (InternalAbelianSheafModule.sectionRings J R).obj W from a)
    (show (H.obj N).val.obj W from b)
  have hc := section_comap_smul R ((U.sheafPushforwardContinuous Ab.{u + 1} J K).obj
      ((sheafPullback U Ab.{u + 1} J K).obj R)) (adj.unitAlgHom R) Z W a
      (j.hom.hom.app W b)
  have hp := pushforward_section_smul J K U ((sheafPullback U Ab.{u + 1} J K).obj R) P W
    ((adj.unit.app R).hom.app W a) (j.hom.hom.app W b)
  have hd := section_comap_smul S ((sheafPullback U Ab.{u + 1} J K).obj R) ρ P (U.op.obj W)
    (inverseImageSectionRingUnit J K U R S ρ W a) (j.hom.hom.app W b)
  have hr : ρ.hom.app (U.op.obj W) (inverseImageSectionRingUnit J K U R S ρ W a) =
      (adj.unit.app R).hom.app W a := by
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun z ↦ z.hom) (asIso ρ).inv_hom_id) (U.op.obj W))
        ((adj.unit.app R).hom.app W a)
    exact he
  rw [hr] at hd
  have hu : j.hom = adj.unit.app N.X := adj.mapModAdjunction_unit_app_hom R N
  have he := hj.trans (hc.trans (hp.trans hd.symm))
  change j.hom.hom.app W _ = _ at he
  rw [hu] at he
  exact he

private theorem sectionRingPullbackIso_unit
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (W : Cᵒᵖ) (r : ULift.{u + 1} (R.obj.obj W)) :
    let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      ((adj.unit.app ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            J R))).hom.app W r)).down =
        inverseImageSectionRingUnit J K U R S ρ W r.down := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf J
      (Type (u + 1))).map (adj.unit.naturality (sectionRingUnderlyingIso R).hom)) W) r
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom J K U R) W) r.down
  have hn' := congrArg (fun x ↦ ((pullbackForgetIso J K U).inv.app R).hom.app
    (U.op.obj W) x) hn
  exact congrArg (fun x ↦ ((asIso ρ).inv.hom.app (U.op.obj W)) x) (hn'.symm.trans hu)

/- Ring operation graphs, proved by transposition through the set adjunction. -/
private theorem sectionModulePullbackIso_transpose
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
    let QY := SheafOfModules.toSheaf ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R))
    ∀ (M : SheafOfModules.{u + 1} ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R)))
      (T : Sheaf J (Type (u + 1)))
      (q : T ⟶ (QY ⋙ sheafCompose J
        (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M)
      (W : Cᵒᵖ) (x : T.obj.obj W),
    let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
    (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app (U.op.obj W)
      (((setPullback J K U).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app (eY.inverse.obj M).X).hom.app W
        (((eY.counitIso.inv.app M).val.app W).hom (q.hom.app W x).down) := by
  intro eY QY M T q W x adj
  let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
  let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
  let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
  let N := eY.inverse.obj M
  have ht :
      (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app (U.op.obj W)
        (((setPullback J K U).map q).hom.app (U.op.obj W)
          ((adj.unit.app T).hom.app W x))).down =
      (((setPullback J K U).map (q ≫ k) ≫
        (pullbackForgetIso J K U).inv.app N.X).hom.app (U.op.obj W)
          ((adj.unit.app T).hom.app W x)) := by
    exact sectionModulePullbackIso_inv_apply J K U R S ρ M T q (U.op.obj W)
      ((adj.unit.app T).hom.app W x)
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf J
      (Type (u + 1))).map (adj.unit.naturality (q ≫ k))) W) x
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullbackForgetIso_unit_hom J K U N.X) W) ((q ≫ k).hom.app W x)
  have hn' := congrArg (fun z ↦ ((pullbackForgetIso J K U).inv.app N.X).hom.app
    (U.op.obj W) z) hn
  exact ht.trans (hn'.symm.trans hu)

private theorem sectionRingPullbackIso_transpose
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf J (Type (u + 1)))
    (q : T ⟶ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R)) (W : Cᵒᵖ) (x : T.obj.obj W) :
    let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map q).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      inverseImageSectionRingUnit J K U R S ρ W (q.hom.app W x).down := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (sheafToPresheaf J
      (Type (u + 1))).map (adj.unit.naturality q)) W) x
  have hn' := congrArg (fun z ↦
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W) z).down) hn
  exact hn'.symm.trans (sectionRingPullbackIso_unit J K U R S ρ W (q.hom.app W x))
private theorem sectionRingPullback_mul_graph
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        J R).obj W)
        (a.hom.app W x).down) *
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        J R).obj W)
        (b.hom.app W x).down)) :
    (setPullback J K U).map t ≫ (sectionRingPullbackIso J K U R S ρ).hom =
      ringMulSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S)
        ((setPullback J K U).obj T)
        ((setPullback J K U).map a ≫ (sectionRingPullbackIso J K U R S ρ).hom)
        ((setPullback J K U).map b ≫ (sectionRingPullbackIso J K U R S ρ).hom) := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      K S).obj (U.op.obj W))
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) *
    (@id ((InternalAbelianSheafModule.sectionRings
      K S).obj (U.op.obj W))
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit J K U R S ρ W) (h W x)).trans
    (_root_.map_mul (inverseImageSectionRingUnit J K U R S ρ W) _ _)
private theorem sectionRingPullback_add_graph
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf J (Type (u + 1)))
    (a b t : T ⟶ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R))
    (h : ∀ W x, (t.hom.app W x).down =
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        J R).obj W)
        (a.hom.app W x).down) +
      (@id ((InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        J R).obj W)
        (b.hom.app W x).down)) :
    (setPullback J K U).map t ≫ (sectionRingPullbackIso J K U R S ρ).hom =
      ringAddSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S)
        ((setPullback J K U).obj T)
        ((setPullback J K U).map a ≫ (sectionRingPullbackIso J K U R S ρ).hom)
        ((setPullback J K U).map b ≫ (sectionRingPullbackIso J K U R S ρ).hom) := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map t).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down = _
  erw [sectionRingPullbackIso_transpose]
  change _ = (@id ((InternalAbelianSheafModule.sectionRings
      K S).obj (U.op.obj W))
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down) +
    (@id ((InternalAbelianSheafModule.sectionRings
      K S).obj (U.op.obj W))
    ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map b).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down)
  erw [sectionRingPullbackIso_transpose, sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit J K U R S ρ W) (h W x)).trans
    (_root_.map_add (inverseImageSectionRingUnit J K U R S ρ W) _ _)
private theorem sectionRingPullback_nat_graph
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ]
    (T : Sheaf J (Type (u + 1))) (n : ℕ)
    (a : T ⟶ (sheafCompose J
      (CategoryTheory.forget CommRingCat.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R))
    (h : ∀ W x, (a.hom.app W x).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        J R).obj W)) :
    (setPullback J K U).map a ≫ (sectionRingPullbackIso J K U R S ρ).hom =
      ringNatSections (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S) ((setPullback J K U).obj T) n := by
  let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
  apply (adj.homEquiv _ _).injective
  apply ObjectProperty.hom_ext _
  ext W x
  apply ULift.ext
  change ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
      (((setPullback J K U).map a).hom.app (U.op.obj W)
        ((adj.unit.app T).hom.app W x))).down =
      (n : (InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u}
        K S).obj (U.op.obj W))
  erw [sectionRingPullbackIso_transpose]
  exact (congrArg (inverseImageSectionRingUnit J K U R S ρ W) (h W x)).trans
    (_root_.map_natCast (inverseImageSectionRingUnit J K U R S ρ W) n)

end Comparison

/-- Let `U : C ⥤ D` be a continuous representably flat functor of sites and
`ρ : S ⟶ U^* R` an isomorphism of commutative ring objects in abelian sheaves. The internal
inverse image `Mod.mapModComap ρ`, transported through the section-module equivalences, is the
module part of an algebraic inverse image along the set-valued sheaf pullback `U^*`.

Source: Stacks Project, Tags 00YV and 03D2.
(auxiliary; not a blueprint node)

Proof. Both the set-valued and the abelian sheaf pullbacks are left Kan extension along `U.op`
followed by sheafification. The comma categories `CostructuredArrow U.op W` are filtered since
`U` is representably flat, so the forgetful functor of abelian groups commutes with the Kan
extension and with sheafification. Composing with the inverse of `ρ` and the equal-universe
`ULift` isomorphisms gives the ring comparison; the section-equivalence counit gives the module
comparison. Each operation graph equation is checked after transposing through the set-valued
adjunction `U^* ⊣ U_*`: the transposed maps are the source maps followed by the abelian
adjunction unit and the inverse coefficient isomorphism. The additive unit preserves addition
and zero, its monoid-homomorphism property (from the monoidal adjunction) preserves
multiplication and one, and the lifted module-adjunction unit preserves scalar multiplication.
Choose the constructed module functor itself, with the identity comparison isomorphism. -/
theorem exists_sectionModuleAlgebraicInverseImage
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    ∃ I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u, u + 1, u + 1}
        (sheafPullback U (Type (u + 1)) J K)
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} K S),
      Nonempty
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).inverse ⋙
          Mod.mapModComap ρ ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S).functor ≅
            I.modules) := by
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S
  let I : SheafOfModules.AlgebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
      u + 1, u + 1} (setPullback J K U)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        J R)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S) := by
    refine
      { ringUnderlying := sectionRingPullbackIso J K U R S ρ
        ringAdd := ?_
        ringMul := ?_
        ringZero := ?_
        ringOne := ?_
        modules := eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor
        moduleUnderlying := sectionModulePullbackIso J K U R S ρ
        moduleAdd := ?_
        moduleZero := ?_
        moduleSMul := ?_ }
    · intro T a b t h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_add_graph J K U R S ρ T a b t h))
    · intro T a b t h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_mul_graph J K U R S ρ T a b t h))
    · intro T a h V x
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x)
        (sectionRingPullback_nat_graph J K U R S ρ T 0 a h))
    · intro T a h V x
      have he := sectionRingPullback_nat_graph J K U R S ρ T 1 a (fun W y ↦ by
        rw [Nat.cast_one]
        exact h W y)
      simpa [ringNatSections] using
        congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x) he)
    · intro M T a b t h V x
      let QY := SheafOfModules.toSheaf ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R))
      let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
      let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
      let N := eY.inverse.obj M
      have ht (q : T ⟶ (QY ⋙ sheafCompose J
          (CategoryTheory.forget Ab.{u + 1} ⋙ uliftFunctor.{u + 1, u + 1})).obj M) :
          (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app V
            (((setPullback J K U).map q).hom.app V x)).down =
          (((setPullback J K U).map (q ≫ k) ≫
            (pullbackForgetIso J K U).inv.app N.X).hom.app V x) := by
        exact sectionModulePullbackIso_inv_apply J K U R S ρ M T _ V x
      have h' : ∀ W y, (t ≫ k).hom.app W y =
          (@id (N.X.obj.obj W) ((a ≫ k).hom.app W y)) +
          (@id (N.X.obj.obj W) ((b ≫ k).hom.app W y)) := by
        intro W y
        change ((eY.counitIso.inv.app M).val.app W).hom (t.hom.app W y).down =
          ((eY.counitIso.inv.app M).val.app W).hom (a.hom.app W y).down +
          ((eY.counitIso.inv.app M).val.app W).hom (b.hom.app W y).down
        have hh := h W y
        dsimp only [id] at hh
        exact (congrArg ((eY.counitIso.inv.app M).val.app W).hom hh).trans
          (_root_.map_add ((eY.counitIso.inv.app M).val.app W).hom _ _)
      have hp := pullback_add_graph J K U N.X T (a ≫ k) (b ≫ k) (t ≫ k) h'
      rw [ht t, ht a, ht b]
      exact congrArg (fun q ↦ q.hom.app V x) hp
    · intro M T a h V x
      let QY := SheafOfModules.toSheaf ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          J R))
      let UY := sheafCompose J (CategoryTheory.forget Ab.{u + 1})
      let euY := sheafUliftIso J (CategoryTheory.forget Ab.{u + 1})
      let k := (euY.app (QY.obj M)).hom ≫ (QY ⋙ UY).map (eY.counitIso.inv.app M)
      let N := eY.inverse.obj M
      have ht :
          (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app V
            (((setPullback J K U).map a).hom.app V x)).down =
          (((setPullback J K U).map (a ≫ k) ≫
            (pullbackForgetIso J K U).inv.app N.X).hom.app V x) := by
        exact sectionModulePullbackIso_inv_apply J K U R S ρ M T _ V x
      have h' : ∀ W y, (a ≫ k).hom.app W y = (0 : N.X.obj.obj W) := by
        intro W y
        change ((eY.counitIso.inv.app M).val.app W).hom (a.hom.app W y).down = 0
        have hh := h W y
        dsimp only [id] at hh
        exact (congrArg ((eY.counitIso.inv.app M).val.app W).hom hh).trans
          (_root_.map_zero ((eY.counitIso.inv.app M).val.app W).hom)
      exact ht.trans (congrArg (fun q ↦ q.hom.app V x)
        (pullback_zero_graph J K U N.X T (a ≫ k) h'))
    · intro M T a b t h V x
      let adj := sheafAdjunctionContinuous U (Type (u + 1)) J K
      let MX := (eY.inverse ⋙ Mod.mapModComap ρ ⋙ eX.functor).obj M
      let RX := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        K S
      let sa := (setPullback J K U).map a ≫ (sectionRingPullbackIso J K U R S ρ).hom
      let sb := (setPullback J K U).map b ≫ (sectionModulePullbackIso J K U R S ρ).inv.app M
      let st := (setPullback J K U).map t ≫ (sectionModulePullbackIso J K U R S ρ).inv.app M
      have hp : st = moduleSMulSections RX MX ((setPullback J K U).obj T) sa sb := by
        apply (adj.homEquiv _ _).injective
        apply ObjectProperty.hom_ext _
        ext W y
        apply ULift.ext
        change (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app (U.op.obj W)
          (((setPullback J K U).map t).hom.app (U.op.obj W)
            ((adj.unit.app T).hom.app W y))).down = _
        have ht := sectionModulePullbackIso_transpose J K U R S ρ M T t W y
        change _ = (@id ((InternalAbelianSheafModule.sectionRings
          K S).obj (U.op.obj W))
          ((sectionRingPullbackIso J K U R S ρ).hom.hom.app (U.op.obj W)
            (((setPullback J K U).map a).hom.app (U.op.obj W)
              ((adj.unit.app T).hom.app W y))).down) •
          (@id (MX.val.obj (U.op.obj W))
          (((sectionModulePullbackIso J K U R S ρ).inv.app M).hom.app (U.op.obj W)
            (((setPullback J K U).map b).hom.app (U.op.obj W)
              ((adj.unit.app T).hom.app W y))).down)
        have ha := sectionRingPullbackIso_transpose J K U R S ρ T a W y
        have hb := sectionModulePullbackIso_transpose J K U R S ρ M T b W y
        have hh := h W y
        dsimp only [id] at hh
        have hc := congrArg ((eY.counitIso.inv.app M).val.app W).hom hh
        have hc' := sectionModuleCounit_smul R M W
          (a.hom.app W y).down (b.hom.app W y).down
        have he := (congrArg (fun z ↦
          ((sheafAdjunctionContinuous U Ab.{u + 1} J K).unit.app (eY.inverse.obj M).X).hom.app W z)
          (hc.trans hc')).trans
          (inverseImageSectionModuleUnit_smul J K U R S ρ (eY.inverse.obj M) W
            (a.hom.app W y).down
            (((eY.counitIso.inv.app M).val.app W).hom (b.hom.app W y).down))
        exact ht.trans (he.trans (congrArg₂
          (fun (r : (InternalAbelianSheafModule.sectionRings
            K S).obj (U.op.obj W))
            (m : MX.val.obj (U.op.obj W)) ↦ r • m) ha.symm hb.symm))
      exact congrArg ULift.down (congrArg (fun q ↦ q.hom.app V x) hp)
  exact ⟨I, ⟨Iso.refl _⟩⟩

/-- Let `U : C ⥤ D` be a continuous representably flat functor of sites and
`ρ : S ⟶ U^* R` an isomorphism of commutative ring objects in abelian sheaves. Then the
internal inverse image `Mod.mapModComap ρ` preserves flat module objects.

Source: Stacks Project, Tag 05VD, lemma-pullback-flat.
(auxiliary; not a blueprint node)

Proof. The explicit balanced tensor comparison transports internal flatness to site-flatness
of section modules. The set-valued sheaf pullback `U^*` is left Kan extension along `U.op`
followed by sheafification, with right adjoint `U_*`. The comma categories are filtered since
`U` is representably flat, and filtered colimits of types commute with finite limits, so `U^*`
is left exact. By `exists_sectionModuleAlgebraicInverseImage` its module inverse image is the
internal inverse image, so the universe-polymorphic algebraic inverse-image flatness theorem
applies. Transfer the result through the source equivalence unit and the comparison
isomorphism, using that the local equational criterion is invariant under isomorphism, and use
the reverse tensor comparison to recover internal flatness. -/
theorem preservesFlat_mapModComap
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (S : Sheaf K Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ (sheafPullback U Ab.{u + 1} J K).obj R) [IsMonHom ρ] [IsIso ρ] :
    (Mod.mapModComap ρ).PreservesFlat := by
  let L := sheafPullback U (Type (u + 1)) J K
  let V := U.sheafPushforwardContinuous (Type (u + 1)) J K
  let adj : L ⊣ V := sheafAdjunctionContinuous U (Type (u + 1)) J K
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    ⟨fun J _ _ ↦ ⟨inferInstance⟩⟩
  have : PreservesFiniteLimits
      (U.op.lan : (Cᵒᵖ ⥤ Type (u + 1)) ⥤ Dᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.preservesFiniteLimits_op_lan_of_flat U
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  obtain ⟨I, ⟨ei⟩⟩ := exists_sectionModuleAlgebraicInverseImage J K U R S ρ
  let eY := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let eX := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} K S
  refine ⟨fun {M} hM ↦ ?_⟩
  have hsec := (InternalAbelianSheafModule.flat_iff_sectionModule J R M).mp hM
  have hi := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
    u + 1, u + 1} L V adj I (eY.functor.obj M) hsec
  let e : eX.functor.obj ((Mod.mapModComap ρ).obj M) ≅ I.modules.obj (eY.functor.obj M) :=
    (Mod.mapModComap ρ ⋙ eX.functor).mapIso (eY.unitIso.app M) ≪≫ ei.app (eY.functor.obj M)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule K S _).mpr
    (isFlatOnSite_of_iso (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} K S) e hi)

end CategoryTheory.Functor.sheafPullbackConstruction
