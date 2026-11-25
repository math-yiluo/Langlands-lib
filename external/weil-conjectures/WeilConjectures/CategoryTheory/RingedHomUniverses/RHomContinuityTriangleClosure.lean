/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Triangle closure of bounded-target internal-Hom continuity

Source: Stacks Project, Cohomology on Sites, Tag 08JC, and the formal bounded-target
closure argument extracted from Bhatt--Scholze, Lemmas 6.3.14 and 6.8.12
(blueprint: lem-sfb-rhom-continuity-triangle-closure).

The predicate below is the P introduced in the statement. Its comparison is the image
under Q of the actual complex-level colimit.post for the existing functor homFixed.
Thus no colimit in the unbounded derived category is used. Every complex representative
of the source is allowed, and the target bound is cohomological, not termwise.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated
open scoped ZeroObject

private theorem colimitPost_natTrans
    {A B : Type*} [Category A] [Category B]
    (I : Type*) [Category I] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (F G : A ⥤ B) (η : F ⟶ G) (M : I ⥤ A) :
    colim.map (Functor.whiskerLeft M η) ≫ colimit.post M G =
      colimit.post M F ≫ η.app (colimit M) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_map_assoc]
  simp only [Functor.whiskerLeft_app, colimit.ι_post, colimit.ι_post_assoc]
  exact (η.naturality (colimit.ι M i)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem shortComplexHomologyPreserves
    {A : Type*} [Category A] [Abelian A]
    (I : Type*) [Category I] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor A) := by
  classical
  refine ⟨fun {F} ↦ ?_⟩
  have : (colim (J := I) (C := A)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let K := (ShortComplex.functorEquivalence I A).inverse.obj F
  let e : K.homology ≅ F ⋙ ShortComplex.homologyFunctor A :=
    NatIso.ofComponents
      (fun i ↦ (K.mapHomologyIso ((evaluation I A).obj i)).symm)
      (by
        intro i j f
        have h := K.homologyMap_mapNatTrans ((evaluation I A).map f)
        change ShortComplex.homologyMap (F.map f) = _ at h
        change K.homology.map f ≫
            (K.mapHomologyIso ((evaluation I A).obj j)).inv =
          (K.mapHomologyIso ((evaluation I A).obj i)).inv ≫
            ShortComplex.homologyMap (F.map f)
        rw [h]
        simp)
  let a : colimit (F ⋙ ShortComplex.homologyFunctor A) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
    (colim.mapIso e).symm ≪≫ (K.mapHomologyIso colim).symm
  refine preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F) ?_
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
  refine Cocone.ext a ?_
  intro i
  have h := K.homologyMap_mapNatTrans (colim.ι (C := A) i)
  change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
  change colimit.ι _ i ≫ a.hom =
    ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
  rw [h]
  simp [a, e]

private theorem complexHomologyPreserves
    {A : Type*} [Category A] [Abelian A]
    (I : Type*) [Category I] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (n : ℤ) :
    PreservesColimitsOfShape I (HomologicalComplex.homologyFunctor A (.up ℤ) n) := by
  have := shortComplexHomologyPreserves (A := A) I
  have : PreservesColimitsOfShape I
      (HomologicalComplex.shortComplexFunctor A (.up ℤ) n) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso A (.up ℤ) n).symm

private theorem colimit_pair_exact
    {B A : Type*} [Category B] [Category A] [Abelian A]
    {I : Type*} [Category I] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (F G H : B ⥤ A) (α : F ⟶ G) (β : G ⟶ H) (M : I ⥤ B)
    (h : ∀ X, (ComposableArrows.mk₂ (α.app X) (β.app X)).Exact) :
    (ComposableArrows.mk₂ (colim.map (Functor.whiskerLeft M α))
      (colim.map (Functor.whiskerLeft M β))).Exact := by
  have hz : Functor.whiskerLeft M α ≫ Functor.whiskerLeft M β = 0 := by
    apply NatTrans.ext
    funext i
    exact (h (M.obj i)).toIsComplex.zero 0
  let S : ShortComplex (I ⥤ A) :=
    ShortComplex.mk (Functor.whiskerLeft M α) (Functor.whiskerLeft M β) hz
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro i
    have hi : (S.map ((evaluation I A).obj i)).Exact := (h (M.obj i)).exact 0
    exact ((ShortComplex.exact_iff_isZero_homology _).mp hi).of_iso
      (S.mapHomologyIso ((evaluation I A).obj i)).symm
  exact (hS.map colim).exact_toComposableArrows

private theorem post_fiveLemma
    {B A : Type*} [Category B] [Category A] [Abelian A]
    {I : Type*} [Category I] [HasColimitsOfShape I B]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (F₀ F₁ F₂ F₃ F₄ : B ⥤ A)
    (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) (γ : F₂ ⟶ F₃) (δ : F₃ ⟶ F₄)
    (h₀ : ∀ X, (ComposableArrows.mk₂ (α.app X) (β.app X)).Exact)
    (h₁ : ∀ X, (ComposableArrows.mk₂ (β.app X) (γ.app X)).Exact)
    (h₂ : ∀ X, (ComposableArrows.mk₂ (γ.app X) (δ.app X)).Exact)
    (M : I ⥤ B)
    [IsIso (colimit.post M F₀)] [IsIso (colimit.post M F₁)]
    [IsIso (colimit.post M F₃)] [IsIso (colimit.post M F₄)] :
    IsIso (colimit.post M F₂) := by
  let R₁ := ComposableArrows.mk₄
    (colim.map (Functor.whiskerLeft M α)) (colim.map (Functor.whiskerLeft M β))
    (colim.map (Functor.whiskerLeft M γ)) (colim.map (Functor.whiskerLeft M δ))
  let R₂ := ComposableArrows.mk₄ (α.app (colimit M)) (β.app (colimit M))
    (γ.app (colimit M)) (δ.app (colimit M))
  let φ : R₁ ⟶ R₂ := ComposableArrows.homMk₄
    (colimit.post M F₀) (colimit.post M F₁) (colimit.post M F₂)
    (colimit.post M F₃) (colimit.post M F₄)
    (colimitPost_natTrans I F₀ F₁ α M) (colimitPost_natTrans I F₁ F₂ β M)
    (colimitPost_natTrans I F₂ F₃ γ M) (colimitPost_natTrans I F₃ F₄ δ M)
  have htop : R₁.Exact := ComposableArrows.exact_of_δ₀
    (colimit_pair_exact F₀ F₁ F₂ α β M h₀)
    (ComposableArrows.exact_of_δ₀ (colimit_pair_exact F₁ F₂ F₃ β γ M h₁)
      (colimit_pair_exact F₂ F₃ F₄ γ δ M h₂))
  have hbottom : R₂.Exact := ComposableArrows.exact_of_δ₀ (h₀ (colimit M))
    (ComposableArrows.exact_of_δ₀ (h₁ (colimit M)) (h₂ (colimit M)))
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono htop hbottom φ
    (by change Epi (colimit.post M F₀); infer_instance)
    (by change IsIso (colimit.post M F₁); infer_instance)
    (by change IsIso (colimit.post M F₃); infer_instance)
    (by change Mono (colimit.post M F₄); infer_instance)

private theorem isZero_Q_colimit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type*} [Category I] [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (M : I ⥤ CochainComplex A ℤ)
    (hM : ∀ i, IsZero (DerivedCategory.Q.obj (M.obj i))) :
    IsZero (DerivedCategory.Q.obj (colimit M)) := by
  let Z : I ⥤ CochainComplex A ℤ := (Functor.const I).obj 0
  let η : M ⟶ Z := 0
  have hZ : IsZero (DerivedCategory.Q.obj (0 : CochainComplex A ℤ)) :=
    DerivedCategory.Q.map_isZero (isZero_zero _)
  have hη : QuasiIso (colimMap η) :=
    (HomologicalComplex.quasiIso A (.up ℤ)).colimMap η (fun i ↦ by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
      exact (hM i).isIso hZ _)
  have hz : IsZero Z := (Functor.isZero_iff _).2 (fun _ ↦ isZero_zero _)
  have hc : IsZero (colimit Z) := (colim (J := I)).map_isZero hz
  exact (DerivedCategory.Q.map_isZero hc).of_iso
    (asIso (DerivedCategory.Q.map (colimMap η)))

private theorem post_quasiIso_shift
    {A B : Type*} [Category A] [Category B] [Abelian B]
    {I : Type*} [Category I] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (F : A ⥤ CochainComplex B ℤ) (M : I ⥤ A) (n : ℤ)
    (hF : QuasiIso (colimit.post M F)) :
    QuasiIso (colimit.post M (F ⋙ shiftFunctor _ n)) := by
  have : QuasiIso (colimit.post M F) := hF
  rw [← colimit.post_post]
  infer_instance

private theorem post_quasiIso_fiveLemma
    {B A : Type*} [Category B] [Category A] [Abelian A]
    {I : Type*} [Category I] [HasColimitsOfShape I B]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (F₀ F₁ F₂ F₃ F₄ : B ⥤ CochainComplex A ℤ)
    (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) (γ : F₂ ⟶ F₃) (δ : F₃ ⟶ F₄)
    (h₀ : ∀ (X : B) (q : ℤ),
      (ComposableArrows.mk₂ (HomologicalComplex.homologyMap (α.app X) q)
        (HomologicalComplex.homologyMap (β.app X) q)).Exact)
    (h₁ : ∀ (X : B) (q : ℤ),
      (ComposableArrows.mk₂ (HomologicalComplex.homologyMap (β.app X) q)
        (HomologicalComplex.homologyMap (γ.app X) q)).Exact)
    (h₂ : ∀ (X : B) (q : ℤ),
      (ComposableArrows.mk₂ (HomologicalComplex.homologyMap (γ.app X) q)
        (HomologicalComplex.homologyMap (δ.app X) q)).Exact)
    (M : I ⥤ B)
    (hF₀ : QuasiIso (colimit.post M F₀)) (hF₁ : QuasiIso (colimit.post M F₁))
    (hF₃ : QuasiIso (colimit.post M F₃)) (hF₄ : QuasiIso (colimit.post M F₄)) :
    QuasiIso (colimit.post M F₂) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor A (.up ℤ) q
  have : PreservesColimitsOfShape I H := complexHomologyPreserves I q
  have hp (F : B ⥤ CochainComplex A ℤ) (hF : QuasiIso (colimit.post M F)) :
      IsIso (colimit.post M (F ⋙ H)) := by
    have hmap : IsIso (H.map (colimit.post M F)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ q).mp (hF.quasiIsoAt q)
    rw [← colimit.post_post]
    infer_instance
  have := hp F₀ hF₀
  have := hp F₁ hF₁
  have := hp F₃ hF₃
  have := hp F₄ hF₄
  have hmid := post_fiveLemma (F₀ ⋙ H) (F₁ ⋙ H) (F₂ ⋙ H) (F₃ ⋙ H) (F₄ ⋙ H)
    (Functor.whiskerRight α H) (Functor.whiskerRight β H)
    (Functor.whiskerRight γ H) (Functor.whiskerRight δ H)
    (fun X ↦ h₀ X q) (fun X ↦ h₁ X q) (fun X ↦ h₂ X q) M
  rw [← colimit.post_post] at hmid
  exact (isIso_comp_left_iff (colimit.post (M ⋙ F₂) H)
    (H.map (colimit.post M F₂))).mp hmid

private theorem post_isIso_natIso
    {A B : Type*} [Category A] [Category B]
    {I : Type*} [Category I] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    (F G : A ⥤ B) (e : F ≅ G) (M : I ⥤ A)
    [IsIso (colimit.post M F)] : IsIso (colimit.post M G) := by
  have : IsIso (colim.map (Functor.whiskerLeft M e.hom)) := by
    change IsIso ((colim.mapIso (Functor.isoWhiskerLeft M e)).hom)
    infer_instance
  have h : IsIso (colim.map (Functor.whiskerLeft M e.hom) ≫ colimit.post M G) := by
    rw [colimitPost_natTrans I F G e.hom M]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

private theorem post_quasiIso_derivedIso
    {A B : Type*} [Category A] [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    {I : Type*} [Category I] [HasColimitsOfShape I A]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (F G : A ⥤ CochainComplex B ℤ)
    (e : F ⋙ DerivedCategory.Q ≅ G ⋙ DerivedCategory.Q) (M : I ⥤ A)
    (hF : QuasiIso (colimit.post M F)) : QuasiIso (colimit.post M G) := by
  have : QuasiIso (colimit.post M F) := hF
  rw [quasiIso_iff]
  intro q
  have := complexHomologyPreserves (A := B) I q
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) q
  let HD := DerivedCategory.homologyFunctor B q
  let fac := DerivedCategory.homologyFunctorFactors B q
  let a : F ⋙ H ≅ G ⋙ H :=
    (Functor.isoWhiskerLeft F fac).symm ≪≫ Functor.isoWhiskerRight e HD ≪≫
      Functor.isoWhiskerLeft G fac
  have hpostF : IsIso (colimit.post M (F ⋙ H)) := by
    have : IsIso (H.map (colimit.post M F)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ q).mp (hF.quasiIsoAt q)
    rw [← colimit.post_post]
    infer_instance
  have : IsIso (colimit.post M (G ⋙ H)) := post_isIso_natIso _ _ a M
  have hpostG : IsIso (H.map (colimit.post M G)) := by
    rw [← colimit.post_post] at this
    exact (isIso_comp_left_iff _ _).mp this
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr hpostG

private theorem triangle_model_with_middle
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Pretriangulated.Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A))
    (L : CochainComplex A ℤ) (eL : DerivedCategory.Q.obj L ≅ T.obj₂) :
    ∃ (K : CochainComplex A ℤ) (f : K ⟶ L),
      Nonempty (DerivedCategory.Q.obj K ≅ T.obj₁) ∧
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone f) ≅ T.obj₃) := by
  classical
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let X := Q.objPreimage T.obj₁
  let eX : Q.obj X ≅ T.obj₁ := Q.objObjPreimageIso T.obj₁
  obtain ⟨K, s, hs, f, hf⟩ := DerivedCategory.right_fac
    (eX.hom ≫ T.mor₁ ≫ eL.inv)
  let := hs
  let eK : Q.obj K ≅ T.obj₁ := asIso (Q.map s) ≪≫ eX
  have comm : Q.map f ≫ eL.hom = eK.hom ≫ T.mor₁ := by
    calc
      Q.map f ≫ eL.hom = Q.map s ≫ (inv (Q.map s) ≫ Q.map f) ≫ eL.hom := by
        simp
      _ = Q.map s ≫ (eX.hom ≫ T.mor₁ ≫ eL.inv) ≫ eL.hom := by rw [← hf]
      _ = eK.hom ≫ T.mor₁ := by simp [eK, Category.assoc]
  let eT := Pretriangulated.isoTriangleOfIso₁₂ _ _
    (DerivedCategory.mappingCone_triangle_distinguished f) hT eK eL comm
  exact ⟨K, f, ⟨eK⟩, ⟨(Pretriangulated.Triangle.π₃.mapIso eT)⟩⟩

namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- The property P of the node: continuity for all uniformly cohomologically bounded-below
filtered complex diagrams, and a uniform lower-bound offset for the target variable.
Source: Stacks 08JC and the bounded-target closure extraction in the node
(blueprint: lem-sfb-rhom-continuity-triangle-closure).

The canonical map is Q(colimit.post M (homFixed L)); its coprojection at i is the
localized Hom map of the target coprojection. Exact termwise sheaf colimits compute
its source. Quantification over source representatives avoids a choice of an object
or a noncanonical comparison. The colimit structures quantified here exist for small
module-sheaf diagrams and are only the structures needed to form the displayed map. -/
def BoundedTargetHomContinuous (A : D.{c, v, r, w} J R) : Prop :=
  (∀ (L : Complex.{c, v, r} J R), Nonempty (DerivedCategory.Q.obj L ≅ A) →
    ∀ (I : Type (max c v r)) [SmallCategory I] [IsFiltered I]
      [HasColimitsOfShape I (Modules.{c, v, r} J R)]
      (M : I ⥤ Complex.{c, v, r} J R) (b : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (M.obj i)).IsGE b) →
        IsIso (DerivedCategory.Q.map (colimit.post M
          (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)))) ∧
  ∃ d : ℤ, ∀ (b : ℤ) (N : D.{c, v, r, w} J R),
    N.IsGE b → ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d)

private noncomputable def homFixed_leftMap
    {K L : Complex.{c, v, r} J R} (f : K ⟶ L) :
    WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⟶
      WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R K :=
  Functor.whiskerLeft (WeilConjectures.coefficientHomResolution.{r, c, v} J R)
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op)

private theorem homFixed_comparison_left
    {K L : Complex.{c, v, r} J R} (f : K ⟶ L) (M : Complex.{c, v, r} J R) :
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (𝟙 (DerivedCategory.Q.obj M))) ≫
        (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R K M).hom =
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L M).hom ≫
        DerivedCategory.Q.map ((homFixed_leftMap.{c, v, r} J R f).app M) := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let e := Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun F ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ F).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ F⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)
  have h :
      ((DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom f.op (𝟙 M)) ≫
          (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R K M).hom =
        (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L M).hom ≫
          ((𝟭 _).prod (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
            Functor.uncurry.obj
              (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
                DerivedCategory.Q).map (Prod.mkHom f.op (𝟙 M)) :=
    e.hom.naturality (Prod.mkHom f.op (𝟙 M))
  simpa [homFixed_leftMap, WeilConjectures.SfbHomFilteredColimit.homFixed,
    homComplex] using h

private noncomputable def homFixed_derivedIso (L : Complex.{c, v, r} J R) :
    DerivedCategory.Q ⋙ hom.{c, v, r, w} J R (DerivedCategory.Q.obj L) ≅
      WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⋙
        DerivedCategory.Q := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let e := Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun F ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ F).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ F⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)
  refine NatIso.ofComponents
    (fun M ↦ WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L M) ?_
  intro M N f
  have h :
      ((DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op L)) f) ≫
          (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L N).hom =
        (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L M).hom ≫
          ((𝟭 _).prod (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
            Functor.uncurry.obj
              (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
                DerivedCategory.Q).map (Prod.mkHom (𝟙 (op L)) f) :=
    e.hom.naturality (Prod.mkHom (𝟙 (op L)) f)
  simpa [WeilConjectures.SfbHomFilteredColimit.homFixed, homComplex] using h

-- Later arguments use these constructions only through their functor and comparison APIs.
attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso

open CategoryTheory.Pretriangulated.Opposite in
private theorem homFixed_homology_exact
    (T : Pretriangulated.Triangle (Complex.{c, v, r} J R))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈
      distTriang (D.{c, v, r, w} J R))
    (M : Complex.{c, v, r} J R) (q : ℤ) :
    (ComposableArrows.mk₂
      (HomologicalComplex.homologyMap ((homFixed_leftMap.{c, v, r} J R T.mor₂).app M) q)
      (HomologicalComplex.homologyMap
        ((homFixed_leftMap.{c, v, r} J R T.mor₁).app M) q)).Exact := by
  classical
  let F := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj (DerivedCategory.Q.obj M)
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact.{c, v, r, w} J R).1
    (DerivedCategory.Q.obj M)
  let : F.CommShift ℤ := s
  let : F.IsTriangulated := hs
  let HD := DerivedCategory.homologyFunctor (Modules.{c, v, r} J R) q
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let e (L : Complex.{c, v, r} J R) :
      HD.obj (F.obj (op (DerivedCategory.Q.obj L))) ≅
        (homComplex.{c, v, max c v r, max c v r}
          (R := R) L (I.obj M)).homology q :=
    HD.mapIso (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L M) ≪≫
      (DerivedCategory.homologyFunctorFactors (Modules.{c, v, r} J R) q).app _
  have he {K L : Complex.{c, v, r} J R} (f : K ⟶ L) :
      HD.map (F.map (DerivedCategory.Q.map f).op) ≫ (e K).hom =
        (e L).hom ≫ HomologicalComplex.homologyMap
          ((homFixed_leftMap.{c, v, r} J R f).app M) q := by
    let g : homComplex.{c, v, max c v r, max c v r} (R := R) L (I.obj M) ⟶
        homComplex.{c, v, max c v r, max c v r} (R := R) K (I.obj M) :=
      (homFixed_leftMap.{c, v, r} J R f).app M
    have hc := congrArg HD.map (homFixed_comparison_left.{c, v, r, w} J R f M)
    change HD.map (_ ≫ _) = HD.map (_ ≫ DerivedCategory.Q.map g) at hc
    simp only [Functor.map_comp] at hc
    have hn : HD.map (DerivedCategory.Q.map g) ≫
        ((DerivedCategory.homologyFunctorFactors (Modules.{c, v, r} J R) q).app _).hom =
      ((DerivedCategory.homologyFunctorFactors (Modules.{c, v, r} J R) q).app _).hom ≫
        HomologicalComplex.homologyMap g q :=
      (DerivedCategory.homologyFunctorFactors (Modules.{c, v, r} J R) q).hom.naturality g
    change HD.map (F.map (DerivedCategory.Q.map f).op) ≫
        (HD.map _ ≫ _) = (HD.map _ ≫ _) ≫ HomologicalComplex.homologyMap g q
    erw [← Category.assoc, hc, Category.assoc, hn, ← Category.assoc]
  let U := F.mapTriangle.obj
    ((Pretriangulated.triangleOpEquivalence (D.{c, v, r, w} J R)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj T)))
  have hU : U ∈ distTriang (D.{c, v, r, w} J R) :=
    F.map_distinguished _ (Pretriangulated.op_distinguished _ hT)
  exact ComposableArrows.exact_of_iso
    (ComposableArrows.isoMk₂ (e T.obj₃) (e T.obj₂) (e T.obj₁)
      (he T.mor₂) (he T.mor₁))
    (DerivedCategory.HomologySequence.exact₂ U hU q).exact_toComposableArrows

private theorem continuous_of_iso {A B : D.{c, v, r, w} J R} (e : A ≅ B)
    (hA : BoundedTargetHomContinuous.{c, v, r, w} J R A) :
    BoundedTargetHomContinuous.{c, v, r, w} J R B := by
  refine ⟨?_, ?_⟩
  · intro L hL
    exact hA.1 L (hL.map (fun eL ↦ eL ≪≫ e.symm))
  · obtain ⟨d, hd⟩ := hA.2
    refine ⟨d, fun b N hN ↦ ?_⟩
    have := hd b N hN
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
        e.symm.op).app N) (b + d)

private theorem bound_sourceShift (A : D.{c, v, r, w} J R) (d : ℤ)
    (hd : ∀ (b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
      ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d))
    (n b : ℤ) (N : D.{c, v, r, w} J R) (hN : N.IsGE b) :
    ((hom.{c, v, r, w} J R (A⟦n⟧)).obj N).IsGE (b + (d + n)) := by
  have := hd b N hN
  have hshift : (((hom.{c, v, r, w} J R A).obj N)⟦-n⟧).IsGE (b + (d + n)) :=
    DerivedCategory.TStructure.t.isGE_shift _ (b + d) (-n) _ (by omega)
  change DerivedCategory.TStructure.t.IsGE
    ((hom.{c, v, r, w} J R A ⋙ shiftFunctor _ (-n)).obj N) (b + (d + n)) at hshift
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((sourceShift.{c, v, r, w} J R A n).app N) _

private theorem continuous_shift (A : D.{c, v, r, w} J R)
    (hA : BoundedTargetHomContinuous.{c, v, r, w} J R A) (n : ℤ) :
    BoundedTargetHomContinuous.{c, v, r, w} J R (A⟦n⟧) := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ?_⟩
  · intro L hL I _ _ _ M b hM
    obtain ⟨eL⟩ := hL
    let K : Complex.{c, v, r} J R := L⟦-n⟧
    let eK : DerivedCategory.Q.obj K ≅ A :=
      (DerivedCategory.Q.commShiftIso (-n)).app L ≪≫
        (shiftFunctor _ (-n)).mapIso eL ≪≫ (shiftEquiv _ n).unitIso.symm.app A
    have hK : QuasiIso (colimit.post M
        (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R K)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp (hA.1 K ⟨eK⟩ I M b hM)
    let F := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R K
    let G := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L
    let eKL : DerivedCategory.Q.obj (K⟦n⟧) ≅ DerivedCategory.Q.obj L :=
      DerivedCategory.Q.mapIso ((shiftEquiv _ n).counitIso.app L)
    let eD : (F ⋙ shiftFunctor _ (-n)) ⋙ DerivedCategory.Q ≅ G ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerLeft F (DerivedCategory.Q.commShiftIso (-n)) ≪≫
      Functor.isoWhiskerRight (homFixed_derivedIso.{c, v, r, w} J R K).symm
        (shiftFunctor _ (-n)) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q
        (sourceShift.{c, v, r, w} J R (DerivedCategory.Q.obj K) n) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Q
        (((Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).mapIso
          (((DerivedCategory.Q.commShiftIso n).app K).symm ≪≫ eKL).symm.op)) ≪≫
      homFixed_derivedIso.{c, v, r, w} J R L
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact post_quasiIso_derivedIso _ _ eD M
      (post_quasiIso_shift _ M (-n) hK)
  · obtain ⟨d, hd⟩ := hA.2
    exact ⟨d + n, bound_sourceShift.{c, v, r, w} J R A d hd n⟩

open CategoryTheory.Pretriangulated.Opposite in
private theorem bound_zero (b : ℤ) (N : D.{c, v, r, w} J R) :
    ((hom.{c, v, r, w} J R 0).obj N).IsGE b := by
  let F := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj N
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact.{c, v, r, w} J R).1 N
  let : F.CommShift ℤ := s
  let : F.IsTriangulated := hs
  exact DerivedCategory.TStructure.t.isGE_of_isZero
    (F.map_isZero (isZero_zero (D.{c, v, r, w} J R)).op) b

open CategoryTheory.Pretriangulated.Opposite in
private theorem zero_source_hom_isZero
    (L M : Complex.{c, v, r} J R)
    (hL : Nonempty (DerivedCategory.Q.obj L ≅ (0 : D.{c, v, r, w} J R))) :
    IsZero (DerivedCategory.Q.obj
      ((WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L).obj M)) := by
  obtain ⟨e⟩ := hL
  let F := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj (DerivedCategory.Q.obj M)
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact.{c, v, r, w} J R).1
    (DerivedCategory.Q.obj M)
  let : F.CommShift ℤ := s
  let : F.IsTriangulated := hs
  have h := F.map_isZero ((isZero_zero (D.{c, v, r, w} J R)).of_iso e).op
  exact h.of_iso (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w}
    J R L M).symm

private theorem continuous_zero :
    BoundedTargetHomContinuous.{c, v, r, w} J R 0 := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro L hL I _ _ _ M b _
    have hs := isZero_Q_colimit (M ⋙
      WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)
      (fun i ↦ zero_source_hom_isZero.{c, v, r, w} J R L (M.obj i) hL)
    have ht := zero_source_hom_isZero.{c, v, r, w} J R L (colimit M) hL
    exact hs.isIso ht _
  · intro b N _
    simpa only [add_zero] using bound_zero.{c, v, r, w} J R b N

open CategoryTheory.Pretriangulated.Opposite in
private theorem bound_triangle
    (T : Pretriangulated.Triangle (D.{c, v, r, w} J R))
    (hT : T ∈ distTriang (D.{c, v, r, w} J R))
    (dA dC : ℤ)
    (hA : ∀ (b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
      ((hom.{c, v, r, w} J R T.obj₁).obj N).IsGE (b + dA))
    (hC : ∀ (b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
      ((hom.{c, v, r, w} J R T.obj₃).obj N).IsGE (b + dC))
    (b : ℤ) (N : D.{c, v, r, w} J R) (hN : N.IsGE b) :
    ((hom.{c, v, r, w} J R T.obj₂).obj N).IsGE (b + min dA dC) := by
  classical
  let F := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj N
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact.{c, v, r, w} J R).1 N
  let : F.CommShift ℤ := s
  let : F.IsTriangulated := hs
  have hA' := hA b N hN
  have hC' := hC b N hN
  have hA'' := DerivedCategory.TStructure.t.isGE_of_ge
    ((hom.{c, v, r, w} J R T.obj₁).obj N) (b + min dA dC) (b + dA)
    (by omega)
  have hC'' := DerivedCategory.TStructure.t.isGE_of_ge
    ((hom.{c, v, r, w} J R T.obj₃).obj N) (b + min dA dC) (b + dC)
    (by omega)
  exact DerivedCategory.TStructure.t.isGE₂
    (F.mapTriangle.obj ((Pretriangulated.triangleOpEquivalence _).functor.obj (op T)))
    (F.map_distinguished _ (Pretriangulated.op_distinguished T hT))
    (b + min dA dC) hC'' hA''

private theorem continuous_middle
    (T : Pretriangulated.Triangle (D.{c, v, r, w} J R))
    (hT : T ∈ distTriang (D.{c, v, r, w} J R))
    (hA : BoundedTargetHomContinuous.{c, v, r, w} J R T.obj₁)
    (hC : BoundedTargetHomContinuous.{c, v, r, w} J R T.obj₃) :
    BoundedTargetHomContinuous.{c, v, r, w} J R T.obj₂ := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  refine ⟨?_, ?_⟩
  · intro L hL I _ _ _ M b hM
    obtain ⟨eL⟩ := hL
    obtain ⟨K, f, ⟨eK⟩, ⟨eC⟩⟩ := triangle_model_with_middle T hT L eL
    let t := CochainComplex.mappingCone.triangle f
    have ht := DerivedCategory.mappingCone_triangle_distinguished f
    have hrot : DerivedCategory.Q.mapTriangle.obj t.rotate ∈
        distTriang (D.{c, v, r, w} J R) :=
      Pretriangulated.isomorphic_distinguished _ (Pretriangulated.rot_of_distTriang _ ht) _
        (DerivedCategory.Q.mapTriangleRotateIso.app t).symm
    have hinv : DerivedCategory.Q.mapTriangle.obj t.invRotate ∈
        distTriang (D.{c, v, r, w} J R) :=
      Pretriangulated.isomorphic_distinguished _ (Pretriangulated.inv_rot_of_distTriang _ ht) _
        (DerivedCategory.Q.mapTriangleInvRotateIso.app t).symm
    have hcont (A : D.{c, v, r, w} J R)
        (hA : BoundedTargetHomContinuous.{c, v, r, w} J R A)
        (B : Complex.{c, v, r} J R) (eB : DerivedCategory.Q.obj B ≅ A) :
        QuasiIso (colimit.post M
          (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R B)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp (hA.1 B ⟨eB⟩ I M b hM)
    let H := WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact post_quasiIso_fiveLemma (H (K⟦(1 : ℤ)⟧))
      (H (CochainComplex.mappingCone f)) (H L) (H K)
      (H ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧))
      (homFixed_leftMap.{c, v, r} J R t.mor₃) (homFixed_leftMap.{c, v, r} J R t.mor₂)
      (homFixed_leftMap.{c, v, r} J R t.mor₁) (homFixed_leftMap.{c, v, r} J R t.invRotate.mor₁)
      (homFixed_homology_exact.{c, v, r, w} J R t.rotate hrot)
      (homFixed_homology_exact.{c, v, r, w} J R t ht)
      (homFixed_homology_exact.{c, v, r, w} J R t.invRotate hinv) M
      (hcont (T.obj₁⟦(1 : ℤ)⟧) (continuous_shift.{c, v, r, w} J R T.obj₁ hA 1) _
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K ≪≫
          (shiftFunctor _ (1 : ℤ)).mapIso eK))
      (hcont T.obj₃ hC _ eC) (hcont T.obj₁ hA K eK)
      (hcont (T.obj₃⟦(-1 : ℤ)⟧) (continuous_shift.{c, v, r, w} J R T.obj₃ hC (-1)) _
        ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone f) ≪≫
          (shiftFunctor _ (-1 : ℤ)).mapIso eC))
  · obtain ⟨dA, hdA⟩ := hA.2
    obtain ⟨dC, hdC⟩ := hC.2
    exact ⟨min dA dC, bound_triangle.{c, v, r, w} J R T hT dA dC hdA hdC⟩

end CategoryTheory.RingedHomUniverses
