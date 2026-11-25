/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
import all Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Geometric part of the affine acyclic hypercover construction

This theorem packages the finite-basis construction, its degreewise coproduct realization,
and the component evaluation comparisons.  The componentwise lifting theorem then supplies
weak contractibility. (auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

private def familyMap {D E : Type (u + 1)} [Category.{v} D] [Category.{w} E]
    (G : D ⥤ E) : FormalCoproduct.{u + 1} D ⥤ FormalCoproduct.{u + 1} E where
  obj Q := ⟨Q.I, fun i ↦ G.obj (Q.obj i)⟩
  map f := ⟨f.f, fun i ↦ G.map (f.φ i)⟩
  map_id Q := FormalCoproduct.hom_ext rfl (fun i ↦ by simp)
  map_comp f g := FormalCoproduct.hom_ext rfl (fun i ↦ by simp)

private theorem familyMap_preservesFiniteLimits
    {D E : Type (u + 1)} [Category.{v} D] [Category.{w} E]
    [HasFiniteLimits D] [HasFiniteLimits E]
    (G : D ⥤ E) [PreservesFiniteLimits G] :
    PreservesFiniteLimits (familyMap G) := by
  classical
  have ht : PreservesLimit (Functor.empty (FormalCoproduct.{u + 1} D))
      (familyMap G) := by
    apply preservesLimit_of_preserves_limit_cone
      (FormalCoproduct.isTerminalIncl (⊤_ D) terminalIsTerminal)
    exact (isLimitMapConeEmptyConeEquiv (familyMap G) _).symm
      (FormalCoproduct.isTerminalIncl _ (terminalIsTerminal.isTerminalObj G))
  have : PreservesLimitsOfShape (Discrete PEmpty) (familyMap G) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  have hp (X Y Z : FormalCoproduct.{u + 1} D) (f : X ⟶ Z) (g : Y ⟶ Z) :
      PreservesLimit (cospan f g) (familyMap G) := by
    let pb (i : Function.Pullback f.f g.f) :=
      pullback.cone (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2)
    apply preservesLimit_of_preserves_limit_cone
      (FormalCoproduct.isLimitPullbackCone f g pb (fun _ ↦ pullback.isLimit _ _))
    let pb' (i : Function.Pullback f.f g.f) :
        PullbackCone
          (G.map (f.φ i.1.1) ≫ eqToHom (by rw [i.2]))
          (G.map (g.φ i.1.2)) :=
      PullbackCone.mk (G.map (pb i).fst) (G.map (pb i).snd) (by
        simpa only [Functor.map_comp, eqToHom_map] using congrArg G.map (pb i).condition)
    have hpb' (i : Function.Pullback f.f g.f) : IsLimit (pb' i) := by
      have hpG := (IsPullback.of_isLimit (pullback.isLimit
        (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2))).map G
      have h' : IsPullback (G.map (pb i).fst) (G.map (pb i).snd)
          (G.map (f.φ i.1.1) ≫ eqToHom (by rw [i.2])) (G.map (g.φ i.1.2)) := by
        simpa only [Functor.map_comp, eqToHom_map] using hpG
      exact h'.isLimit
    exact (PullbackCone.isLimitMapConeEquiv
      (FormalCoproduct.pullbackCone f g pb) (familyMap G)).symm
      (FormalCoproduct.isLimitPullbackCone
        ((familyMap G).map f) ((familyMap G).map g) pb' hpb')
  have : PreservesLimitsOfShape WalkingCospan (familyMap G) :=
    ⟨fun {F} ↦ by
      have := hp (F.obj .left) (F.obj .right) (F.obj .one)
        (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)
      exact preservesLimit_of_iso_diagram (familyMap G) (diagramIsoCospan F).symm⟩
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

namespace GeometryRealization

open FormalCoproduct

private noncomputable abbrev sheafRealization
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [J.Subcanonical] (T : C) :
    FormalCoproduct.{u + 1} (Over T) ⥤ Over (J.uliftYoneda.{u + 1}.obj T) :=
  by
    let : HasSheafify J (Type (u + 1)) :=
      inferInstanceAs (HasSheafify J (Type (max (u + 1) u)))
    let : HasCoproducts.{u + 1} (Sheaf J (Type (u + 1))) := fun I ↦
      Sheaf.instHasColimitsOfShape
    let : HasCoproducts.{u + 1} (Over (J.uliftYoneda.{u + 1}.obj T)) :=
      fun I ↦ CategoryTheory.Over.instHasColimitsOfShape
    exact (FormalCoproduct.eval _ _).obj (Over.post J.uliftYoneda.{u + 1})

private noncomputable def restrictedFamilyYoneda (C : Type (u + 1)) [Category.{u} C] :
    FormalCoproduct.{u + 1} C ⥤ Cᵒᵖ ⥤ Type (u + 1) :=
  CategoryTheory.yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (incl C).op

private noncomputable def restrictedFamilyCofan {C : Type (u + 1)} [Category.{u} C]
    (Q : FormalCoproduct.{u + 1} C) :
    Cofan (fun i : Q.I ↦ CategoryTheory.uliftYoneda.{u + 1}.obj (Q.obj i)) :=
  Cofan.mk ((restrictedFamilyYoneda C).obj Q) (fun i ↦
    { app := fun U ↦ ↾fun g ↦ Hom.fromIncl i g.down })

set_option backward.isDefEq.respectTransparency false in
private noncomputable def isColimitRestrictedFamilyCofan {C : Type (u + 1)} [Category.{u} C]
    (Q : FormalCoproduct.{u + 1} C) : IsColimit (restrictedFamilyCofan Q) := by
  refine Cofan.IsColimit.mk _ (fun s ↦
    { app := fun U ↦ ↾fun f ↦ (s.inj (f.f PUnit.unit)).app U ⟨f.φ PUnit.unit⟩
      naturality := ?_ }) ?_ ?_
  · intro U V f
    ext g
    exact ConcreteCategory.congr_hom ((s.inj (g.f PUnit.unit)).naturality f) ⟨g.φ PUnit.unit⟩
  · intro s i
    ext U g
    rfl
  · intro s m hm
    ext U f
    change ((incl C).obj U.unop ⟶ Q) at f
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (hm (f.f PUnit.unit)) U) ⟨f.φ PUnit.unit⟩
    change m.app U (Hom.fromIncl _ _) = _ at h
    exact (congrArg (fun t ↦ m.app U t) (Hom.fromIncl_asSigma f)).symm.trans h

private noncomputable def familyYonedaIso (C : Type (u + 1)) [Category.{u} C] :
    FormalCoproduct.uliftYoneda.{u + 1} (C := C) ≅ restrictedFamilyYoneda C := by
  let b (Q : FormalCoproduct.{u + 1} C) :
      FormalCoproduct.uliftYoneda.{u + 1}.obj Q ≅ (restrictedFamilyYoneda C).obj Q :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso
      (isColimitRestrictedFamilyCofan Q)
  have hb (Q : FormalCoproduct.{u + 1} C) (i : Q.I) :
      Sigma.ι (fun i ↦ CategoryTheory.uliftYoneda.{u + 1}.obj (Q.obj i)) i ≫ (b Q).hom =
        (restrictedFamilyCofan Q).inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
      (isColimitRestrictedFamilyCofan Q) (Discrete.mk i)
  refine NatIso.ofComponents b ?_
  intro Q R f
  apply Sigma.hom_ext
  intro i
  simp only [FormalCoproduct.uliftYoneda, eval_obj_map, Sigma.ι_comp_desc_assoc,
    Category.assoc, Function.comp_def]
  rw [hb R, ← Category.assoc, hb Q]
  ext U g
  rfl

private theorem familyYoneda_preservesLimits (C : Type (u + 1)) [Category.{u} C] :
    PreservesLimits (FormalCoproduct.uliftYoneda.{u + 1} (C := C)) := by
  have : PreservesLimits (restrictedFamilyYoneda C) := by
    dsimp [restrictedFamilyYoneda]
    infer_instance
  exact preservesLimits_of_natIso (familyYonedaIso C).symm

private def familyToOver {C : Type (u + 1)} [Category.{u} C] (T : C) :
    FormalCoproduct.{u + 1} (Over T) ⥤ Over ((incl C).obj T) where
  obj Q := Over.mk (Y := ⟨Q.I, fun i ↦ (Q.obj i).left⟩)
    ⟨fun _ ↦ PUnit.unit, fun i ↦ (Q.obj i).hom⟩
  map f := Over.homMk ⟨f.f, fun i ↦ (f.φ i).left⟩ (by
    refine hom_ext ?_ ?_
    · rfl
    · intro i
      simp [Over.w (f.φ i)])

private def overToFamily {C : Type (u + 1)} [Category.{u} C] (T : C) :
    Over ((incl C).obj T) ⥤ FormalCoproduct.{u + 1} (Over T) where
  obj Q := ⟨Q.left.I, fun i ↦ Over.mk (Q.hom.φ i)⟩
  map {Q R} f := ⟨f.left.f, fun i ↦ Over.homMk (f.left.φ i) (by
    obtain ⟨_, h⟩ := (hom_ext_iff _ _).mp (Over.w f)
    simpa [incl] using h i)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def familyOverEquiv {C : Type (u + 1)} [Category.{u} C] (T : C) :
    FormalCoproduct.{u + 1} (Over T) ≌ Over ((incl C).obj T) :=
  CategoryTheory.Equivalence.mk (familyToOver T) (overToFamily T)
    (NatIso.ofComponents
      (fun Q ↦ isoOfComponents (Equiv.refl _) (fun i ↦ Over.isoMk (Iso.refl _)))
      (by
        intro Q R f
        ext i
        · rfl
        · simp [familyToOver, overToFamily, isoOfComponents, Over.homMk_left,
            Over.isoMk_hom_left]))
    (NatIso.ofComponents
      (fun Q ↦ Over.isoMk (Iso.refl _) (by
        refine hom_ext ?_ ?_
        · funext i
          exact Subsingleton.elim (α := PUnit) _ _
        · intro i
          simp [familyToOver, overToFamily, incl]))
      (by
        intro Q R f
        ext i
        · rfl
        · simp [familyToOver, overToFamily, Over.homMk_left, Over.isoMk_hom_left]))

private noncomputable def isColimitSelf {D : Type (u + 1)} [Category.{u} D]
    (Q : FormalCoproduct.{u + 1} D) :
    IsColimit (Cofan.mk Q (fun i : Q.I ↦ Hom.fromIncl i (𝟙 (Q.obj i)))) :=
  (coproductIsCoproduct Q.toFun).ofIsoColimit
    (Cocone.ext (coproductIsoSelf Q) (fun i ↦ ι_comp_coproductIsoSelf_hom Q i.as))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def evalExtensionIso
    {D : Type (u + 1)} [Category.{u} D] {E : Type*} [Category* E] [HasCoproducts.{u + 1} E]
    (G : FormalCoproduct.{u + 1} D ⥤ E) (H : D ⥤ E)
    (hG : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G)
    (e : incl D ⋙ G ≅ H) : G ≅ (eval _ _).obj H := by
  let c (Q : FormalCoproduct.{u + 1} D) :=
    Cofan.mk (G.obj Q) (fun i : Q.I ↦ G.map (Hom.fromIncl i (𝟙 _)))
  have hc (Q : FormalCoproduct.{u + 1} D) : IsColimit (c Q) := by
    have := hG Q.I
    exact isColimitCofanMkObjOfIsColimit G _ _ (isColimitSelf Q)
  let d (Q : FormalCoproduct.{u + 1} D) :=
    Cofan.mk (∐ fun i : Q.I ↦ H.obj (Q.obj i))
      (fun i : Q.I ↦ (e.app (Q.obj i)).hom ≫ Sigma.ι (fun i : Q.I ↦ H.obj (Q.obj i)) i)
  have hd (Q : FormalCoproduct.{u + 1} D) : IsColimit (d Q) := by
    let ei : Discrete.functor (fun i : Q.I ↦ G.obj ((incl D).obj (Q.obj i))) ≅
        Discrete.functor (fun i : Q.I ↦ H.obj (Q.obj i)) :=
      Discrete.natIso (fun i ↦ e.app (Q.obj i.as))
    exact (IsColimit.precomposeHomEquiv ei _).symm (coproductIsCoproduct _)
  let b (Q : FormalCoproduct.{u + 1} D) := (hc Q).coconePointUniqueUpToIso (hd Q)
  have hb (Q : FormalCoproduct.{u + 1} D) (i : Q.I) :
      G.map (Hom.fromIncl i (𝟙 _)) ≫ (b Q).hom =
        (e.app (Q.obj i)).hom ≫ Sigma.ι (fun i : Q.I ↦ H.obj (Q.obj i)) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (hc Q) (hd Q) (Discrete.mk i)
  refine NatIso.ofComponents b ?_
  intro Q R f
  apply Cofan.IsColimit.hom_ext (hc Q)
  intro i
  change G.map (Hom.fromIncl i (𝟙 _)) ≫ G.map f ≫ (b R).hom =
    G.map (Hom.fromIncl i (𝟙 _)) ≫ (b Q).hom ≫ ((eval _ _).obj H).map f
  rw [← G.map_comp_assoc]
  have h : Hom.fromIncl i (𝟙 _) ≫ f =
      (incl D).map (f.φ i) ≫ Hom.fromIncl (f.f i) (𝟙 _) := by
    ext j
    · rfl
    · simp [Hom.fromIncl, incl]
  rw [h, G.map_comp, Category.assoc, hb R]
  trans (e.app (Q.obj i)).hom ≫ H.map (f.φ i) ≫
    Sigma.ι (fun i : R.I ↦ H.obj (R.obj i)) (f.f i)
  · exact e.hom.naturality_assoc (f.φ i) _
  · simp only [eval_obj_map, Function.comp_def, ← Category.assoc]
    rw [hb Q]
    simp [Category.assoc]

private theorem overPost_preservesCoproducts
    {D : Type*} [Category* D] [HasCoproducts.{u + 1} D]
    {E : Type*} [Category* E] [HasCoproducts.{u + 1} E]
    (G : D ⥤ E) (X : D) (I : Type (u + 1))
    [PreservesColimitsOfShape (Discrete I) G] :
    PreservesColimitsOfShape (Discrete I) (Over.post G (X := X)) := by
  have : PreservesColimitsOfShape (Discrete I)
      (Over.post G (X := X) ⋙ Over.forget (G.obj X)) := by
    change PreservesColimitsOfShape (Discrete I) (Over.forget X ⋙ G)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (Over.post G) (Over.forget (G.obj X))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Realizing formal families of representables over `T` preserves finite limits.
Source: Stacks Project, Hypercoverings, Tag 01G2(2) and Tag 0DB1.

Proof: the formal-family Yoneda functor is the ordinary Yoneda functor on formal
coproducts restricted to singleton families. The coproduct universal property and
the equivalence between maps from a singleton and pairs `(i, U ⟶ Q_i)` give the
natural comparison isomorphism. Both ordinary Yoneda and restriction preserve
limits, so formal-family Yoneda does too, as in Tag 01G2(2).

A formal family over `T` is equivalently a formal family in `C` with a morphism to
the singleton family `{T}`. Use this equivalence, apply formal-family Yoneda on
the slice, and then apply sheafification on the slice. These functors preserve
finite limits. Identify the resulting base with `h_T` by the singleton-coproduct
isomorphism and the sheafification counit; changing the base along an isomorphism
also preserves limits. The resulting composite preserves coproducts and agrees
with sheaf Yoneda on singleton families. Since every formal family is the
coproduct of its singleton families, the coproduct universal property gives a
natural isomorphism from this composite to `sheafRealization`. Transporting
finite-limit preservation along that isomorphism completes the proof.
(auxiliary; not a blueprint node). -/
private theorem sheafRealization_preservesFiniteLimits {C : Type (u + 1)} [Category.{u} C]
    [HasPullbacks C] (J : GrothendieckTopology C) [J.Subcanonical] (T : C) :
    PreservesFiniteLimits (sheafRealization J T) := by
  let : HasSheafify J (Type (u + 1)) :=
    inferInstanceAs (HasSheafify J (Type (max (u + 1) u)))
  let : HasCoproducts.{u + 1} (Sheaf J (Type (u + 1))) := fun I ↦
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Over (J.uliftYoneda.{u + 1}.obj T)) :=
    fun I ↦ CategoryTheory.Over.instHasColimitsOfShape
  let H := FormalCoproduct.uliftYoneda.{u + 1} (C := C)
  let S := presheafToSheaf J (Type (u + 1))
  have : PreservesLimits H := familyYoneda_preservesLimits C
  let q : incl C ⋙ H ≅ CategoryTheory.uliftYoneda.{u + 1} :=
    (evalCompInclIsoId C (Cᵒᵖ ⥤ Type (u + 1))).app CategoryTheory.uliftYoneda.{u + 1}
  let r : CategoryTheory.uliftYoneda.{u + 1} ⋙ S ≅ J.uliftYoneda.{u + 1} :=
    Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf.symm S ≪≫
    (Functor.associator J.uliftYoneda.{u + 1} (sheafToPresheaf J (Type (u + 1))) S) ≪≫
      Functor.isoWhiskerLeft J.uliftYoneda.{u + 1}
        (asIso (sheafificationAdjunction J (Type (u + 1))).counit) ≪≫
      (J.uliftYoneda.{u + 1}).rightUnitor
  let z : incl C ⋙ (H ⋙ S) ≅ J.uliftYoneda.{u + 1} :=
    (Functor.associator (incl C) H S).symm ≪≫ Functor.isoWhiskerRight q S ≪≫ r
  let G := (familyOverEquiv T).functor ⋙ Over.post (H ⋙ S) ⋙ Over.map (z.app T).hom
  have : PreservesFiniteLimits (H ⋙ S) := comp_preservesFiniteLimits H S
  have : PreservesFiniteLimits
      (Over.post (H ⋙ S) (X := (incl C).obj T) ⋙ Over.map (z.app T).hom) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have hG (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) G := by
    have : PreservesColimitsOfShape (Discrete I) H := by
      dsimp [H, FormalCoproduct.uliftYoneda]
      infer_instance
    have : PreservesColimitsOfShape (Discrete I) (Over.post (H ⋙ S)
        (X := (incl C).obj T)) := overPost_preservesCoproducts _ _ _
    dsimp [G]
    infer_instance
  let e : incl (Over T) ⋙ G ≅ Over.post J.uliftYoneda.{u + 1} :=
    NatIso.ofComponents (fun X ↦ Over.isoMk (z.app X.left)
      (by exact (z.hom.naturality X.hom).symm))
      (by
        intro X Y f
        apply Over.OverMorphism.ext
        exact z.hom.naturality f.left)
  exact preservesFiniteLimits_of_natIso (evalExtensionIso G (Over.post J.uliftYoneda.{u + 1}) hG e)

private theorem yoneda_hom_ext_of_cover {C : Type (u + 1)} [Category.{u} C]
    (J : Precoverage C) [J.toGrothendieck.Subcanonical]
    {X : C} {Z : Sheaf J.toGrothendieck (Type (u + 1))}
    (g h : J.toGrothendieck.uliftYoneda.{u + 1}.obj X ⟶ Z)
    {I : Type (u + 1)} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Presieve.ofArrows U f ∈ J X)
    (heq : ∀ i, J.toGrothendieck.uliftYoneda.{u + 1}.map (f i) ≫ g =
      J.toGrothendieck.uliftYoneda.{u + 1}.map (f i) ≫ h) : g = h := by
  apply J.toGrothendieck.uliftYonedaEquiv.injective
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp Z.property
    |>.isSheafFor_of_mem_precoverage hf).isSeparatedFor.ext
  rintro V k ⟨i⟩
  simpa only [J.toGrothendieck.uliftYonedaEquiv_naturality] using
    congrArg J.toGrothendieck.uliftYonedaEquiv (heq i)

/-- Componentwise covering morphisms induce epimorphisms after sheaf realization.
Source: Stacks Project, Hypercoverings, Tags 01G3 and 0DB1.

Proof: test cancellation on each representable summand of the target. The covering
hypothesis and separatedness of the testing sheaf reduce equality there to equality on
all summands mapping to that component. These equalities follow by precomposing the
assumed equality with the corresponding source coproduct inclusions. Empty covering
families are allowed: separatedness gives the same conclusion in this case.
(auxiliary; not a blueprint node). -/
private theorem sheafRealization_map_epi {C : Type (u + 1)} [Category.{u} C]
    (J : Precoverage C) [J.toGrothendieck.Subcanonical] {T : C}
    {X Y : FormalCoproduct.{u + 1} (Over T)} (f : X ⟶ Y)
    (hf : ∀ j : Y.I,
      Presieve.ofArrows
        (fun i : {i : X.I // f.f i = j} ↦ (X.obj i.val).left)
        (fun i ↦ (f.φ i.val ≫ eqToHom (congrArg Y.obj i.property)).left) ∈
          J (Y.obj j).left) :
    Epi ((sheafRealization J.toGrothendieck T).map f) := by
  let : HasCoproducts.{u + 1} (Sheaf J.toGrothendieck (Type (u + 1))) := fun I ↦
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Over (J.toGrothendieck.uliftYoneda.{u + 1}.obj T)) :=
    fun I ↦ CategoryTheory.Over.instHasColimitsOfShape
  constructor
  intro Z g h hgh
  apply Sigma.hom_ext
  intro j
  apply (Over.forget (J.toGrothendieck.uliftYoneda.{u + 1}.obj T)).map_injective
  apply yoneda_hom_ext_of_cover J _ _ _ _ (hf j)
  intro i
  obtain ⟨i, hi⟩ := i
  dsimp at hi ⊢
  subst j
  have hh := congrArg (fun k ↦
    Sigma.ι (fun i : X.I ↦
      (Over.post J.toGrothendieck.uliftYoneda.{u + 1}).obj (X.obj i)) i ≫ k) hgh
  have hh' := congrArg (fun k ↦ (Over.forget _).map k) hh
  simpa [sheafRealization, eval, Category.assoc, ← Functor.map_comp,
    Function.comp_def, Over.post] using hh'

end GeometryRealization

private theorem properFace_finite (n : ℕ) :
    Finite (SimplicialObject.ProperFaceCategory n) := by
  let f (a : SimplicialObject.ProperFaceCategory n) :
      Σ r : Fin n, (SimplexCategory.mk r.val ⟶ SimplexCategory.mk n) :=
    ⟨⟨a.obj.left.len, a.property.1⟩, a.obj.hom⟩
  apply Finite.of_injective f
  rintro ⟨⟨a, ar, ah⟩, ha⟩ ⟨⟨b, br, bh⟩, hb⟩ h
  have hab : a = b := SimplexCategory.ext (congrArg (fun x ↦ x.1.val) h)
  subst b
  cases ar
  cases br
  have hr : ah = bh := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst bh
  rfl

@[instance_reducible] private noncomputable def properFace_finCategory (n : ℕ) :
    FinCategory (SimplicialObject.ProperFaceCategory n) where
  fintypeObj := @Fintype.ofFinite _ (properFace_finite n)
  fintypeHom a b := by
    have : Finite (a.obj.left ⟶ b.obj.left) := inferInstance
    have : Finite (a ⟶ b) := Finite.of_injective (fun f ↦ f.hom.left) (by
      intro f g h
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext h)
    exact Fintype.ofFinite _

private def properFaceDiagramIso
    {D : Type*} [Category* D] {E : Type*} [Category* E] {C : Type*} [Category* C]
    (K : SimplicialObject D) (F : D ⥤ E) (U : SimplicialObject C) (H : C ⥤ E)
    (e : K ⋙ F ≅ U ⋙ H) (n : ℕ) :
    K.properFaceDiagram n ⋙ F ≅ U.properFaceDiagram n ⋙ H :=
  NatIso.ofComponents (fun a ↦ e.app (op a.unop.obj.left)) (by
    intro a b f
    exact e.hom.naturality f.unop.hom.left.op)

private theorem matching_epi_of_properFace
    {D : Type*} [Category* D] {E : Type*} [Category* E] {C : Type*} [Category* C]
    (K : SimplicialObject D) (F : D ⥤ E) [PreservesFiniteLimits F]
    (U : SimplicialObject C) (H : C ⥤ E) [PreservesFiniteLimits H]
    (e : K ⋙ F ≅ U ⋙ H) (n : ℕ)
    (M : Cone (K.properFaceDiagram n)) (hM : IsLimit M)
    (κ : K _⦋n⦌ ⟶ M.pt)
    (hκ : ∀ a : SimplicialObject.ProperFaceCategory n,
      κ ≫ M.π.app (op a) = K.map a.obj.hom.op)
    [Epi (F.map κ)]
    (c : Cone (U.properFaceDiagram n)) (hc : IsLimit c)
    (μ : U _⦋n⦌ ⟶ c.pt)
    (hμ : ∀ a : SimplicialObject.ProperFaceCategory n,
      μ ≫ c.π.app (op a) = U.map a.obj.hom.op) : Epi (H.map μ) := by
  let := properFace_finCategory n
  let d := (Cone.postcompose (properFaceDiagramIso K F U H e n).hom).obj (F.mapCone M)
  have hd : IsLimit d := (IsLimit.postcomposeHomEquiv _ _).symm
    (isLimitOfPreserves F hM)
  let c' := H.mapCone c
  have hc' : IsLimit c' := isLimitOfPreserves H hc
  let b := hd.conePointUniqueUpToIso hc'
  have h : H.map μ = (e.app (op ⦋n⦌)).inv ≫ F.map κ ≫ b.hom := by
    apply hc'.hom_ext
    rintro ⟨a⟩
    change H.map μ ≫ H.map (c.π.app (op a)) = _
    rw [← H.map_comp, hμ a]
    simp only [Category.assoc, b, IsLimit.conePointUniqueUpToIso_hom_comp]
    change H.map (U.map a.obj.hom.op) = (e.app (op ⦋n⦌)).inv ≫
      F.map κ ≫ F.map (M.π.app (op a)) ≫ (e.app (op a.obj.left)).hom
    rw [← F.map_comp_assoc, hκ a]
    have he := e.hom.naturality a.obj.hom.op
    simpa only [Functor.comp_map, Iso.app_hom, Iso.app_inv,
      Iso.inv_hom_id_app_assoc] using
      congrArg (fun f ↦ (e.app (op ⦋n⦌)).inv ≫ f) he.symm
  rw [h]
  infer_instance

private theorem yoneda_epi_of_ulift
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {A B : C} (f : A ⟶ B) (h : Epi (J.uliftYoneda.{u + 1}.map f)) :
    Epi (J.yoneda.map f) := by
  let H := sheafCompose J uliftFunctor.{u + 1, u}
  let := h
  constructor
  intro Z g k hfg
  apply H.map_injective
  apply (cancel_epi (J.uliftYoneda.{u + 1}.map f)).mp
  change H.map (J.yoneda.map f) ≫ H.map g = H.map (J.yoneda.map f) ≫ H.map k
  rw [← H.map_comp, ← H.map_comp, hfg]

/-- Finite-basis geometry produces affine terms, component evaluation comparisons, and
epimorphic matching arrows. Source: Stacks Project, proetale.tex, Tag 09A1 (2), and
hypercovering.tex, Tags 0DAV, 0DB1, 0DB2
(auxiliary; not a blueprint node).
Proof: apply the finite-basis hypercover theorem in the qcqs subsite, then realize finite formal
coproducts in the full slice. Transport matching epimorphisms and component evaluation
bijections.
-/
theorem exists_affine_hypercover_geometry
    (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    ∃ U : SimplicialObject (Over W),
      (∀ n : ℕ, IsAffine (U _⦋n⦌).left.left) ∧
      (∀ n : ℕ, ∃ (I : Type (u + 1)) (V : I → X.ProEt)
        (maps : ∀ i : I, V i ⟶ (U _⦋n⦌).left),
        (∀ F : Sheaf (topology X) (Type (u + 1)),
          Function.Bijective (fun s : F.obj.obj (op (U _⦋n⦌).left) ↦
            fun i ↦ F.obj.map (maps i).op s)) ∧
        (∀ (i : I) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op (V i))))) ∧
      Epi ((topology X).yoneda.map (U _⦋0⦌).hom) ∧
      (∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌),
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋1⦌ ⟶ c.pt,
          (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) ∧
      (∀ n : ℕ, ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧
        ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) := by
  classical
  obtain ⟨haffqc, ⟨hpb, J, hJ, hinc, hsch, hcov, hslice, hadjoin⟩, hsub, hcop⟩ :=
    qcqs_finite_family_geometry.{u, u + 1, 0} X
  let := hpb
  have : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let T : Qcqs X := ⟨W, inferInstance, inferInstance⟩
  let B : Set (Qcqs X) := {V | IsAffine V.obj.left ∧
    ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op V.obj))}
  have hBcover (Q : Qcqs X) :
      ∃ (I : Type (u + 1)) (V : I → Qcqs X) (f : ∀ i, V i ⟶ Q),
        Finite I ∧ (∀ i, V i ∈ B) ∧ Presieve.ofArrows V f ∈ qcqsPrecoverage X Q := by
    let : CompactSpace Q.obj.left := Q.property.1
    obtain ⟨V, f, hf, hV, hweak⟩ := exists_affine_weaklyContractible_cover X Q.obj
    let V' : Qcqs X := ⟨V, (haffqc V hV).1, (haffqc V hV).2⟩
    let f' : V' ⟶ Q := ObjectProperty.homMk f
    refine ⟨PUnit, fun _ ↦ V', fun _ ↦ f', inferInstance, fun _ ↦ ⟨hV, hweak⟩, ?_⟩
    constructor
    · simpa [Presieve.map_ofArrows, Presieve.ofArrows_pUnit, f', qcqsInclusion] using hf
    · exact Precoverage.ofArrows_mem_finite _ _
  have hBadjoin (Q : Qcqs X) (I : Type (u + 1)) [Finite I]
      (V : I → Qcqs X) (f : ∀ i, V i ⟶ Q) (_hV : ∀ i, V i ∈ B)
      (hf : Presieve.ofArrows V f ∈ qcqsPrecoverage X Q)
      (P : Qcqs X) (_hP : P ∈ B) (g : P ⟶ Q) :
      Presieve.ofArrows V f ⊔ Presieve.singleton g ∈ qcqsPrecoverage X Q := by
    apply hadjoin Q _ _ hf
    simp [Precoverage.mem_finite_iff]
  obtain ⟨K, M, μ, hfinite, hbasis, hzero, hlim, hproj, hcover⟩ :=
    exists_site_finite_basis_hypercover (qcqsPrecoverage X) B hBcover hBadjoin T
  let G : Over T ⥤ Over W := Over.post (X := T) (qcqsInclusion X)
  have : HasFiniteLimits (Over T) := (hslice T).1
  have : PreservesFiniteLimits G := (hslice T).2.1
  let K' : SimplicialObject (FormalCoproduct.{u + 1} (Over W)) := K ⋙ familyMap G
  let Y := (topology X).uliftYoneda.{u + 1}
  have : PreservesFiniteLimits Y := ⟨fun J _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (Over.post Y (X := W)) := inferInstance
  let : HasPushouts (Sheaf (topology X) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Sheaf (topology X) (Type (u + 1))) := fun I ↦
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Over (Y.obj W)) :=
    fun I ↦ CategoryTheory.Over.instHasColimitsOfShape
  let R := GeometryRealization.sheafRealization (topology X) W
  have : PreservesFiniteLimits R :=
    GeometryRealization.sheafRealization_preservesFiniteLimits (topology X) W
  have : PreservesFiniteLimits (familyMap G) := familyMap_preservesFiniteLimits G
  let F := familyMap G ⋙ R
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have hcops (n : ℕ) := by
    let := hfinite n
    exact hcop (K _⦋n⦌).I (fun i ↦ ((K _⦋n⦌).obj i).left.obj)
      (fun i ↦ ((K _⦋n⦌).obj i).left.property.1)
      (fun i ↦ ((K _⦋n⦌).obj i).left.property.2)
  choose A ι e he hqc hqs haff hcolim hiso hprod hnat hempty using hcops
  let g (n : ℕ) : A n ⟶ W := Y.preimage
    ((hcolim n).some.desc (Cofan.mk (Y.obj W)
      (fun i ↦ Y.map (G.obj ((K _⦋n⦌).obj i)).hom)))
  have hιg (n : ℕ) (i : (K _⦋n⦌).I) :
      ι n i ≫ g n = (G.obj ((K _⦋n⦌).obj i)).hom := by
    apply Y.map_injective
    simp only [Functor.map_comp, g, Functor.map_preimage]
    exact (hcolim n).some.fac _ ⟨i⟩
  let a (n : ℕ) : Cofan (K' _⦋n⦌).obj :=
    Cofan.mk (Over.mk (g n)) (fun i ↦ Over.homMk (ι n i) (hιg n i))
  have hsa (n : ℕ) : IsColimit (Cofan.mk ((Over.post Y).obj (a n).pt)
      (fun i ↦ (Over.post Y).map ((a n).inj i))) := by
    apply isColimitOfReflects (Over.forget (Y.obj W))
    exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm (hcolim n).some
  have ha (n : ℕ) : IsColimit (a n) := by
    apply isColimitOfReflects (Over.post Y)
    exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm (hsa n)
  let U : SimplicialObject (Over W) :=
    { obj := fun n ↦ (a n.unop.len).pt
      map := fun {n m} φ ↦ (ha n.unop.len).desc
        (Cofan.mk (a m.unop.len).pt
          (fun i ↦ (K'.map φ).φ i ≫ (a m.unop.len).inj ((K'.map φ).f i)))
      map_id := by
        intro n
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K'.map (𝟙 n)).φ i ≫ _ = _
        rw [K'.map_id]
        simp
      map_comp := by
        intro n m l φ ψ
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K'.map (φ ≫ ψ)).φ i ≫ _ = _
        rw [K'.map_comp]
        simp [Category.assoc] }
  let b (n : ℕ) : F.obj (K _⦋n⦌) ≅ (Over.post Y).obj (a n).pt :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso (hsa n)
  have hb (n : ℕ) (i : (K _⦋n⦌).I) :
      Sigma.ι (fun i ↦ (Over.post Y).obj (G.obj ((K _⦋n⦌).obj i))) i ≫
        (b n).hom = (Over.post Y).map ((a n).inj i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
      (hsa n) (Discrete.mk i)
  let eb : K ⋙ F ≅ U ⋙ Over.post Y :=
    NatIso.ofComponents (fun n ↦ b n.unop.len) (by
      intro n m φ
      rcases n with ⟨⟨n⟩⟩
      rcases m with ⟨⟨m⟩⟩
      apply Sigma.hom_ext
      intro i
      simp only [Functor.comp_map, F, R, GeometryRealization.sheafRealization,
        FormalCoproduct.eval_obj_map, Sigma.ι_comp_desc_assoc,
        Function.comp_def, Category.assoc, familyMap]
      rw [hb m]
      rw [← Category.assoc, hb n]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp [U, K', familyMap])
  have hFepi (n : ℕ) : Epi (F.map (μ n)) := by
    apply GeometryRealization.sheafRealization_map_epi (precoverage X)
      ((familyMap G).map (μ n))
    intro j
    have hv := hcov ((M n).pt.obj j).left _ (hcover n j)
    simpa [Presieve.map_ofArrows, G, familyMap, Over.post, eqToHom_map] using hv
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact haff n (fun i ↦ (hbasis n i).1)
  · intro n
    exact ⟨(K _⦋n⦌).I, fun i ↦ ((K _⦋n⦌).obj i).left.obj,
      ι n, hprod n, fun i ↦ (hbasis n i).2⟩
  · let c : Cone (U.properFaceDiagram 0) :=
      ⟨Over.mk (𝟙 W),
        { app := fun a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
          naturality := fun a b f ↦ (Nat.not_lt_zero _ a.unop.property.1).elim }⟩
    have hc : IsLimit c :=
      { lift := fun s ↦ Over.mkIdTerminal.from s.pt
        fac := fun s j ↦ (Nat.not_lt_zero _ j.unop.property.1).elim
        uniq := fun s m hm ↦ Over.mkIdTerminal.hom_ext _ _ }
    let κ : U _⦋0⦌ ⟶ c.pt := Over.mkIdTerminal.from _
    have hκ : ∀ a : SimplicialObject.ProperFaceCategory 0,
        κ ≫ c.π.app (op a) = U.map a.obj.hom.op :=
      fun a ↦ (Nat.not_lt_zero _ a.property.1).elim
    let := hFepi 0
    let := matching_epi_of_properFace K F U (Over.post Y) eb 0
      (M 0) (hlim 0).some (μ 0) (hproj 0) c hc κ hκ
    have h := Over.epi_left_of_epi ((Over.post Y).map κ)
    have h' : Epi (Y.map κ.left) := h
    rw [show κ.left = (U _⦋0⦌).hom from Over.mkIdTerminal_from_left _] at h'
    exact yoneda_epi_of_ulift (topology X) _ h'
  · let c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌) :=
      limit.cone (Discrete.functor (fun _ : Fin 2 ↦ U _⦋0⦌))
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    let κ : U _⦋1⦌ ⟶ c.pt := Fan.IsLimit.lift hc.some (fun i ↦ U.δ i)
    have hκ : ∀ i : Fin 2, κ ≫ c.proj i = U.δ i :=
      fun i ↦ Fan.IsLimit.fac hc.some _ i
    obtain ⟨_, π, hπ, _, hfaces, _⟩ :=
      SimplicialObject.matching_object_proper_faces_one U c hc.some κ hκ
    let := hFepi 1
    let := matching_epi_of_properFace K F U (Over.post Y) eb 1
      (M 1) (hlim 1).some (μ 1) (hproj 1) (Cone.mk c.pt π) hπ.some κ hfaces
    have h := Over.epi_left_of_epi ((Over.post Y).map κ)
    exact ⟨c, hc, κ, hκ,
      yoneda_epi_of_ulift (topology X) κ.left h⟩
  · intro n
    let : Fintype (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (Fintype (Fin (n + 3)))
    let : Fintype (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (DecidableEq (Fin (n + 3)))
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let c : Multifork (SimplicialObject.matchingBoundaryIndex U n) :=
      Multiequalizer.multifork _
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    have hδ : ∀ p : (SimplicialObject.matchingBoundaryShape n).R,
        U.δ p.val.1 ≫ (SimplicialObject.matchingBoundaryIndex U n).fst p =
          U.δ p.val.2 ≫ (SimplicialObject.matchingBoundaryIndex U n).snd p := by
      rintro ⟨⟨a, b⟩, h⟩
      dsimp [SimplicialObject.matchingBoundaryIndex]
      have hb : b = (b.pred (Fin.ne_zero_of_lt h)).succ := (Fin.succ_pred _ _).symm
      have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
          b.pred (Fin.ne_zero_of_lt h) := by
        rw [Fin.le_iff_val_le_val]
        have h' : a.val < b.val := h
        simp only [Fin.val_castLT, Fin.val_pred]
        omega
      have hface := (SimplicialObject.δ_comp_δ U H).symm
      rw [← hb] at hface
      exact hface
    let κ : U _⦋n + 2⦌ ⟶ c.pt :=
      Multifork.IsLimit.lift hc.some (fun i ↦ U.δ i) hδ
    have hκ : ∀ i : Fin (n + 3),
        κ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i :=
      fun i ↦ Multifork.IsLimit.fac hc.some _ hδ i
    obtain ⟨_, π, hπ, _, hfaces, _⟩ :=
      SimplicialObject.matching_object_proper_faces_succ_succ U n c hc.some κ hκ
    let := hFepi (n + 2)
    let := matching_epi_of_properFace K F U (Over.post Y) eb (n + 2)
      (M (n + 2)) (hlim (n + 2)).some (μ (n + 2)) (hproj (n + 2))
      (Cone.mk c.pt π) hπ.some κ hfaces
    have h := Over.epi_left_of_epi ((Over.post Y).map κ)
    exact ⟨c, hc, κ, hκ,
      yoneda_epi_of_ulift (topology X) κ.left h⟩

end AlgebraicGeometry.Scheme.ProEt
