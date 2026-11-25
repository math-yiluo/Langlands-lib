/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant

import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Transport of integral lattices from a slice site

Source: Bhatt--Scholze, Proposition 6.8.4(6), restriction to an etale member.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u vC vD uC uD

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

open Scheme.ProEt

private def etaleSliceFrom (X : Scheme.{u}) (U : X.Etale) :
    U.left.ProEt ⥤ Over ((Scheme.toProEt X).obj U) :=
  sliceFrom X ((Scheme.toProEt X).obj U)

private theorem sliceFrom_continuous (X : Scheme.{u}) (W : X.ProEt) :
    (sliceFrom X W).IsContinuous (topology W.left) ((topology X).over W) := by
  change (sliceEquiv X W).inverse.IsContinuous _ _
  have := sliceDense X W
  infer_instance

private instance etaleSliceFrom_continuous (X : Scheme.{u}) (U : X.Etale) :
    (etaleSliceFrom X U).IsContinuous
      (topology U.left) ((topology X).over ((Scheme.toProEt X).obj U)) :=
  sliceFrom_continuous X ((Scheme.toProEt X).obj U)

private instance etaleSliceFrom_cocontinuous (X : Scheme.{u}) (U : X.Etale) :
    (etaleSliceFrom X U).IsCocontinuous
      (topology U.left) ((topology X).over ((Scheme.toProEt X).obj U)) :=
  sliceFrom_cocont X ((Scheme.toProEt X).obj U)

private instance etaleSliceFrom_equivalence (X : Scheme.{u}) (U : X.Etale) :
    (etaleSliceFrom X U).IsEquivalence :=
  inferInstanceAs (sliceEquiv X ((Scheme.toProEt X).obj U)).inverse.IsEquivalence

private instance etaleSliceFrom_post_continuous (X : Scheme.{u}) (U : X.Etale)
    (V : U.left.ProEt) :
    (Over.post (X := V) (etaleSliceFrom X U)).IsContinuous
      ((topology U.left).over V)
      (((topology X).over ((Scheme.toProEt X).obj U)).over
        ((etaleSliceFrom X U).obj V)) := by
  apply Functor.isContinuous_iff_coverPreserving.mpr
  exact (CoverPreserving.of_isContinuous (etaleSliceFrom X U) _ _).overPost V

private theorem finiteLocallyFree_pushforward
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (K.over V) AddCommGrpCat.{u}]
    [∀ V, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    [∀ V, (Over.post (X := V) G).IsContinuous (K.over V) (J.over (G.obj V))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward.{u} φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    (hp : ∀ (V : D) (W : C) (f : G.obj V ⟶ W),
      Limits.PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u} (R := R.over W)
          (F := Over.post (X := V) G ⋙ Over.map f)
          (((Over.forget V).sheafPushforwardContinuous RingCat.{u} (K.over V) K).map φ)))
    (M : SheafOfModules.{u} R) [h : M.IsFiniteLocallyFree] :
    ((SheafOfModules.pushforward.{u} φ).obj M).IsFiniteLocallyFree := by
  classical
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  have := hq
  let q' : ((SheafOfModules.pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (V : D) (i : q.I), G.obj V ⟶ q.X i
      X := fun i ↦ i.1
      coversTop := fun V ↦ by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj V)))
        intro W g ⟨i, ⟨v⟩⟩
        exact ⟨⟨W, i, v⟩, ⟨𝟙 _⟩⟩
      generators := fun i ↦ by
        have := hp i.1 (q.X i.2.1) i.2.2
        exact (q.generators i.2.1).map
          (SheafOfModules.pushforward.{u}
            (F := Over.post (X := i.1) G ⋙ Over.map i.2.2)
            (((Over.forget i.1).sheafPushforwardContinuous RingCat (K.over i.1) K).map φ))
          ((SheafOfModules.pushforward (𝟙 (S.over i.1))).mapIso η).symm }
  have : q'.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [q']
    infer_instance
  apply SheafOfModules.IsFiniteLocallyFree.mk
  refine ⟨q'.shrink, inferInstance, ?_⟩
  constructor
  intro i
  let j := i.2.choose
  have := hp j.1 (q.X j.2.1) j.2.2
  have := hf.isFiniteType j.2.1
  change (q'.generators j).IsFiniteType
  dsimp [q']
  infer_instance

private noncomputable def pushforwardSheafificationIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}] [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K] [G.IsEquivalence]
    (R : Sheaf K RingCat.{u + 1}) (P : PresheafOfModules.{u + 1} R.obj) :
    (PresheafOfModules.sheafification (R :=
      (G.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) (𝟙 _)).obj
        ((PresheafOfModules.pushforward (F := G) (𝟙 (G.op ⋙ R.obj))).obj P) ≅
      (SheafOfModules.pushforward (F := G) (S :=
        (G.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) (𝟙 _)).obj
          ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P) := by
  let S := (G.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R
  let T := (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P
  let Q := (PresheafOfModules.pushforward (F := G) (𝟙 (G.op ⋙ R.obj))).obj P
  let N := (SheafOfModules.pushforward (F := G) (S := S) (𝟙 S)).obj T
  let g : Q ⟶ N.val :=
    (PresheafOfModules.pushforward (F := G) (𝟙 (G.op ⋙ R.obj))).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P)
  let f : (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj Q ⟶ N :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm g
  have hf : (SheafOfModules.toSheaf S).map f =
      (G.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1} J K).hom.app
        P.presheaf := by
    dsimp only [f]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply Sheaf.hom_ext
    rw [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
    rfl
  have : IsIso ((SheafOfModules.toSheaf S).map f) := by
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf S)
  exact asIso f

/-- A lattice on the localized site transports to a lattice on the cover member's
small site, with the identity coefficient identification on continuous functions.
Source: Bhatt--Scholze, Proposition 6.8.4(6), restriction to a covering member;
Stacks Project, Tags 098K, 094T and 0951, localization of the pro-etale site.
(auxiliary; not a blueprint node)

Proof: an object over the etale member U is a weakly etale arrow V → U;
composition with U → X identifies its small pro-etale site with the slice of
X_proet over U. The inverse sends an object of the slice to its arrow to U;
weak etaleness follows by cancellation. Both functors preserve and reflect covers,
since the fpqc covering criterion uses only the underlying scheme arrows. Restrict
the integral module along this equivalence. Continuous coefficients are unchanged on
each object and morphism, so this is a module over the member's integral coefficient
sheaf. Transport its finite free trivializations to obtain finite local freeness.
The equivalence preserves sheafification and sectionwise tensor products; therefore
change of rings commutes with it. Transport the pair's rationalization isomorphism
and forget to module presheaves. The rational coefficient comparison is identity
on continuous functions, exactly the displayed coefficient identification. -/
theorem lisse_lattice_of_slice (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (U : X.Etale)
    (P : IntegralLatticePair (lisseIntegerToField l E X) L ((Scheme.toProEt X).obj U)) :
    ∃ M : ringedSiteModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology U.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (lisseIntegerSheaf l E U.left)),
      M.IsFiniteLocallyFree ∧
      Nonempty ((SheafOfModules.changeOfRings
        (lisseIntegerToField l E U.left) M).val ≅
        (PresheafOfModules.pushforward
          (lisseEtaleCoefficientIdentification l E U.hom)).obj L.val) := by
  let W := (Scheme.toProEt X).obj U
  let G := etaleSliceFrom X U
  let R := (sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E X)
  let R' := (sheafCompose (topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E U.left)
  have hcoeff : R' = (G.sheafPushforwardContinuous RingCat.{u + 1}
      (topology U.left) ((topology X).over W)).obj (R.over W) := by
    rfl
  let a : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (topology U.left) ((topology X).over W)).obj (R.over W) := eqToHom hcoeff
  let M := (SheafOfModules.pushforward.{u + 1} a).obj P.module
  have hP := P.locallyFree
  have hfree : M.IsFiniteLocallyFree := by
    apply finiteLocallyFree_pushforward G a (Iso.refl _) ?_ P.module
    intro V T f
    let G' := Over.post (X := V) G ⋙ Over.map f
    have : G'.IsContinuous ((topology U.left).over V) (((topology X).over W).over T) :=
      Functor.isContinuous_comp _ _ _ (((topology X).over W).over _) _
    have : G'.IsCocontinuous ((topology U.left).over V)
        (((topology X).over W).over T) :=
      isCocontinuous_comp _ _ _ (((topology X).over W).over _)
    let b : R'.over V ⟶
        (G'.sheafPushforwardContinuous RingCat.{u + 1}
          ((topology U.left).over V) (((topology X).over W).over T)).obj ((R.over W).over T) :=
      ((Over.forget V).sheafPushforwardContinuous RingCat.{u + 1}
        ((topology U.left).over V) (topology U.left)).map a
    have : (SheafOfModules.pushforward.{u + 1} b).IsLeftAdjoint :=
      SheafOfModules.isLeftAdjoint_pushforward_of_isIso b
    infer_instance
  let S := (sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)
  let S' := (sheafCompose (topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E U.left)
  let b : S' ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (topology U.left) ((topology X).over W)).obj (S.over W) := 𝟙 _
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (latticeScalarMap (lisseIntegerToField l E X) W) P.module
  let T' := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
    (lisseIntegerToField l E U.left) M
  let t : T' ≅ (PresheafOfModules.pushforward b.hom).obj T :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro V V' f
      change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
        (lisseIntegerToField l E U.left) M f =
          SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap (lisseIntegerToField l E X) W) P.module (G.op.map f)
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      exact (Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
          (lisseIntegerToField l E U.left) M f) 1 m).trans
          (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap (lisseIntegerToField l E X) W) P.module (G.op.map f)) 1 m).symm)
  let e : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (lisseIntegerToField l E U.left) M ≅
      (SheafOfModules.pushforward b).obj (L.over W) :=
    (PresheafOfModules.sheafification (R := S') (𝟙 S'.obj)).mapIso t ≪≫
      pushforwardSheafificationIso (topology U.left) ((topology X).over W) G
        (S.over W) T ≪≫ (SheafOfModules.pushforward b).mapIso P.rationalization
  refine ⟨M, hfree, ⟨?_⟩⟩
  exact (SheafOfModules.forget S').mapIso e

end AlgebraicGeometry.ProEtale
