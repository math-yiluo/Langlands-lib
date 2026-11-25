/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-! # Abelian specialization with independently sized coefficients

## References

* Stacks Project, Tag 09AC, first reduction, and Tag 01IH for closed immersions into affine schemes
* Stacks Project, Tag 09AC, with the fully faithful adjunction of Tag 09BK
* Stacks Project, Tag 09BL, (2), and Tag 09AC, localization and unit identification
* Stacks Project, Tag 09AC, and Tag 09BL (1), (2)
-/

@[expose] public section
set_option autoImplicit false
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
namespace AlgebraicGeometry.Scheme
namespace IndependentSpecialization

private instance independentAbSheafify {C : Type (t + 1)} [Category.{t} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} C := essentiallySmallSelf _
  let : HasSheafify ((equivSmallModel.{max u (t + 1)} C).inverse.inducedTopology J)
      AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J _

private instance independentTypeSheafify {C : Type (t + 1)} [Category.{t} C]
    (J : GrothendieckTopology C) : HasSheafify J (Type (max u (t + 1))) := by
  let : EssentiallySmall.{max u (t + 1)} C := essentiallySmallSelf _
  exact hasSheafifyEssentiallySmallSite J _

private instance independentTypeW {C : Type (t + 1)} [Category.{t} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective (Type (max u (t + 1))) := by
  let : EssentiallySmall.{max u (t + 1)} C := essentiallySmallSelf _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (A := Type (max u (t + 1))) J

private instance independentKan {X Y : Scheme.{t}} (f : X ⟶ Y)
    (D : Type v) [Category.{w} D] [HasColimitsOfSize.{t + 1, t + 1} D]
    (F : Y.ProEtᵒᵖ ⥤ D) : (proEtaleBaseChange f).op.HasLeftKanExtension F := by
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : LocallySmall.{t + 1} X.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  have : ∀ V : X.ProEtᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange f).op V) D := fun _ ↦
    hasColimitsOfShape_of_essentiallySmall.{t + 1} _ _
  infer_instance

private noncomputable abbrev proEtaleSheafDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y)
    (D : Type v) [Category.{w} D] :=
  (proEtaleBaseChange f).sheafPushforwardContinuous D (ProEt.topology Y) (ProEt.topology X)

private noncomputable abbrev proEtaleSheafAdjunction {X Y : Scheme.{t}} (f : X ⟶ Y)
    (D : Type v) [Category.{w} D] [HasColimitsOfSize.{t + 1, t + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange f) D (ProEt.topology Y) (ProEt.topology X)

private noncomputable abbrev localizationRestriction (D : Type v) [Category.{w} D]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (hf : WeaklyEtale f) :=
  (MorphismProperty.Over.map ⊤ hf).sheafPushforwardContinuous D
    (ProEt.topology X) (ProEt.topology Y)

private noncomputable abbrev localizationRestrictionLowerStarAdjunction
    (D : Type v) [Category.{w} D] {X Y : Scheme.{t}} (f : X ⟶ Y) (hf : WeaklyEtale f) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f hf
    _root_.trivial).sheafPushforwardContinuous
      (ProEt.topology X) (ProEt.topology Y) (E := D)

private instance abSmallColimits :
    HasColimitsOfSize.{t + 1, t + 1} AddCommGrpCat.{max u (t + 1)} :=
  hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _

-- A section of a surjective affine cover is obtained by lifting the Yoneda identity.
private theorem split_affine_proetale_cover {X : Scheme.{t}} (V W : X.ProEt)
    [IsAffine V.left] [IsAffine W.left]
    (hV : ∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (q : W ⟶ V) [Surjective q.left] : ∃ s : V ⟶ W, s ≫ q = 𝟙 V := by
  let J := ProEt.topology X
  let H := J.uliftYoneda.{max u (t + 1)}
  have hcover : Sieve.generate (Presieve.singleton q) ∈ J V := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton q.left ∈ proetalePrecoverage V.left
    exact Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale q.left)
  have hepi : Epi (H.map q) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton q) hcover |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨s, hs⟩ := hV _ _ (H.map q) hepi (ULift.up (𝟙 V))
  exact ⟨s.down, congrArg ULift.down hs⟩

-- Use the kernel quotient map explicitly; no arbitrary quotient presentation is chosen.
private theorem quotient_specialization {T Y : Scheme.{t}} [IsAffine Y]
    (f : T ⟶ Y) [IsClosedImmersion f]
    (hspec : ∀ x : Y, ∃ z : T, Specializes x (f z)) :
    ∀ x : Spec Γ(Y, ⊤), ∃ z : ↥(pullback (𝟙 (Spec Γ(Y, ⊤)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))))),
      Specializes x ((pullback.fst (𝟙 (Spec Γ(Y, ⊤)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))))) z) := by
  have hsurj : Function.Surjective f.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  let e := f.appTop.hom.quotientKerEquivOfSurjective hsurj
  let g : T ⟶ Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) :=
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
  have he : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom)) ≫
    CommRingCat.ofHom e.toRingHom = f.appTop := by
    ext a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj a
  have hg : g ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))) = f ≫ Y.isoSpec.hom := by
    change (T.toSpecΓ ≫ Spec.map _) ≫ Spec.map _ = f ≫ Y.toSpecΓ
    rw [Category.assoc, ← Spec.map_comp, he]
    exact (Scheme.toSpecΓ_naturality f).symm
  intro x
  obtain ⟨z, hz⟩ := hspec (Y.isoSpec.inv x)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom)))
  let l : Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) ⟶
    pullback (𝟙 (Spec Γ(Y, ⊤))) j := pullback.lift j (𝟙 _) (by simp)
  refine ⟨l (g z), ?_⟩
  have hz' := hz.map Y.isoSpec.hom.continuous
  have hx : Y.isoSpec.hom (Y.isoSpec.inv x) = x :=
    congrArg (fun k : Spec Γ(Y, ⊤) ⟶ Spec Γ(Y, ⊤) ↦ k x)
    Y.isoSpec.inv_hom_id
  have hgz : Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))) (g z) =
    Y.isoSpec.hom (f z) := congrArg (fun k : T ⟶ _ ↦ k z) hg
  rw [hx] at hz'
  have hlhom : l ≫ pullback.fst (𝟙 _) j = j := pullback.lift_fst _ _ _
  have hl : (pullback.fst (𝟙 _) j) (l (g z)) = j (g z) :=
    congrArg (fun k : Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) ⟶
      Spec Γ(Y, ⊤) ↦ k (g z)) hlhom
  change Specializes (x : Spec Γ(Y, ⊤)) ((pullback.fst (𝟙 _) j) (l (g z)))
  rw [hl, hgz]
  exact hz'

/-- Affine coordinates transport projectivity of evaluation and the closed-fibre
specialization condition. The ideal is the actual kernel of the global-sections
map of the closed base change. -/
private theorem specialization_affine_coordinates
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z)) :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) ∧
    (∀ x : B.left, ∃ z : ↥(pullback B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      Specializes x ((pullback.fst B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) := by
  dsimp only
  constructor
  · let B := AffineProEt.ofEtale (𝟙 (Spec Γ(V.left, ⊤)))
    intro P Q φ hφ y
    have hlocal : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi φ).mpr hφ
    obtain ⟨W, q, hq, z, hz⟩ :=
      (AffineProEt.isLocallySurjective_iff_of_isSheaf φ.hom P.property Q.property).mp hlocal B y
    let w : W.left ⟶ V.left := W.hom ≫ V.left.isoSpec.inv
    have hW : WeaklyEtale W.hom := proAffineEtale_le_weaklyEtale _ W.prop
    have hw : WeaklyEtale w := by dsimp [w]; infer_instance
    let W' : X.ProEt := ProEt.mk (w ≫ V.hom)
    let q' : W' ⟶ V := MorphismProperty.Over.homMk w rfl
    have hqleft : q.left = W.hom := by
      have h := MorphismProperty.Over.w q
      change q.left ≫ 𝟙 _ = W.hom at h
      simpa only [Category.comp_id] using h
    have hW' : IsAffine W'.left := inferInstanceAs (IsAffine W.left)
    have hq' : Surjective q'.left := by
      change Surjective (W.hom ≫ V.left.isoSpec.inv)
      rw [← hqleft]
      infer_instance
    obtain ⟨s, hs⟩ := split_affine_proetale_cover V W' hweak q'
    have hsleft : s.left ≫ w = 𝟙 V.left :=
      congrArg (fun k : V ⟶ V ↦ k.left) hs
    let t : B ⟶ W := MorphismProperty.Over.homMk (V.left.isoSpec.inv ≫ s.left) (by
      apply (cancel_mono V.left.isoSpec.inv).mp
      change (V.left.isoSpec.inv ≫ s.left) ≫ W.hom ≫ V.left.isoSpec.inv =
        (𝟙 _) ≫ V.left.isoSpec.inv
      change V.left.isoSpec.inv ≫ (s.left ≫ w) = (𝟙 _) ≫ V.left.isoSpec.inv
      rw [hsleft, Category.comp_id, Category.id_comp])
    have ht : t ≫ q = 𝟙 B := by
      apply MorphismProperty.Over.Hom.ext
      change (V.left.isoSpec.inv ≫ s.left) ≫ q.left = 𝟙 _
      rw [hqleft]
      exact MorphismProperty.Over.w t
    refine ⟨P.obj.map t.op z, ?_⟩
    rw [NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, ← op_comp, ht]
    exact Q.obj.map_id_apply _ y
  · exact quotient_specialization (Y := V.left) (pullback.fst V.hom i) hspec

namespace AffineProEt

open AlgebraicGeometry.Scheme.AffineProEt

private abbrev toProEt (S : Scheme.{t}) := AlgebraicGeometry.Scheme.AffineProEt.toProEt S

private noncomputable abbrev precoverage {S : Scheme.{t}} : Precoverage S.AffineProEt :=
  AlgebraicGeometry.Scheme.AffineProEt.precoverage

private theorem precoverage_cover {S : Scheme.{t}} {V : S.AffineProEt}
    {R : Presieve V} (hR : R ∈ precoverage V) :
    Sieve.generate R ∈ topology S V := by
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.generate_map_eq_functorPushforward]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [precoverage, AlgebraicGeometry.Scheme.AffineProEt.precoverage,
    ProEt.precoverage, Precoverage.mem_comap_iff,
    Presieve.map_comp, Functor.comp_obj] using hR

private theorem finite_cover_precoverage {S : Scheme.{t}} {V : S.AffineProEt}
    {ι : Type t} [Finite ι] (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
    (hs : ∀ x : V.left, ∃ j, x ∈ Set.range (f j).left.base) :
    Presieve.ofArrows U f ∈ precoverage V := by
  let E : V.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    ⟨⟨ι, fun j ↦ (U j).left, fun j ↦ (f j).left⟩,
      (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hs, fun _ ↦ inferInstance⟩⟩
  have : Finite E.I₀ := inferInstanceAs (Finite ι)
  have : ∀ j, QuasiCompact (E.f j) := fun j ↦
    inferInstanceAs (QuasiCompact (f j).left)
  have hqc : QuasiCompactCover E.toPreZeroHypercover := QuasiCompactCover.of_finite
  have hE : E.presieve₀ ∈ Scheme.proetalePrecoverage V.left :=
    ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, E.mem₀⟩
  simpa only [precoverage, AlgebraicGeometry.Scheme.AffineProEt.precoverage,
    Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Functor.comp_obj, Functor.comp_map, toProEt_obj_left, toProEt_map,
    ProEt.forget_obj, ProEt.forget_map, Over.forget_obj, Over.forget_map, E,
    PreZeroHypercover.presieve₀, ProEt.forget, toProEt,
    MorphismProperty.Comma.forget, MorphismProperty.Over.changeProp,
    MorphismProperty.Comma.changeProp] using hE

private noncomputable def sigmaCover_colimit {S : Scheme.{t}} {V : S.AffineProEt}
    {ι : Type t} [Finite ι] (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
    [(topology S).Subcanonical] :
    IsColimit (Cofan.mk (sigmaCover U f) (sigmaCoverι U f)) := by
  classical
  apply Cofan.IsColimit.ofBijective
  intro Y
  let H := (topology S).uliftYoneda.{max u (t + 1)}.obj Y
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h : (ULift.up a : H.obj.obj (op (sigmaCover U f))) = ULift.up b :=
      sigmaCover_ext U f H.property (fun j ↦ congrArg ULift.up (congrFun hab j))
    exact congrArg ULift.down h
  · intro a
    obtain ⟨b, hb⟩ := exists_sigmaCover_glue U f H.property (fun j ↦ ULift.up (a j))
    exact ⟨b.down, funext (fun j ↦ congrArg ULift.down (hb j))⟩

private theorem leftAdjoint_sigmaCover_glue {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    {V : S.AffineProEt} {ι : Type t} [Finite ι]
    (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
    (H : Sheaf (topology T) (Type (max u (t + 1)))) (x : ∀ j, H.obj.obj (op (v.obj (U j)))) :
    ∃ z : H.obj.obj (op (v.obj (sigmaCover U f))),
      ∀ j, H.obj.map (v.map (sigmaCoverι U f j)).op z = x j := by
  classical
  let B := fun j ↦ v.obj (U j)
  let g := fun j ↦ v.map (f j)
  obtain ⟨t, ht⟩ := exists_sigmaCover_glue B g H.property x
  let hv := adj.leftAdjoint_preservesColimits
  let hc := (Cofan.isColimitMapCoconeEquiv v U (Cofan.mk _ (sigmaCoverι U f)))
    (isColimitOfPreserves v (sigmaCover_colimit.{t, u} U f))
  let c := Cofan.mk (sigmaCover B g) (sigmaCoverι B g)
  let a := hc.desc c
  refine ⟨H.obj.map a.op t, ?_⟩
  intro j
  have h := hc.fac c ⟨j⟩
  change v.map (sigmaCoverι U f j) ≫ a = sigmaCoverι B g j at h
  calc
    _ = H.obj.map (a.op ≫ (v.map (sigmaCoverι U f j)).op) t :=
      (H.obj.map_comp_apply a.op (v.map (sigmaCoverι U f j)).op t).symm
    _ = H.obj.map (sigmaCoverι B g j).op t :=
      congrArg (fun b ↦ H.obj.map b.op t) h
    _ = x j := ht j

private theorem cover_split {S : Scheme.{t}} [(topology S).Subcanonical]
    (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V)))
    {W : S.AffineProEt} (q : W ⟶ V) (hq : Surjective q.left) :
    ∃ σ : V ⟶ W, σ ≫ q = 𝟙 V := by
  let J := topology S
  let H := J.uliftYoneda.{max u (t + 1)}
  have hcover := generate_singleton_mem_topology q hq
  have hepi : Epi (H.map q) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton q) hcover |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨s, hs⟩ := hV _ _ (H.map q) hepi (ULift.up (𝟙 V))
  exact ⟨s.down, congrArg ULift.down hs⟩

private theorem precomposition_unit_injective {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt)
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) (Type (max u (t + 1)))) (V : S.AffineProEt) :
    Function.Injective ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  intro p q hpq
  obtain ⟨ι, _, U, f, hf, hs⟩ := exists_finite_jointly_surjective_of_mem_topology
    (Presheaf.equalizerSieve_mem (topology S) (toSheafify (topology S) (v.op ⋙ H.obj))
      p q hpq)
  have hcover := precoverage_cover (hcov V _ (finite_cover_precoverage U f hs))
  rw [Presieve.map_ofArrows] at hcover
  have hsep := ((isSheaf_iff_isSheaf_of_type _ H.obj).mp H.property).isSheafFor
    _ hcover |>.isSeparatedFor
  apply hsep.ext
  rintro Y g ⟨j⟩
  exact hf j

private theorem precomposition_unit_surjective {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (H : Sheaf (topology T) (Type (max u (t + 1)))) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V))) :
    Function.Surjective ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  classical
  let P := v.op ⋙ H.obj
  let G := (presheafToSheaf (topology S) (Type (max u (t + 1)))).obj P
  let η := toSheafify (topology S) P
  intro s
  obtain ⟨ι, _, U, f, hf, hs⟩ := exists_finite_jointly_surjective_of_mem_topology
    (Presheaf.imageSieve_mem (topology S) η (U := op V) s)
  choose x hx using hf
  obtain ⟨z, hz⟩ := leftAdjoint_sigmaCover_glue v adj U f H x
  obtain ⟨σ, hσ⟩ := cover_split V hV (sigmaCoverπ U f) (surjective_sigmaCoverπ U f hs)
  have heq : η.app (op (sigmaCover U f)) z = G.obj.map (sigmaCoverπ U f).op s := by
    apply sigmaCover_ext U f G.property
    intro j
    rw [← η.naturality_apply]
    change η.app (op (U j)) (H.obj.map (v.map (sigmaCoverι U f j)).op z) = _
    rw [hz j, hx j]
    exact ((G.obj.map_comp_apply (sigmaCoverπ U f).op (sigmaCoverι U f j).op s).symm.trans
      (congrArg (fun a ↦ G.obj.map a.op s) (sigmaCoverι_π U f j))).symm
  refine ⟨P.map σ.op z, ?_⟩
  change η.app (op V) (P.map σ.op z) = s
  rw [η.naturality_apply, heq]
  exact (G.obj.map_comp_apply (sigmaCoverπ U f).op σ.op s).symm.trans
    ((congrArg (fun a ↦ G.obj.map a.op s) hσ).trans (G.obj.map_id_apply _ s))

/-- The affine closed-site counit is invertible at a weakly contractible object
whose points specialize into the closed fibre. -/
private theorem isIso_closedSiteCounit_of_specialization
    (A : Type t) [CommRing A] (I : Ideal A)
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (V : (Spec (.of A)).AffineProEt)
    (hweak : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      Specializes x ((pullback.fst V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) :
    IsIso (adj.counit.app V) := by
  obtain ⟨_, _, hfull, hfaith, _, _, _, _⟩ := affine_closed_site_functor_properties A I
  have : (closedSiteLift A I).Full := hfull
  have : (closedSiteLift A I).Faithful := hfaith
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  let p := adj.counit.app V
  have hp : IsIso (r.map p) := inferInstance
  have hpi : IsIso (r.map p).left := inferInstance
  have hs : Surjective p.left := by
    constructor
    intro x
    obtain ⟨z, hxz⟩ := hspec x
    obtain ⟨w, hw⟩ := (asIso (r.map p).left).hom.surjective z
    have hfst : (r.map p).left ≫ pullback.fst V.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
        pullback.fst (v.obj (r.obj V)).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p.left := by
      exact pullback.lift_fst _ _ _
    have hw' : p.left ((pullback.fst (v.obj (r.obj V)).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) w) =
        (pullback.fst V.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z := by
      exact (congrArg (fun f : _ ⟶ V.left ↦ f w) hfst).symm.trans
        (congrArg (fun z ↦ (pullback.fst V.hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z) hw)
    obtain ⟨t, _, ht⟩ := Flat.generalizingMap p.left (hw' ▸ hxz)
    exact ⟨t, ht⟩
  let : (topology (Spec (.of A))).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt (Spec (.of A)))
      (topology (Spec (.of A))) (ProEt.topology (Spec (.of A)))
  obtain ⟨s, hs⟩ := cover_split V hweak p hs
  have hrs : r.map s = inv (r.map p) := by
    apply (cancel_mono (r.map p)).mp
    rw [← r.map_comp, hs, r.map_id, IsIso.inv_hom_id]
  have hps : p ≫ s = 𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    change adj.unit.app (r.obj V) ≫ r.map (p ≫ s) =
      adj.unit.app (r.obj V) ≫ r.map (𝟙 _)
    have hmap : r.map (p ≫ s) = r.map (𝟙 _) := by
      rw [r.map_comp, hrs, IsIso.hom_inv_id, r.map_id]
    exact congrArg (fun f ↦ adj.unit.app (r.obj V) ≫ f) hmap
  exact ⟨⟨s, hps, hs⟩⟩

private theorem projectiveEvaluation_of_iso {S : Scheme.{t}} {B C : S.AffineProEt}
    (e : B ≅ C)
    (hB : ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) :
    ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op C)) := by
  intro P Q φ hφ y
  obtain ⟨x, hx⟩ := hB P Q φ hφ (Q.obj.map e.hom.op y)
  refine ⟨P.obj.map e.inv.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp]
  simp

private theorem cover_split_of_cover {S : Scheme.{t}} [(topology S).Subcanonical]
    (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    {W : S.AffineProEt} (q : W ⟶ V)
    (hq : Sieve.generate (Presieve.singleton q) ∈ topology S V) :
    ∃ σ : V ⟶ W, σ ≫ q = 𝟙 V := by
  let J := topology S
  let H := J.uliftYoneda.{max u (t + 1)}
  have hepi : Epi (H.map q) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton q) hq |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨σ, hσ⟩ := hV _ _ (H.map q) hepi (ULift.up (𝟙 V))
  exact ⟨σ.down, congrArg ULift.down hσ⟩

private theorem projectiveEvaluation_closedBaseChange
    (A : Type t) [CommRing A] (I : Ideal A)
    (B : (Spec (.of A)).AffineProEt)
    (hB : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B)))
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (hε : IsIso (adj.counit.app B)) :
    ∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective
        (φ.hom.app (op ((closedSiteBaseChange A I).obj B))) := by
  obtain ⟨_, _, hfull, hfaith, _, _, hcov, _⟩ := affine_closed_site_functor_properties A I
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  have : v.Full := hfull
  have : v.Faithful := hfaith
  have : IsIso (adj.counit.app B) := hε
  have : (topology (Spec (.of A))).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt (Spec (.of A)))
      (topology (Spec (.of A))) (ProEt.topology (Spec (.of A)))
  have hvB := projectiveEvaluation_of_iso (asIso (adj.counit.app B)).symm hB
  intro P Q φ hφ y
  have : Epi φ := hφ
  have hlocal : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi φ).mpr hφ
  obtain ⟨W, q, hq, x, hx⟩ := (isLocallySurjective_iff φ).mp hlocal (r.obj B) y
  have hpre : Presieve.singleton q ∈ precoverage (r.obj B) := by
    have h := finite_cover_precoverage (fun _ : PUnit.{t + 1} ↦ W)
      (fun _ ↦ q) (fun z ↦ ⟨PUnit.unit, hq.surj z⟩)
    simpa only [Presieve.ofArrows_pUnit] using h
  have hcover : Sieve.generate (Presieve.singleton (v.map q)) ∈ topology _ (v.obj (r.obj B)) := by
    have h := precoverage_cover (hcov (r.obj B) _ hpre)
    simpa only [Presieve.map_singleton] using h
  obtain ⟨t, ht⟩ := cover_split_of_cover (v.obj (r.obj B)) hvB (v.map q) hcover
  let σ : r.obj B ⟶ W := v.preimage t
  have hσ : σ ≫ q = 𝟙 _ := by
    apply v.map_injective
    dsimp only [σ]
    rw [v.map_comp, v.map_preimage, v.map_id]
    exact ht
  refine ⟨P.obj.map σ.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp, hσ]
  exact Q.obj.map_id_apply _ y

private theorem isIso_precomposition_toSheafify {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) AddCommGrpCat.{max u (t + 1)}) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V))) :
    IsIso ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  let H₀ := (sheafCompose (topology T) (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj H
  have hbij : Function.Bijective
      ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) :=
    ⟨precomposition_unit_injective v hcov H₀ V,
      precomposition_unit_surjective v adj H₀ V hV⟩
  have : PreservesFilteredColimitsOfSize.{t + 1, t + 1}
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t + 1, max u (t + 1)} _
  have : (topology S).PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let e := sheafifyComposeIso (topology S)
    (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) (v.op ⋙ H.obj)
  have hfac := congrArg (fun φ ↦ φ.app (op V))
    (sheafComposeIso_hom_fac (topology S)
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) (v.op ⋙ H.obj))
  have : IsIso ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) :=
    (isIso_iff_bijective _).mpr hbij
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (ConcreteCategory.hom
    ((Functor.whiskerRight (toSheafify (topology S) (v.op ⋙ H.obj))
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).app (op V)))
  have he := congrArg ConcreteCategory.hom hfac
  have hc : Function.Bijective (ConcreteCategory.hom
      (e.hom.app (op V))) := (isIso_iff_bijective _).mp inferInstance
  rw [← he]
  exact hc.comp hbij

private theorem isIso_affineUnit_sections
    (A : Type t) [CommRing A] (I : Ideal A)
    (B : (Spec (.of A)).AffineProEt)
    (hB : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B)))
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (hε : IsIso (adj.counit.app B))
    (F : Sheaf (ProEt.topology (Spec (.of A))) AddCommGrpCat.{max u (t + 1)}) :
    IsIso (((proEtaleSheafAdjunction
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        AddCommGrpCat.{max u (t + 1)}).unit.app F).hom.app
          (op ((toProEt (Spec (.of A))).obj B))) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  obtain ⟨_, _, _, _, hco, _, hcov, _⟩ := affine_closed_site_functor_properties A I
  have : v.IsCocontinuous (topology Z) (topology X) := hco
  have : r.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  have : (topology Z).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt Z)
      (topology Z) (ProEt.topology Z)
  let D := AddCommGrpCat.{max u (t + 1)}
  let RX := (toProEt X).sheafPushforwardContinuous D (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous D (topology Z) (ProEt.topology Z)
  let L := sheafToPresheaf (topology X) D ⋙
    (Functor.whiskeringLeft _ _ D).obj v.op ⋙ presheafToSheaf (topology Z) D
  let R := r.sheafPushforwardContinuous D (topology X) (topology Z)
  let a : L ⊣ R :=
    ((adj.op.whiskerLeft D).comp (sheafificationAdjunction (topology Z) D)).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf (topology X) D))
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  have t : r ⋙ toProEt Z ≅ toProEt X ⋙ proEtaleBaseChange i := Iso.refl _
  have : (toProEt X ⋙ proEtaleBaseChange i).IsContinuous
      (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (ProEt.topology X) (ProEt.topology Z)
  have : (r ⋙ toProEt Z).IsContinuous (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (topology Z) (ProEt.topology Z)
  let beta : proEtaleSheafDirectImage i D ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X) (proEtaleBaseChange i)
      D (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm D (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp r (toProEt Z) D
      (topology X) (topology Z) (ProEt.topology Z)).symm
  let alpha := ((mateEquiv (proEtaleSheafAdjunction i D) a).symm beta.hom)
  have : IsIso alpha := isIso_inverseMate_of_equivalences (proEtaleSheafAdjunction i D) a beta
  have hp := projectiveEvaluation_closedBaseChange A I B hB adj hε
  have hη : IsIso ((a.unit.app (RX.obj F)).hom.app (op B)) := by
    have heq : (a.unit.app (RX.obj F)).hom.app (op B) =
        (RX.obj F).obj.map (adj.counit.app B).op ≫
          (toSheafify (topology Z) (v.op ⋙ (RX.obj F).obj)).app (op (r.obj B)) := by
      dsimp [a]
      rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Adjunction.comp_unit_app, sheafificationAdjunction_unit_app,
        Functor.comp_map, Iso.refl_hom, NatTrans.id_app]
      rfl
    rw [heq]
    have : IsIso (adj.counit.app B) := hε
    have := isIso_precomposition_toSheafify v adj hcov (RX.obj F) (r.obj B) hp
    infer_instance
  have hu := unit_mateEquiv_symm (proEtaleSheafAdjunction i D) a beta.hom F
  have hu' := congrArg (fun f ↦ f.hom.app (op B)) hu
  change ((proEtaleSheafAdjunction i D).unit.app F).hom.app (op ((toProEt X).obj B)) ≫
    (beta.hom.app _).hom.app (op B) =
      (a.unit.app (RX.obj F)).hom.app (op B) ≫
        (R.map (alpha.app F)).hom.app (op B) at hu'
  have : IsIso (((proEtaleSheafAdjunction i D).unit.app F).hom.app
      (op ((toProEt X).obj B)) ≫ (beta.hom.app _).hom.app (op B)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.hom.app _).hom.app (op B))

end AffineProEt

section Localization
universe u'
open AlgebraicGeometry MorphismProperty AlgebraicGeometry.ProEtale CategoryTheory.Category
variable (A : Type u') [Category.{max u (t + 1)} A]

variable {U' U Z' Z : Scheme.{t}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

variable [WeaklyEtale j] [WeaklyEtale j']

local instance : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
 instIsContinuousOverSchemeWeaklyEtaleTopMorphismPropertyCompPullbackMapTopology_weilConjectures.{t}
    (g' := g') (j' := j')

local instance : (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
 instIsContinuousOverSchemeWeaklyEtaleTopMorphismPropertyCompMapPullbackTopology_weilConjectures.{t}
    (j := j) (g'' := g'')

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
private noncomputable def localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    proEtaleSheafDirectImage g'' A ⋙ localizationRestriction A j inferInstance ⟶
      localizationRestriction A j' inferInstance ⋙ proEtaleSheafDirectImage g' A :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

/-- If the square is cartesian, the base change map on restrictions is an isomorphism, being
induced by an isomorphism of site functors. -/
private lemma isIso_localRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (localRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

private noncomputable def siteMate (sq : CommSq g' j' j g'') :=
  (mateEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j) trivial)
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
      (inferInstance : WeaklyEtale j') trivial)
    (TwoSquare.mk _ _ _ _ (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') sq)))
private theorem siteMate_eq (sq : CommSq g' j' j g'') :
    siteMate sq = (MorphismProperty.Over.pullbackComp g' j).inv ≫
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) sq.w).hom ≫
      (MorphismProperty.Over.pullbackComp j' g'').hom := by
  ext b
  dsimp [siteMate, mateEquiv]
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

private lemma isIso_mate_localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    IsIso ((mateEquiv
      (localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  have hs : IsIso (siteMate sq) := by rw [siteMate_eq]; infer_instance
  have h (F : Sheaf (ProEt.topology U') A) (b : Z.ProEt) :
      ((mateEquiv
        (localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app
          (op b) = F.obj.map ((siteMate sq).app b).op := by
    simp only [Functor.comp_obj, mateEquiv, localizationRestrictionLowerStarAdjunction,
      Adjunction.sheafPushforwardContinuous, Functor.id_obj,
      localRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
      ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
      Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app,
      Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit_app,
      Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuous_obj_obj_map]
    change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = _
    simp only [← Functor.map_comp]
    dsimp [siteMate, mateEquiv]
    simp only [id_comp, comp_id, ← Functor.map_comp, ← op_comp]
    simp only [Functor.map_comp, op_comp, Category.assoc]
  have hF (F : Sheaf (ProEt.topology U') A) : IsIso ((mateEquiv
      (localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F) := by
    have hB : ∀ b : Z.ProEtᵒᵖ, IsIso (((mateEquiv
        (localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app b) :=
      fun b ↦ by
        have hi : IsIso (F.obj.map ((siteMate sq).app b.unop).op) := inferInstance
        exact (h F b.unop).symm ▸ hi
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ A)).mp
    change IsIso (((mateEquiv
      (localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

variable [HasColimitsOfSize.{t + 1, t + 1} A]
  [∀ S : Scheme.{t}, HasWeakSheafify (ProEt.topology S) A]

private theorem isIso_inverseMate_localRestrictionBaseChange (sq : CommSq g' j' j g'') :
    IsIso (((mateEquiv (proEtaleSheafAdjunction g'' A)
      (proEtaleSheafAdjunction g' A)).symm
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let aj := localizationRestrictionLowerStarAdjunction A j inferInstance
  let ab := localizationRestrictionLowerStarAdjunction A j' inferInstance
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)
  let alpha := (mateEquiv ai ak).symm beta
  have hm : mateEquiv ai ak alpha = beta := (mateEquiv ai ak).apply_symm_apply beta
  have h := iterated_mateEquiv_conjugateEquiv ai ak aj ab alpha
  rw [hm] at h
  have hc : IsIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha) := by
    rw [← h]
    exact isIso_mate_localRestrictionBaseChangeMap A sq
  have := hc
  let e := (conjugateIsoEquiv (ai.comp ab) (aj.comp ak)).symm
    (asIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha))
  have he : e.hom = alpha :=
    (conjugateEquiv (ai.comp ab) (aj.comp ak)).symm_apply_apply alpha
  change IsIso alpha
  rw [← he]
  infer_instance

private theorem isIso_unit_sections_of_localization
    (hsq : IsPullback g' j' j g'') (W : U.ProEt)
    (F : Sheaf (ProEt.topology Z) A)
    (hη : IsIso (((proEtaleSheafAdjunction g' A).unit.app
      ((localizationRestriction A j inferInstance).obj F)).hom.app (op W))) :
    IsIso (((proEtaleSheafAdjunction g'' A).unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let G := localizationRestriction A j inferInstance
  let R := proEtaleSheafDirectImage g' A
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A hsq.toCommSq)
  let alpha := (mateEquiv ai ak).symm beta
  have : IsIso alpha := isIso_inverseMate_localRestrictionBaseChange A hsq.toCommSq
  have : IsIso beta := isIso_localRestrictionBaseChangeMap_of_isPullback A hsq
  have hu := unit_mateEquiv_symm ai ak beta F
  have hu' := congrArg (fun f ↦ f.hom.app (op W)) hu
  change ((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W) =
    (ak.unit.app (G.obj F)).hom.app (op W) ≫
      (R.map (alpha.app F)).hom.app (op W) at hu'
  have : IsIso ((ak.unit.app (G.obj F)).hom.app (op W)) := hη
  have : IsIso (((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.app _).hom.app (op W))

end Localization

private theorem affine_closed_coordinates {X Z : Scheme.{t}}
    (i : Z ⟶ X) [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left] :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    ∃ e : pullback V.hom i ≅ Spec (.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        pullback.fst V.hom i ≫ V.left.isoSpec.hom := by
  let T := pullback V.hom i
  let f : T ⟶ V.left := pullback.fst V.hom i
  obtain ⟨hT, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  have : IsAffine T := hT
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker f.appTop.hom
  let E := RingHom.quotientKerEquivOfSurjective hf
  let e : T ≅ Spec (.of (A ⧸ I)) :=
    T.isoSpec ≪≫ Scheme.Spec.mapIso E.toCommRingCatIso.op
  refine ⟨e, ?_⟩
  change T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f ≫ V.left.isoSpec.hom
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom E.toRingHom = f.appTop := by
    ext a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf a
  rw [he]
  exact Scheme.isoSpec_hom_naturality f

private theorem affine_closed_square {X Z : Scheme.{t}}
    (i : Z ⟶ X) [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left] :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    ∃ b : Spec (.of (A ⧸ I)) ⟶ Z,
      WeaklyEtale b ∧ IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        b (V.left.isoSpec.inv ≫ V.hom) i := by
  obtain ⟨e, he⟩ := affine_closed_coordinates i V
  let b := e.inv ≫ pullback.snd V.hom i
  have hb : WeaklyEtale b := by
    dsimp [b]
    infer_instance
  refine ⟨b, hb, ?_⟩
  apply (IsPullback.of_hasPullback V.hom i).of_iso e V.left.isoSpec
    (Iso.refl Z) (Iso.refl X)
  · exact he.symm
  · simp [b]
  · simp
  · simp

/-- For affine `V`, if evaluation at the identity object is projective and the counit of the
affine closed-site lift adjunction is invertible there, then the inverse-image unit is an
isomorphism on sections over `V`. -/
private theorem isIso_proEtaleUnit_sections_of_closedSiteCounit
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
 :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) →
    ∀ adj : AffineProEt.closedSiteLift A I ⊣ AffineProEt.closedSiteBaseChange A I,
      IsIso (adj.counit.app B) →
      IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{max u (t + 1)}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}).obj (op V))) := by
  dsimp only
  intro hB adj hε
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
  let a : Spec A ⟶ X := V.left.isoSpec.inv ≫ V.hom
  have : WeaklyEtale a := by dsimp [a]; infer_instance
  obtain ⟨b, hb, hsq⟩ := affine_closed_square i V
  have : WeaklyEtale b := hb
  let W : (Spec A).ProEt := ProEt.mk (𝟙 (Spec A))
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale a)).obj W ≅ V :=
    MorphismProperty.Over.isoMk V.left.isoSpec.symm (by
      change a = (𝟙 (Spec A)) ≫ a
      exact (Category.id_comp a).symm)
  have hη (F : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}) :
      IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{max u (t + 1)}).unit.app F).hom.app
        (op V)) := by
    have hf := AffineProEt.isIso_affineUnit_sections A I
      (AffineProEt.ofEtale (𝟙 (Spec A))) hB adj hε
      ((localizationRestriction AddCommGrpCat.{max u (t + 1)}
        a inferInstance).obj F)
    have hl := isIso_unit_sections_of_localization AddCommGrpCat.{max u (t + 1)} hsq W F hf
    exact (NatTrans.isIso_app_iff_of_iso _ e.op).mpr hl
  have : ∀ F, IsIso ((Functor.whiskerRight
      (proEtaleSheafAdjunction i AddCommGrpCat.{max u (t + 1)}).unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}).obj (op V))).app F) := hη
  exact NatIso.isIso_of_isIso_app _

end IndependentSpecialization

/-- The actual abelian inverse-image unit is bijective on an affine specialization
neighbourhood, for any chosen left adjoint and independently sized coefficients. -/
theorem proEtale_abelian_unit_bijective_of_specialization
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z))
    (B : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)})
    (aB : B ⊣ (proEtaleBaseChange i).sheafPushforwardContinuous
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z))
    (M : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}) :
    Function.Bijective ((aB.unit.app M).hom.app (op V)) := by
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
  let W := AffineProEt.ofEtale (𝟙 (Spec A))
  obtain ⟨hW, hspecW⟩ := IndependentSpecialization.specialization_affine_coordinates
    i V hweak hspec
  obtain ⟨_, _, _, _, _, ⟨adj⟩, _, _⟩ :=
    AffineProEt.affine_closed_site_functor_properties A I
  have hc : IsIso (adj.counit.app W) :=
    IndependentSpecialization.AffineProEt.isIso_closedSiteCounit_of_specialization
      A I adj W hW hspecW
  have hu := IndependentSpecialization.isIso_proEtaleUnit_sections_of_closedSiteCounit
    i V hW adj hc
  let a := IndependentSpecialization.proEtaleSheafAdjunction i AddCommGrpCat.{max u (t + 1)}
  let E := sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⋙
    (CategoryTheory.evaluation _ _).obj (op V)
  have : IsIso (E.map (a.unit.app M)) :=
    inferInstanceAs (IsIso ((Functor.whiskerRight a.unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}).obj (op V))).app M))
  have he := congrArg E.map (Adjunction.unit_leftAdjointUniq_hom_app a aB M)
  rw [E.map_comp] at he
  have : IsIso (E.map (aB.unit.app M)) := by
    rw [← he]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (E.map (aB.unit.app M))

end AlgebraicGeometry.Scheme
