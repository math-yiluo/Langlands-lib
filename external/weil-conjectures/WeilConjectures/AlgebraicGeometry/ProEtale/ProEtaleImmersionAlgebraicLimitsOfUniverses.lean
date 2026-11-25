/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.LargeSetSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-! # Immersion inverse image with independently sized algebraic coefficients

## References

* Stacks Tags 09AA and 09BL, including Zariski localization and the finite-operation descriptions of
  rings and abelian groups (Tag 00YV)
-/

@[expose] public section
set_option autoImplicit false
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev inverse {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  sheafPullback (proEtaleBaseChange f) (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)

private noncomputable abbrev inverseAdj {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  sheafAdjunctionContinuous (proEtaleBaseChange f) (Type (max u (t + 1)))
    (ProEt.topology Y) (ProEt.topology X)

namespace AffineProEt

private theorem large_leftAdjoint_sigmaCover_glue {S T : Scheme.{t}}
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
    (isColimitOfPreserves v (sigmaCover_colimit U f))
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

private theorem large_precomposition_unit_injective {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt)
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) (Type (max u (t + 1)))) (V : S.AffineProEt) :
    Function.Injective ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  have : (topology S).WEqualsLocallyBijective (Type (max u (t + 1))) :=
    largeSetSheafification_locallyBijective (topology S)
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

private theorem large_precomposition_unit_surjective {S T : Scheme.{t}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (H : Sheaf (topology T) (Type (max u (t + 1)))) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (t + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V))) :
    Function.Surjective ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  classical
  have : (topology S).WEqualsLocallyBijective (Type (max u (t + 1))) :=
    largeSetSheafification_locallyBijective (topology S)
  let P := v.op ⋙ H.obj
  let G := (presheafToSheaf (topology S) (Type (max u (t + 1)))).obj P
  let η := toSheafify (topology S) P
  intro s
  obtain ⟨ι, _, U, f, hf, hs⟩ := exists_finite_jointly_surjective_of_mem_topology
    (Presheaf.imageSieve_mem (topology S) η (U := op V) s)
  choose x hx using hf
  obtain ⟨z, hz⟩ := large_leftAdjoint_sigmaCover_glue v adj U f H x
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

private theorem large_evaluation (A : Type t) [CommRing A] (I : Ideal A) :
    Nonempty
      (inverse.{t, u} (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
        (toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous
          (Type (max u (t + 1)))
          (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I)))) ≅
      sheafToPresheaf (ProEt.topology (Spec (.of A))) (Type (max u (t + 1))) ⋙
        (Functor.whiskeringLeft _ _ (Type (max u (t + 1)))).obj
          (closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙
        presheafToSheaf (topology (Spec (.of (A ⧸ I)))) (Type (max u (t + 1)))) := by
  classical
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let v := closedSiteLift A I
  let u := closedSiteBaseChange A I
  obtain ⟨_, _, _, _, hco, ⟨adj⟩, hcov, _⟩ := affine_closed_site_functor_properties A I
  let : v.IsCocontinuous (topology Z) (topology X) := hco
  let : u.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  let RX := (toProEt X).sheafPushforwardContinuous (Type (max u (t + 1)))
    (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous (Type (max u (t + 1)))
    (topology Z) (ProEt.topology Z)
  let L := sheafToPresheaf (topology X) (Type (max u (t + 1))) ⋙
    (Functor.whiskeringLeft _ _ (Type (max u (t + 1)))).obj v.op ⋙
    presheafToSheaf (topology Z) (Type (max u (t + 1)))
  let R := u.sheafPushforwardContinuous (Type (max u (t + 1))) (topology X) (topology Z)
  have a : L ⊣ R :=
    ((adj.op.whiskerLeft (Type (max u (t + 1)))).comp
      (sheafificationAdjunction (topology Z) (Type (max u (t + 1))))).restrictFullyFaithful
        (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf (topology X) _))
        (Functor.FullyFaithful.id _)
        (Iso.refl _) (Iso.refl _)
  have t : u ⋙ toProEt Z ≅ toProEt X ⋙ proEtaleBaseChange i := Iso.refl _
  let : (toProEt X ⋙ proEtaleBaseChange i).IsContinuous
      (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (ProEt.topology X)
      (ProEt.topology Z)
  let : (u ⋙ toProEt Z).IsContinuous (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (topology Z) (ProEt.topology Z)
  let beta : (proEtaleBaseChange i).sheafPushforwardContinuous (Type (max u (t + 1)))
      (ProEt.topology X) (ProEt.topology Z) ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X) (proEtaleBaseChange i)
      (Type (max u (t + 1))) (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm (Type (max u (t + 1)))
      (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp u (toProEt Z) (Type (max u (t + 1)))
      (topology X) (topology Z) (ProEt.topology Z)).symm
  let alpha := ((mateEquiv (inverseAdj.{t, u} i) a).symm
    beta.hom)
  have : IsIso alpha :=
    isIso_inverseMate_of_equivalences (inverseAdj.{t, u} i) a beta
  exact ⟨(asIso alpha).symm⟩

end AffineProEt

private theorem sectionsLimits {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (V : C) :
    PreservesLimitsOfSize.{0, 0} ((sheafSections J (Type u)).obj (op V)) := by
  constructor
  intro I _
  exact preservesLimitsOfShape_of_natIso
    (sheafSectionsNatIsoEvaluation J (Type u)).symm

namespace AffineProEt

private abbrev nativeProjective (S : Scheme.{t}) (V : S.AffineProEt) : Prop :=
  ∀ (P Q : Sheaf (topology S) (Type (t + 1))) (f : P ⟶ Q),
    Epi f → Function.Surjective (f.hom.app (op V))

private theorem projective_evaluations_conservative (S : Scheme.{t}) [IsAffine S] :
    JointlyReflectIsomorphisms (fun V : {V : S.AffineProEt // nativeProjective S V} ↦
      (sheafSections (topology S) (Type (max u (t + 1)))).obj (op V.val)) := by
  constructor
  intro F G a ha
  have hb (V : S.AffineProEt) (hV : nativeProjective S V) :
      Function.Bijective (a.hom.app (op V)) := by
    exact (isIso_iff_bijective _).mp (ha ⟨V, hV⟩)
  have hi : Presheaf.IsLocallyInjective (topology S) a.hom := by
    constructor
    intro V x y hxy
    obtain ⟨ι, W, f, hc, hW⟩ := exists_weaklyContractible_cover S V.unop
    apply (topology S).superset_covering _ (precoverage_cover hc)
    rw [Sieve.generate_le_iff]
    rintro T g ⟨j⟩
    apply (hb (W j) (hW j)).injective
    rw [a.hom.naturality_apply, a.hom.naturality_apply, hxy]
  have hs : Presheaf.IsLocallySurjective (topology S) a.hom := by
    constructor
    intro V y
    obtain ⟨ι, W, f, hc, hW⟩ := exists_weaklyContractible_cover S V
    apply (topology S).superset_covering _ (precoverage_cover hc)
    rw [Sieve.generate_le_iff]
    rintro T g ⟨j⟩
    exact (hb (W j) (hW j)).surjective (G.obj.map (f j).op y)
  exact (Sheaf.isLocallyBijective_iff_isIso a).mp ⟨hi, hs⟩

private theorem quotient_limits (A : Type t) [CommRing A] (I : Ideal A) :
    PreservesLimitsOfSize.{0, 0}
      (inverse.{t, u} (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let res := (toProEt Z).sheafPushforwardContinuous (Type (max u (t + 1)))
    (topology Z) (ProEt.topology Z)
  let R := inverse.{t, u} q ⋙ res
  let v := closedSiteLift A I ⋙ toProEt X
  let P := sheafToPresheaf (ProEt.topology X) (Type (max u (t + 1))) ⋙
    (Functor.whiskeringLeft _ _ (Type (max u (t + 1)))).obj v.op
  let E := fun V : {V : Z.AffineProEt // nativeProjective Z V} ↦
    (sheafSections (topology Z) (Type (max u (t + 1)))).obj (op V.val)
  have heval (V : {V : Z.AffineProEt // nativeProjective Z V}) :
      PreservesLimitsOfSize.{0, 0} (R ⋙ E V) := by
    let η : (sheafSections (ProEt.topology X) (Type (max u (t + 1)))).obj
          (op (v.obj V.val)) ⟶
        (P ⋙ presheafToSheaf (topology Z) (Type (max u (t + 1)))) ⋙ E V :=
      { app := fun F ↦ (toSheafify (topology Z) (P.obj F)).app (op V.val)
        naturality := by
          intro F G f
          exact congr_app (toSheafify_naturality (topology Z) (P.map f)) (op V.val) }
    obtain ⟨_, _, _, _, _, ⟨adj⟩, hcov, _⟩ := affine_closed_site_functor_properties A I
    have : (topology Z).Subcanonical :=
      GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt Z)
        (topology Z) (ProEt.topology Z)
    have hη (F : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) :
        IsIso (η.app F) := by
      rw [isIso_iff_bijective]
      let H := ((toProEt X).sheafPushforwardContinuous (Type (max u (t + 1)))
        (topology X) (ProEt.topology X)).obj F
      exact ⟨large_precomposition_unit_injective _ hcov H V.val,
        large_precomposition_unit_surjective _ adj H V.val V.property⟩
    have : IsIso η := NatIso.isIso_of_isIso_app η
    obtain ⟨e⟩ := large_evaluation.{t, u} A I
    have := sectionsLimits.{max u (t + 1)} (ProEt.topology X) (v.obj V.val)
    exact preservesLimits_of_natIso
      (asIso η ≪≫ (Functor.isoWhiskerRight e (E V)).symm)
  have hE : ∀ V, PreservesLimitsOfSize.{0, 0} (E V) :=
    fun V ↦ sectionsLimits.{max u (t + 1)} (topology Z) V.val
  have hR : PreservesLimitsOfSize.{0, 0} R := by
    constructor
    intro J _
    constructor
    intro D
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
    apply (projective_evaluations_conservative.{t, u} Z).jointlyReflectsLimit
    intro V
    let := heval V
    exact isLimitOfPreserves (R ⋙ E V) (limit.isLimit D)
  exact preservesLimits_of_reflects_of_preserves (inverse.{t, u} q) res

end AffineProEt

private noncomputable def inverseComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverse.{t, u} (f ≫ g) ≅ inverse.{t, u} g ⋙ inverse.{t, u} f := by
  let a := (inverseAdj.{t, u} g).comp (inverseAdj.{t, u} f)
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    (Type (max u (t + 1))) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  exact (inverseAdj.{t, u} (f ≫ g)).leftAdjointUniq (a.ofNatIsoRight e)

private noncomputable def restrictionIso {X Y : Scheme.{t}} (f : X ⟶ Y) [WeaklyEtale f] :
    inverse.{t, u} f ≅
      (MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{t})
        (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
          (Type (max u (t + 1))) (ProEt.topology X) (ProEt.topology Y) := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) _root_.trivial).sheafPushforwardContinuous
      (E := Type (max u (t + 1))) (ProEt.topology X) (ProEt.topology Y)
  exact (inverseAdj.{t, u} f).leftAdjointUniq a

private theorem restrictionLimits {X Y : Scheme.{t}} (f : X ⟶ Y) [WeaklyEtale f] :
    PreservesLimitsOfSize.{0, 0} (inverse.{t, u} f) :=
  preservesLimits_of_natIso (restrictionIso.{t, u} f).symm

private theorem zariskiLimits
    {X Y : Scheme.{t}} (f : Y ⟶ X)
    (h : ∀ U : X.affineOpens,
      PreservesLimitsOfSize.{0, 0}
        (inverse.{t, u} (f ∣_ U.1))) :
    PreservesLimitsOfSize.{0, 0}
      (inverse.{t, u} f) := by
  let K := fun U : X.affineOpens ↦
    inverse.{t, u} (f ⁻¹ᵁ U.1).ι
  have hK : ∀ U, PreservesLimitsOfSize.{0, 0} (K U) :=
    fun U ↦ restrictionLimits.{t, u} (f ⁻¹ᵁ U.1).ι
  have hcomp : ∀ U, PreservesLimitsOfSize.{0, 0}
      (inverse.{t, u} f ⋙ K U) := by
    intro U
    let := h U
    let := restrictionLimits.{t, u} U.1.ι
    have : PreservesLimitsOfSize.{0, 0}
        (inverse.{t, u} (f ∣_ U.1 ≫ U.1.ι)) :=
      preservesLimits_of_natIso (inverseComp.{t, u} (f ∣_ U.1) U.1.ι).symm
    rw [morphismRestrict_ι] at this
    exact preservesLimits_of_natIso (inverseComp.{t, u} (f ⁻¹ᵁ U.1).ι f)
  have hc : Presieve.ofArrows (fun U : X.affineOpens ↦ (f ⁻¹ᵁ U.1).toScheme)
      (fun U ↦ (f ⁻¹ᵁ U.1).ι) ∈ proetalePrecoverage Y := by
    apply zariskiPrecoverage_le_proetalePrecoverage
    apply (ofArrows_mem_precoverage_iff _).mpr
    refine ⟨?_, fun U ↦ inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U.1).ι)⟩
    intro y
    have hy : f.base y ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X, TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨U, hU⟩ := hy
    exact ⟨U, by simpa using hU⟩
  have hcon : JointlyReflectIsomorphisms K := by
    constructor
    intro F G a ha
    have hr (U : X.affineOpens) : IsIso
        (((MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{t})
          (inferInstance : WeaklyEtale (f ⁻¹ᵁ U.1).ι)).sheafPushforwardContinuous
            (Type (max u (t + 1))) (ProEt.topology (f ⁻¹ᵁ U.1)) (ProEt.topology Y)).map a) := by
      exact (NatIso.isIso_map_iff (restrictionIso.{t, u} (f ⁻¹ᵁ U.1).ι) a).mp (ha U)
    refine Sheaf.isIso_of_isIso_app_of_mem _ a fun V ↦
      ⟨_, ProEt.ofArrows_baseChange_mem_topology V
        (fun U : X.affineOpens ↦ (f ⁻¹ᵁ U.1).ι) hc, ?_⟩
    rintro T k ⟨W, b, Z, ⟨U⟩, rfl⟩
    let g := (f ⁻¹ᵁ U.1).ι
    let p := b.left ≫ pullback.snd V.hom g
    have hp : p ≫ g = T.hom := by
      dsimp [p]
      rw [Category.assoc, ← pullback.condition]
      exact MorphismProperty.Over.w b
    have hpwe : WeaklyEtale p :=
      MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
        p g (inferInstance : WeaklyEtale g) (by rw [hp]; exact T.prop)
    have h1 : IsIso
        ((((MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{t})
          (inferInstance : WeaklyEtale g)).sheafPushforwardContinuous
            (Type (max u (t + 1))) (ProEt.topology (f ⁻¹ᵁ U.1)) (ProEt.topology _)).map a).hom.app
              (op (MorphismProperty.Over.mk ⊤ p hpwe))) := by
      let := hr U
      infer_instance
    have e : (MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{t})
        (inferInstance : WeaklyEtale g)).obj (MorphismProperty.Over.mk ⊤ p hpwe) ≅ T :=
      MorphismProperty.Over.isoMk (Iso.refl _) (by simpa using hp.symm)
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ a.hom _ _ e.op h1
  constructor
  intro J _
  constructor
  intro D
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
  apply hcon.jointlyReflectsLimit
  intro U
  let := hcomp U
  exact isLimitOfPreserves (inverse.{t, u} f ⋙ K U)
    (limit.isLimit D)

private theorem compLimits {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [PreservesLimitsOfSize.{0, 0} (inverse.{t, u} f)]
    [PreservesLimitsOfSize.{0, 0} (inverse.{t, u} g)] :
    PreservesLimitsOfSize.{0, 0} (inverse.{t, u} (f ≫ g)) :=
  preservesLimits_of_natIso (inverseComp.{t, u} f g).symm

private theorem affineClosedLimits {Z X : Scheme.{t}} [IsAffine Z] [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesLimitsOfSize.{0, 0} (inverse.{t, u} i) := by
  obtain ⟨I, e, hi⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion (i ≫ X.isoSpec.hom))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : PreservesLimitsOfSize.{0, 0} (inverse.{t, u} q) := AffineProEt.quotient_limits _ I
  have := restrictionLimits.{t, u} e.hom
  have := restrictionLimits.{t, u} X.isoSpec.inv
  have := compLimits.{t, u} e.hom q
  have hi' : i = (e.hom ≫ q) ≫ X.isoSpec.inv := by
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi']
  exact compLimits.{t, u} (e.hom ≫ q) X.isoSpec.inv

private theorem closedLimits {X Y : Scheme.{t}} (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesLimitsOfSize.{0, 0} (inverse.{t, u} f) := by
  apply zariskiLimits.{t, u} f
  intro U
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  exact affineClosedLimits.{t, u} (f ∣_ U.1)

private theorem immersionLimits {X Y : Scheme.{t}} (f : X ⟶ Y) [IsImmersion f] :
    PreservesLimitsOfSize.{0, 0} (inverse.{t, u} f) := by
  have := closedLimits.{t, u} f.liftCoborder
  have := restrictionLimits.{t, u} f.coborderRange.ι
  simpa only [Scheme.Hom.liftCoborder_ι] using
    compLimits.{t, u} f.liftCoborder f.coborderRange.ι

private noncomputable def modelEquivalence (Z : Scheme.{t})
    (D : Type v) [Category.{w} D] :
    Sheaf (coefficientProEtaleModelTopology.{t, u} Z) D ≌ Sheaf (ProEt.topology Z) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : Z.ProEt ⥤ coefficientProEtaleSiteModel.{t, u} Z).sheafPushforwardContinuous
      D (ProEt.topology Z) (coefficientProEtaleModelTopology Z))
    ((AsSmall.down : coefficientProEtaleSiteModel.{t, u} Z ⥤ Z.ProEt).sheafPushforwardContinuous
      D (coefficientProEtaleModelTopology Z) (ProEt.topology Z))
    (Iso.refl _) (Iso.refl _)

private theorem ringLimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    [PreservesLimitsOfSize.{0, 0} (sheafPullback F (Type u) J K)]
    (L : Sheaf J RingCat.{u} ⥤ Sheaf K RingCat.{u})
    (adj : L ⊣ F.sheafPushforwardContinuous RingCat.{u} J K) :
    PreservesLimitsOfSize.{0, 0} L := by
  let U := CategoryTheory.forget RingCat.{u}
  have hf (T : GrothendieckTopology C) :
      PreservesLimitsOfSize.{0, 0} (sheafCompose T U) := by
    have : PreservesLimitsOfSize.{0, 0} (sheafCompose T U ⋙ sheafToPresheaf T (Type u)) :=
      show PreservesLimitsOfSize.{0, 0}
        (sheafToPresheaf T RingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj U) by
          infer_instance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf T (Type u))
  have hg : PreservesLimitsOfSize.{0, 0} (sheafCompose K U) := by
    have : PreservesLimitsOfSize.{0, 0} (sheafCompose K U ⋙ sheafToPresheaf K (Type u)) :=
      show PreservesLimitsOfSize.{0, 0}
        (sheafToPresheaf K RingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj U) by
          infer_instance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf K (Type u))
  have := hf J
  have : ReflectsLimitsOfSize.{0, 0} (sheafCompose K U) :=
    reflectsLimits_of_reflectsIsomorphisms
  let e := adj.leftAdjointUniq (sheafAdjunctionContinuous F RingCat.{u} J K)
  let c := Functor.isoWhiskerRight e (sheafCompose K U) ≪≫ sheafPullbackForgetIso J K F U
  have : PreservesLimitsOfSize.{0, 0} (L ⋙ sheafCompose K U) :=
    preservesLimits_of_natIso c.symm
  exact preservesLimits_of_reflects_of_preserves L (sheafCompose K U)

private theorem abelianLimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    [PreservesLimitsOfSize.{0, 0} (sheafPullback F (Type u) J K)]
    (L : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    (adj : L ⊣ F.sheafPushforwardContinuous AddCommGrpCat.{u} J K) :
    PreservesLimitsOfSize.{0, 0} L := by
  let U := CategoryTheory.forget AddCommGrpCat.{u}
  have hf (T : GrothendieckTopology C) :
      PreservesLimitsOfSize.{0, 0} (sheafCompose T U) := by
    have : PreservesLimitsOfSize.{0, 0} (sheafCompose T U ⋙ sheafToPresheaf T (Type u)) :=
      show PreservesLimitsOfSize.{0, 0}
        (sheafToPresheaf T AddCommGrpCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj U) by
          infer_instance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf T (Type u))
  have hg : PreservesLimitsOfSize.{0, 0} (sheafCompose K U) := by
    have : PreservesLimitsOfSize.{0, 0} (sheafCompose K U ⋙ sheafToPresheaf K (Type u)) :=
      show PreservesLimitsOfSize.{0, 0}
        (sheafToPresheaf K AddCommGrpCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj U) by
          infer_instance
    exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf K (Type u))
  have := hf J
  have : ReflectsLimitsOfSize.{0, 0} (sheafCompose K U) :=
    reflectsLimits_of_reflectsIsomorphisms
  let e := adj.leftAdjointUniq (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K)
  let c := Functor.isoWhiskerRight e (sheafCompose K U) ≪≫ sheafPullbackForgetIso J K F U
  have : PreservesLimitsOfSize.{0, 0} (L ⋙ sheafCompose K U) :=
    preservesLimits_of_natIso c.symm
  exact preservesLimits_of_reflects_of_preserves L (sheafCompose K U)

/-- Ring and abelian inverse image along an immersion preserve small limits,
regardless of the independent coefficient universe or the choice of left adjoint. -/
theorem proEtale_immersion_algebraicInverse_limits
    {X Y : Scheme.{t}} (i : X ⟶ Y) [IsImmersion i]
    (L : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (aL : L ⊣ (proEtaleBaseChange i).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X))
    (B : Sheaf (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)})
    (aB : B ⊣ (proEtaleBaseChange i).sheafPushforwardContinuous
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)) :
    PreservesLimitsOfSize.{0, 0} L ∧ PreservesLimitsOfSize.{0, 0} B := by
  let eRY := modelEquivalence.{t, u} Y RingCat.{max u (t + 1)}
  let eRX := modelEquivalence.{t, u} X RingCat.{max u (t + 1)}
  let eAY := modelEquivalence.{t, u} Y AddCommGrpCat.{max u (t + 1)}
  let eAX := modelEquivalence.{t, u} X AddCommGrpCat.{max u (t + 1)}
  let eSY := modelEquivalence.{t, u} Y (Type (max u (t + 1)))
  let eSX := modelEquivalence.{t, u} X (Type (max u (t + 1)))
  let U := coefficientProEtaleModelBaseChange.{t, u} i
  let J := coefficientProEtaleModelTopology.{t, u} Y
  let K := coefficientProEtaleModelTopology.{t, u} X
  let L' := eRY.functor ⋙ L ⋙ eRX.inverse
  let B' := eAY.functor ⋙ B ⋙ eAX.inverse
  let aL' : L' ⊣ U.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K :=
    aL.restrictFullyFaithful eRY.fullyFaithfulFunctor eRX.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  let aB' : B' ⊣ U.sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)} J K :=
    aB.restrictFullyFaithful eAY.fullyFaithfulFunctor eAX.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  let aS' : (eSY.functor ⋙ inverse.{t, u} i ⋙ eSX.inverse) ⊣
      U.sheafPushforwardContinuous (Type (max u (t + 1))) J K :=
    (inverseAdj.{t, u} i).restrictFullyFaithful
      eSY.fullyFaithfulFunctor eSX.fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)
  have := immersionLimits.{t, u} i
  let e := aS'.leftAdjointUniq (sheafAdjunctionContinuous U (Type (max u (t + 1))) J K)
  have : PreservesLimitsOfSize.{0, 0} (sheafPullback U (Type (max u (t + 1))) J K) :=
    preservesLimits_of_natIso e
  let : (AsSmall.down :
      coefficientProEtaleSiteModel.{t, u} Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up :
      X.ProEt ⥤ coefficientProEtaleSiteModel.{t, u} X).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits U := by
    dsimp [U, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : PreservesLimitsOfSize.{0, 0} L' := ringLimits J K U L' aL'
  have : PreservesLimitsOfSize.{0, 0} B' := abelianLimits J K U B' aB'
  have hL : PreservesLimitsOfSize.{0, 0} (eRY.inverse ⋙ L' ⋙ eRX.functor) := inferInstance
  have hB : PreservesLimitsOfSize.{0, 0} (eAY.inverse ⋙ B' ⋙ eAX.functor) := inferInstance
  exact ⟨preservesLimits_of_natIso (Iso.refl _ : (eRY.inverse ⋙ L' ⋙ eRX.functor) ≅ L),
    preservesLimits_of_natIso (Iso.refl _ : (eAY.inverse ⋙ B' ⋙ eAX.functor) ≅ B)⟩

end AlgebraicGeometry.Scheme
