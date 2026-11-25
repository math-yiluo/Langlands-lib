/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Finite
public import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos

import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.RingTheory.ProEtale.IdentifiesLocalRings
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.EffectiveEpi.Extensive
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sheaves.Stalks

/-!
# The component-site projection of an affine scheme

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 2.2.8,
paragraph preceding Lemma 4.2.13, and Lemma 4.2.13(1), with the split-cover
qualification recorded in the DAG (blueprint: lem-zl-affine-component-site-projection).

## Main definitions

* `componentProfinite`: the component quotient of a qcqs scheme, as a profinite space.
* `componentObject`, `componentObjectMap`: the component object of a qcqs pro-etale
  object over the component quotient of the base, and its map on morphisms.
* `HasSplitFiniteQcqsCovers`: the split-cover condition on a qcqs pro-etale object.
* `ComponentSiteEvaluation`: the geometric morphism with its split-cover evaluation in one
  coefficient category.

## Main statements

* `affine_component_site_projection`: the component-site projection of an affine scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Bundle the actual component quotient with its quotient topology. The structure proofs
come from the spectral-component theorem; there is no chosen replacement space.
Source: Bhatt--Scholze, Lemma 2.2.8
(blueprint: lem-zl-affine-component-site-projection). -/
def componentProfinite (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Profinite.{u} := by
  letI : SpectralSpace X := {}
  exact @Profinite.of (ConnectedComponents X) _
    (spectralSpace_connectedComponents_profinite (T := X)).1
    (spectralSpace_connectedComponents_profinite (T := X)).2.1
    (spectralSpace_connectedComponents_profinite (T := X)).2.2

/-- The component object of a qcqs pro-etale object, over the component quotient of the base.
Source: Bhatt--Scholze, Lemma 2.2.8 and paragraph before Lemma 4.2.13
(blueprint: lem-zl-affine-component-site-projection). -/
def componentObject (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (W : Qcqs T) : Over (componentProfinite T) := by
  letI : CompactSpace W.obj.left := W.property.1
  letI : QuasiSeparatedSpace W.obj.left := W.property.2
  exact Over.mk (ConcreteCategory.ofHom
    ⟨W.obj.hom.continuous.connectedComponentsMap,
      W.obj.hom.continuous.connectedComponentsMap_continuous⟩ :
        componentProfinite W.obj.left ⟶ componentProfinite T)

/-- The map on actual component quotients induced by a map over the base.
Source: Bhatt--Scholze, Lemma 4.2.13(1), canonical factorization
(blueprint: lem-zl-affine-component-site-projection). -/
def componentObjectMap {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    {V W : Qcqs T} (a : V ⟶ W) : componentObject T V ⟶ componentObject T W :=
  Over.homMk (ConcreteCategory.ofHom
    ⟨a.hom.left.continuous.connectedComponentsMap,
      a.hom.left.continuous.connectedComponentsMap_continuous⟩) (by
        ext z
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
        change ConnectedComponents.mk (W.obj.hom (a.hom.left x)) =
          ConnectedComponents.mk (V.obj.hom x)
        exact congrArg ConnectedComponents.mk
          (congrArg (fun f : V.obj.left ⟶ T ↦ f x) a.hom.w))

/-- Precisely the finite qcqs split-cover condition: the canonical coproduct map has a
scheme section. Since the coproduct map is over T, its section is automatically over T.
Finite index sets are represented by Fin n, including n = 0.
Source: the corrected split-cover form of Bhatt--Scholze, Lemma 4.2.13(1),
using Stacks Tags 00WB and 00WK (blueprint: lem-zl-affine-component-site-projection). -/
def HasSplitFiniteQcqsCovers {T : Scheme.{u}} (W : Qcqs T) : Prop :=
  ∀ (n : ℕ) (V : Fin n → Qcqs T) (a : ∀ i, (V i).obj ⟶ W.obj),
    Presieve.ofArrows (fun i ↦ (V i).obj) a ∈ precoverage T W.obj →
      ∃ σ : W.obj.left ⟶ ∐ (fun i ↦ (V i).obj.left),
        σ ≫ Sigma.desc (fun i ↦ (a i).left) = 𝟙 W.obj.left

/-- The evaluation assertion in a coefficient category. The direct image is identified
with actual restriction along U. Its adjunction unit and the component factorization b
normalize the evaluation isomorphisms, which are natural in both sheaves and eligible W.
Taking C to be sets, abelian groups, or rings retains all operations.
Source: Bhatt--Scholze, Lemma 4.2.13(1), with split-cover sheafification via
Stacks Tags 00WB/00WK (blueprint: lem-zl-affine-component-site-projection). -/
def ComponentSiteEvaluation (T : Scheme.{u}) [IsAffine T]
    (U : Over (componentProfinite T) ⥤ T.ProEt)
    (r : ∀ E : Over (componentProfinite T), C((U.obj E).left, E.left))
    (hU : U.IsContinuous ((coherentTopology Profinite.{u}).over (componentProfinite T))
      (topology T))
    (C : Type w) [Category.{v} C] : Prop :=
  ∃ g : GeometricMorphism (Sheaf (topology T) C)
      (Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T)) C),
    ∃ d : g.direct ≅ U.sheafPushforwardContinuous C
        ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T),
      ∃ b : ∀ (W : Qcqs T) (E : Over (componentProfinite T)),
          (W.obj ⟶ U.obj E) → (componentObject T W ⟶ E),
        (∀ (W : Qcqs T) (E : Over (componentProfinite T))
          (a : W.obj ⟶ U.obj E) (x : W.obj.left),
          (b W E a).left (ConnectedComponents.mk x) = r E (a.left x)) ∧
        ∃ e : ∀ (F : Sheaf
            ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (W : Qcqs T) (_hW : HasSplitFiniteQcqsCovers W),
              (g.inverse.obj F).obj.obj (op W.obj) ≅ F.obj.obj (op (componentObject T W)),
          (∀ (F : Sheaf
              ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (W : Qcqs T) (hW : HasSplitFiniteQcqsCovers W)
            (E : Over (componentProfinite T)) (a : W.obj ⟶ U.obj E),
            ((g.adj.unit.app F ≫ d.hom.app (g.inverse.obj F)).hom.app (op E)) ≫
                (g.inverse.obj F).obj.map a.op ≫ (e F W hW).hom =
              F.obj.map (b W E a).op) ∧
          (∀ (F G : Sheaf
              ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (α : F ⟶ G) (V W : Qcqs T)
            (hV : HasSplitFiniteQcqsCovers V) (hW : HasSplitFiniteQcqsCovers W)
            (a : V ⟶ W),
            (g.inverse.obj F).obj.map a.hom.op ≫
                (g.inverse.map α).hom.app (op V.obj) ≫ (e G V hV).hom =
              (e F W hW).hom ≫ F.obj.map (componentObjectMap a).op ≫
                α.hom.app (op (componentObject T V)))

-- The source correspondence assumes both algebras identify local rings. Its inverse
-- and injectivity arguments only need that property for B, as checked here.
open Algebra.BijectiveOnStalks in
private theorem component_algHom_bijective
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.BijectiveOnStalks A B] :
    Function.Bijective (Algebra.BijectiveOnStalks.continuousMap_of_algHom :
      (B →ₐ[A] C) → Algebra.BijectiveOnStalks.HomOver A B C) := by
  constructor
  · -- Injectivity: an `A`-algebra map `B → C` is determined by its localizations,
    -- which factor through the bijective maps `A_{p ∩ A} → B_{φ(p)}`.
    intro f₁ f₂ heq
    have hcomap (p : PrimeSpectrum C) :
        p.asIdeal.comap f₁.toRingHom = p.asIdeal.comap f₂.toRingHom :=
      congrArg PrimeSpectrum.asIdeal (DFunLike.congr_fun heq p)
    apply AlgHom.toRingHom_injective
    apply RingHom.ext
    intro b
    refine eq_of_localizationAtPrime_eq fun p ↦ ?_
    have : (p.asIdeal.comap f₁.toRingHom).IsPrime := Ideal.IsPrime.comap _
    set q := p.asIdeal.comap f₁.toRingHom with hq
    have : (q.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    set K := Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl
      with hK
    have hKbij : Function.Bijective K :=
      Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) q
    set M₁ := Localization.localRingHom q p.asIdeal f₁.toRingHom rfl with hM₁
    set M₂ := Localization.localRingHom q p.asIdeal f₂.toRingHom (hcomap p) with hM₂
    have hMcomp : M₁.comp K = M₂.comp K := by
      refine IsLocalization.ringHom_ext (q.comap (algebraMap A B)).primeCompl
        (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, hK, hM₁, hM₂,
        Localization.localRingHom_to_map]
      rw [show f₁.toRingHom (algebraMap A B a) = algebraMap A C a from f₁.commutes a,
        show f₂.toRingHom (algebraMap A B a) = algebraMap A C a from f₂.commutes a]
    have hM : M₁ = M₂ := RingHom.ext fun x ↦ by
      obtain ⟨y, rfl⟩ := hKbij.surjective x
      exact RingHom.congr_fun hMcomp y
    change algebraMap C (Localization.AtPrime p.asIdeal) (f₁.toRingHom b) =
      algebraMap C (Localization.AtPrime p.asIdeal) (f₂.toRingHom b)
    rw [← Localization.localRingHom_to_map q p.asIdeal f₁.toRingHom rfl b,
      ← Localization.localRingHom_to_map q p.asIdeal f₂.toRingHom (hcomap p) b,
      ← hM₁, ← hM₂, hM]
  · -- Surjectivity: glue the per-prime maps via the structure sheaf of `Spec C`.
    intro φ
    refine ⟨{ ringHomOfHomOver φ with commutes' := ringHomOfHomOver_algebraMap φ }, ?_⟩
    exact HomOver.ext fun p ↦ comap_ringHomOfHomOver φ p

-- Use the existing explicit graph-restriction algebra; no existential choice of data.
private noncomputable def componentBaseMap (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    C(E.left, ConnectedComponents (PrimeSpectrum Γ(T, ⊤))) :=
  ⟨fun e ↦ T.isoSpec.hom.continuous.connectedComponentsMap (E.hom e),
    T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp E.hom.hom.hom.continuous⟩

private noncomputable abbrev componentAlgebra (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :=
  WContractification.PullbackProfinite Γ(T, ⊤) E.left (componentBaseMap T E)

private noncomputable def componentScheme (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : Scheme.{u} := Spec (.of (componentAlgebra T E))

private instance componentScheme_isAffine (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : IsAffine (componentScheme T E) := by
  dsimp [componentScheme]
  infer_instance

private noncomputable def componentStructure (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : componentScheme T E ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (componentAlgebra T E))) ≫ T.isoSpec.inv

private noncomputable def componentProjection (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : C(componentScheme T E, E.left) :=
  WContractification.PullbackProfinite.projT Γ(T, ⊤) E.left (componentBaseMap T E)

private noncomputable def componentFiberHomeo (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : componentScheme T E ≃ₜ
      {p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2} := by
  let h := WContractification.PullbackProfinite.fiberHomeo
    Γ(T, ⊤) E.left (componentBaseMap T E)
  let e := Scheme.homeoOfIso T.isoSpec
  refine h.trans
    { toFun := fun p ↦ ⟨(e.symm p.1.2, p.1.1), ?_⟩
      invFun := fun p ↦ ⟨(p.1.2, e p.1.1), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have hp := p.2
    change T.isoSpec.hom.continuous.connectedComponentsMap (E.hom p.1.1) =
      ConnectedComponents.mk p.1.2 at hp
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.hom p.1.1)
    rw [← hx, Continuous.connectedComponentsMap_mk] at hp
    change ConnectedComponents.mk (e x) = ConnectedComponents.mk p.1.2 at hp
    have hi := congrArg e.symm.continuous.connectedComponentsMap hp
    change ConnectedComponents.mk (e.symm p.1.2) = E.hom p.1.1
    simpa only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply, hx] using hi.symm
  · change T.isoSpec.hom.continuous.connectedComponentsMap (E.hom p.1.2) = _
    rw [← p.2, Continuous.connectedComponentsMap_mk]
    rfl
  · intro p
    apply Subtype.ext
    exact Prod.ext rfl (e.apply_symm_apply _)
  · intro p
    apply Subtype.ext
    exact Prod.ext (e.symm_apply_apply _) rfl
  · exact (e.symm.continuous.comp (continuous_snd.comp continuous_subtype_val)).prodMk
      (continuous_fst.comp continuous_subtype_val) |>.subtype_mk _
  · exact (continuous_snd.comp continuous_subtype_val).prodMk
      (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) |>.subtype_mk _

private theorem componentFiberHomeo_fst (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : componentScheme T E) :
    (componentFiberHomeo T E x).1.1 = componentStructure T E x := by
  change T.isoSpec.inv
      (WContractification.PullbackProfinite.fiberHomeo
        Γ(T, ⊤) E.left (componentBaseMap T E) x).1.2 = _
  rw [WContractification.PullbackProfinite.snd_fiberHomeo]
  rfl

private theorem componentFiberHomeo_snd (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : componentScheme T E) :
    (componentFiberHomeo T E x).1.2 = componentProjection T E x := rfl

private theorem componentStructure_weaklyEtale (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : WeaklyEtale (componentStructure T E) := by
  dsimp only [componentStructure]
  infer_instance

private noncomputable def componentProEtObject (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : T.ProEt := by
  let := componentStructure_weaklyEtale T E
  exact ProEt.mk (componentStructure T E)

private theorem componentStructure_stalk (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (x : componentScheme T E) :
    IsIso ((componentStructure T E).stalkMap x) := by
  let f : CommRingCat.of Γ(T, ⊤) ⟶ CommRingCat.of (componentAlgebra T E) :=
    CommRingCat.ofHom (algebraMap Γ(T, ⊤) (componentAlgebra T E))
  have hb : IsIso (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap f.hom x).asIdeal x.asIdeal f.hom rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Algebra.BijectiveOnStalks.bijective_localRingHom (R := Γ(T, ⊤)) x.asIdeal)
  have hi : IsIso ((Spec.map f).stalkMap x) := by
    rw [← Scheme.localRingHom_comp_stalkIso]
    infer_instance
  dsimp only [componentStructure]
  rw [Scheme.Hom.stalkMap_comp]
  infer_instance

private theorem componentProjection_surjective (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) : Function.Surjective (componentProjection T E) := by
  intro e
  obtain ⟨t, ht⟩ := ConnectedComponents.surjective_coe (E.hom e)
  refine ⟨(componentFiberHomeo T E).symm ⟨(t, e), ht⟩, ?_⟩
  rw [← componentFiberHomeo_snd, Homeomorph.apply_symm_apply]

private theorem componentProjection_fibers (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) (e : E.left) :
    _root_.IsPreconnected (componentProjection T E ⁻¹' {e}) := by
  obtain ⟨t, ht⟩ := ConnectedComponents.surjective_coe (E.hom e)
  let h := componentFiberHomeo T E
  let f : connectedComponent t → componentScheme T E := fun x ↦
    h.symm ⟨(x.1, e), (ConnectedComponents.coe_eq_coe'.mpr x.2).trans ht⟩
  have hf : Continuous f := h.symm.continuous.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)
  have him : Set.range f = componentProjection T E ⁻¹' {e} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change componentProjection T E (h.symm _) = e
      rw [← componentFiberHomeo_snd, Homeomorph.apply_symm_apply]
    · intro hy
      change componentProjection T E y = e at hy
      have he : (h y).1.2 = e := (componentFiberHomeo_snd T E y).trans hy
      have hx : (h y).1.1 ∈ connectedComponent t := by
        apply ConnectedComponents.coe_eq_coe'.mp
        exact (h y).2.trans ((congrArg E.hom he).trans ht.symm)
      refine ⟨⟨(h y).1.1, hx⟩, ?_⟩
      change h.symm _ = y
      apply h.injective
      rw [h.apply_symm_apply]
      exact Subtype.ext (Prod.ext rfl he.symm)
  let : PreconnectedSpace (connectedComponent t) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  rw [← him, ← Set.image_univ]
  exact isPreconnected_univ.image _ hf.continuousOn

private noncomputable def componentComponentsHomeo (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    ConnectedComponents (componentScheme T E) ≃ₜ E.left :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (componentProjection T E).continuous.connectedComponentsLift
      ⟨(componentProjection T E).continuous.connectedComponentsLift_injective
        (componentProjection_fibers T E),
        fun e ↦ by
          obtain ⟨x, hx⟩ := componentProjection_surjective T E e
          exact ⟨ConnectedComponents.mk x, hx⟩⟩)
    (componentProjection T E).continuous.connectedComponentsLift_continuous

private noncomputable def componentContinuousMap {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') :
    Algebra.BijectiveOnStalks.HomOver Γ(T, ⊤) (componentAlgebra T E')
      (componentAlgebra T E) := by
  let h := WContractification.PullbackProfinite.fiberHomeo
    Γ(T, ⊤) E.left (componentBaseMap T E)
  let h' := WContractification.PullbackProfinite.fiberHomeo
    Γ(T, ⊤) E'.left (componentBaseMap T E')
  let m : C(PrimeSpectrum (componentAlgebra T E), PrimeSpectrum (componentAlgebra T E')) :=
    ⟨fun x ↦ h'.symm ⟨(a.left (h x).1.1, (h x).1.2), by
        change T.isoSpec.hom.continuous.connectedComponentsMap
          (E'.hom (a.left (h x).1.1)) = _
        rw [show E'.hom (a.left (h x).1.1) = E.hom (h x).1.1 from
          ConcreteCategory.congr_hom a.w (h x).1.1]
        exact (h x).2⟩,
      by
        apply h'.symm.continuous.comp
        apply Continuous.subtype_mk
        exact (a.left.hom.hom.continuous.comp
          (continuous_fst.comp (continuous_subtype_val.comp h.continuous))).prodMk
            (continuous_snd.comp (continuous_subtype_val.comp h.continuous))⟩
  exact
    { toContinuousMap := m
      comp_comap_algebraMap x := by
        change WContractification.PullbackProfinite.projSpec _ _ _ (m x) =
          WContractification.PullbackProfinite.projSpec _ _ _ x
        rw [← WContractification.PullbackProfinite.snd_fiberHomeo,
          ← WContractification.PullbackProfinite.snd_fiberHomeo]
        change (h' (h'.symm _)).1.2 = (h x).1.2
        rw [Homeomorph.apply_symm_apply] }

private noncomputable def componentAlgebraMap {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') :
    componentAlgebra T E' →ₐ[Γ(T, ⊤)] componentAlgebra T E :=
  Algebra.BijectiveOnStalks.algHom_of_continuousMap Γ(T, ⊤)
    (componentAlgebra T E') (componentAlgebra T E) (componentContinuousMap a)

private theorem componentAlgebraMap_comap {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E')
    (x : PrimeSpectrum (componentAlgebra T E)) :
    WContractification.PullbackProfinite.fiberHomeo
        Γ(T, ⊤) E'.left (componentBaseMap T E')
      (PrimeSpectrum.comap (componentAlgebraMap a).toRingHom x) =
        ⟨(a.left (componentProjection T E x),
          WContractification.PullbackProfinite.projSpec
            Γ(T, ⊤) E.left (componentBaseMap T E) x), by
          change T.isoSpec.hom.continuous.connectedComponentsMap
            (E'.hom (a.left (componentProjection T E x))) = _
          rw [show E'.hom (a.left (componentProjection T E x)) =
              E.hom (componentProjection T E x) from
            ConcreteCategory.congr_hom a.w (componentProjection T E x)]
          have hp := (WContractification.PullbackProfinite.fiberHomeo
            Γ(T, ⊤) E.left (componentBaseMap T E) x).2
          rw [WContractification.PullbackProfinite.fst_fiberHomeo,
            WContractification.PullbackProfinite.snd_fiberHomeo] at hp
          exact hp⟩ := by
  have hm := congrArg (fun f ↦ f x)
    (Algebra.BijectiveOnStalks.continuousMap_of_algHom_algHom_of_continuousMap
      Γ(T, ⊤) (componentAlgebra T E') (componentAlgebra T E) (componentContinuousMap a))
  change PrimeSpectrum.comap (componentAlgebraMap a).toRingHom x = _ at hm
  rw [hm]
  change (WContractification.PullbackProfinite.fiberHomeo
    Γ(T, ⊤) E'.left (componentBaseMap T E'))
      ((WContractification.PullbackProfinite.fiberHomeo
        Γ(T, ⊤) E'.left (componentBaseMap T E')).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact WContractification.PullbackProfinite.snd_fiberHomeo _ _ _ _

private noncomputable def componentProEtMap {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') :
    componentProEtObject T E ⟶ componentProEtObject T E' :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (componentAlgebraMap a).toRingHom)) (by
      change Spec.map _ ≫ (Spec.map _ ≫ T.isoSpec.inv) =
        Spec.map _ ≫ T.isoSpec.inv
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext r
      exact (componentAlgebraMap a).commutes r)

private theorem componentProEtMap_projection {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') (x : componentScheme T E) :
    componentProjection T E' ((componentProEtMap a).left x) =
      a.left (componentProjection T E x) := by
  have h := congrArg (fun z ↦ z.1.1) (componentAlgebraMap_comap a x)
  exact h

private theorem componentProEtMap_ext {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)}
    (f g : componentProEtObject T E ⟶ componentProEtObject T E')
    (h : ∀ x, componentProjection T E' (f.left x) =
      componentProjection T E' (g.left x)) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  obtain ⟨f', hf'⟩ := Spec.map_surjective f.left
  obtain ⟨g', hg'⟩ := Spec.map_surjective g.left
  have hf : ∀ r, f'.hom (algebraMap Γ(T, ⊤) (componentAlgebra T E') r) =
      algebraMap Γ(T, ⊤) (componentAlgebra T E) r := by
    have hw := f.w
    change f.left ≫ (Spec.map _ ≫ T.isoSpec.inv) = Spec.map _ ≫ T.isoSpec.inv at hw
    rw [← hf', ← Category.assoc, cancel_mono, ← Spec.map_comp] at hw
    have hr := Spec.map_injective hw
    exact fun r ↦ congrArg (fun k ↦ k.hom r) hr
  have hg : ∀ r, g'.hom (algebraMap Γ(T, ⊤) (componentAlgebra T E') r) =
      algebraMap Γ(T, ⊤) (componentAlgebra T E) r := by
    have hw := g.w
    change g.left ≫ (Spec.map _ ≫ T.isoSpec.inv) = Spec.map _ ≫ T.isoSpec.inv at hw
    rw [← hg', ← Category.assoc, cancel_mono, ← Spec.map_comp] at hw
    have hr := Spec.map_injective hw
    exact fun r ↦ congrArg (fun k ↦ k.hom r) hr
  let fa : componentAlgebra T E' →ₐ[Γ(T, ⊤)] componentAlgebra T E :=
    { f'.hom with commutes' := hf }
  let ga : componentAlgebra T E' →ₐ[Γ(T, ⊤)] componentAlgebra T E :=
    { g'.hom with commutes' := hg }
  have he : fa = ga :=
    (Algebra.BijectiveOnStalks.continuousMap_of_algHom_bijective
      Γ(T, ⊤) (componentAlgebra T E') (componentAlgebra T E)).1 (by
        apply Algebra.BijectiveOnStalks.HomOver.ext
        intro x
        apply (componentFiberHomeo T E').injective
        apply Subtype.ext
        apply Prod.ext
        · rw [componentFiberHomeo_fst, componentFiberHomeo_fst]
          change componentStructure T E' (Spec.map f' x) =
            componentStructure T E' (Spec.map g' x)
          rw [hf', hg']
          exact congrArg (fun k : componentScheme T E ⟶ T ↦ k x) (f.w.trans g.w.symm)
        · change componentProjection T E' (Spec.map f' x) =
            componentProjection T E' (Spec.map g' x)
          rw [hf', hg']
          exact h x)
  have he' : f' = g' := CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
  rw [← hf', ← hg', he']

private noncomputable def componentFunctor (T : Scheme.{u}) [IsAffine T] :
    Over (componentProfinite T) ⥤ T.ProEt where
  obj := componentProEtObject T
  map := componentProEtMap
  map_id E := by
    apply componentProEtMap_ext
    intro x
    exact componentProEtMap_projection (𝟙 E) x
  map_comp a b := by
    apply componentProEtMap_ext
    intro x
    rw [componentProEtMap_projection]
    change b.left (a.left (componentProjection T _ x)) =
      componentProjection T _ ((componentProEtMap b).left ((componentProEtMap a).left x))
    rw [componentProEtMap_projection, componentProEtMap_projection]

-- First establish the scheme mapping property on affine sources, then glue.
private theorem component_affine_lift {T W : Scheme.{u}} [IsAffine T] [IsAffine W]
    (f : W ⟶ T) (E : Over (componentProfinite T)) (r : C(W, E.left))
    (hr : ∀ x, ConnectedComponents.mk (f x) = E.hom (r x)) :
    ∃ g : W ⟶ componentScheme T E,
      g ≫ componentStructure T E = f ∧ ∀ x, componentProjection T E (g x) = r x := by
  let : Algebra Γ(T, ⊤) Γ(W, ⊤) := f.appTop.hom.toAlgebra
  let e := Scheme.homeoOfIso W.isoSpec
  let h := componentFiberHomeo T E
  let m : C(Spec Γ(W, ⊤), componentScheme T E) :=
    ⟨fun x ↦ h.symm ⟨(f (e.symm x), r (e.symm x)), hr (e.symm x)⟩,
      h.symm.continuous.comp
        (((f.continuous.comp e.symm.continuous).prodMk
          (r.continuous.comp e.symm.continuous)).subtype_mk _)⟩
  let φ : Algebra.BijectiveOnStalks.HomOver Γ(T, ⊤)
      (componentAlgebra T E) Γ(W, ⊤) :=
    { toContinuousMap := m
      comp_comap_algebraMap x := by
        apply (Scheme.homeoOfIso T.isoSpec).symm.injective
        change componentStructure T E (m x) =
          T.isoSpec.inv (Spec.map f.appTop x)
        rw [← componentFiberHomeo_fst]
        change (h (h.symm _)).1.1 = _
        rw [h.apply_symm_apply]
        exact (congrArg (fun k : Spec Γ(W, ⊤) ⟶ T ↦ k x)
          (Scheme.isoSpec_inv_naturality f)).symm }
  obtain ⟨a, ha⟩ := (component_algHom_bijective Γ(T, ⊤)
    (componentAlgebra T E) Γ(W, ⊤)).2 φ
  refine ⟨W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom a.toRingHom), ?_, ?_⟩
  · dsimp only [componentStructure]
    rw [Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp]
    have hac : CommRingCat.ofHom (algebraMap Γ(T, ⊤) (componentAlgebra T E)) ≫
        CommRingCat.ofHom a.toRingHom = f.appTop := by
      ext x
      exact a.commutes x
    rw [hac, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  · intro x
    have hx := DFunLike.congr_fun ha (W.isoSpec.hom x)
    change PrimeSpectrum.comap a.toRingHom (W.isoSpec.hom x) = m (W.isoSpec.hom x) at hx
    change componentProjection T E (Spec.map (CommRingCat.ofHom a.toRingHom)
      (W.isoSpec.hom x)) = r x
    change componentProjection T E (PrimeSpectrum.comap a.toRingHom
      (W.isoSpec.hom x)) = r x
    rw [hx, ← componentFiberHomeo_snd]
    change (h (h.symm _)).1.2 = r x
    rw [h.apply_symm_apply]
    exact congrArg r (e.symm_apply_apply x)

private theorem component_affine_ext {T W : Scheme.{u}} [IsAffine T] [IsAffine W]
    (E : Over (componentProfinite T)) (f g : W ⟶ componentScheme T E)
    (hb : f ≫ componentStructure T E = g ≫ componentStructure T E)
    (hr : ∀ x, componentProjection T E (f x) = componentProjection T E (g x)) :
    f = g := by
  let f₀ := f ≫ componentStructure T E
  let : Algebra Γ(T, ⊤) Γ(W, ⊤) := f₀.appTop.hom.toAlgebra
  obtain ⟨f', hf'⟩ := Spec.map_surjective (W.isoSpec.inv ≫ f)
  obtain ⟨g', hg'⟩ := Spec.map_surjective (W.isoSpec.inv ≫ g)
  have hc (k : CommRingCat.of (componentAlgebra T E) ⟶ Γ(W, ⊤))
      (a : W ⟶ componentScheme T E) (hk : Spec.map k = W.isoSpec.inv ≫ a)
      (ha : a ≫ componentStructure T E = f₀) :
      ∀ r, k.hom (algebraMap Γ(T, ⊤) (componentAlgebra T E) r) =
        algebraMap Γ(T, ⊤) Γ(W, ⊤) r := by
    have he : CommRingCat.ofHom (algebraMap Γ(T, ⊤) (componentAlgebra T E)) ≫ k =
        f₀.appTop := by
      apply Spec.map_injective
      rw [Spec.map_comp, hk, ← cancel_mono T.isoSpec.inv]
      change (W.isoSpec.inv ≫ a) ≫ componentStructure T E = _
      rw [Category.assoc, ha, ← Scheme.isoSpec_inv_naturality]
    exact fun r ↦ congrArg (fun k ↦ k.hom r) he
  let fa : componentAlgebra T E →ₐ[Γ(T, ⊤)] Γ(W, ⊤) :=
    { f'.hom with commutes' := hc f' f hf' rfl }
  let ga : componentAlgebra T E →ₐ[Γ(T, ⊤)] Γ(W, ⊤) :=
    { g'.hom with commutes' := hc g' g hg' hb.symm }
  have he : fa = ga := (component_algHom_bijective Γ(T, ⊤)
      (componentAlgebra T E) Γ(W, ⊤)).1 (by
    apply Algebra.BijectiveOnStalks.HomOver.ext
    intro x
    apply (componentFiberHomeo T E).injective
    apply Subtype.ext
    apply Prod.ext
    · rw [componentFiberHomeo_fst, componentFiberHomeo_fst]
      change componentStructure T E (Spec.map f' x) =
        componentStructure T E (Spec.map g' x)
      rw [hf', hg']
      exact congrArg (fun k : W ⟶ T ↦ k (W.isoSpec.inv x)) hb
    · change componentProjection T E (Spec.map f' x) =
        componentProjection T E (Spec.map g' x)
      rw [hf', hg']
      exact hr (W.isoSpec.inv x))
  have he' : f' = g' := CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
  apply (cancel_epi W.isoSpec.inv).mp
  rw [← hf', ← hg', he']

private theorem component_scheme_ext {T W : Scheme.{u}} [IsAffine T]
    (E : Over (componentProfinite T)) (f g : W ⟶ componentScheme T E)
    (hb : f ≫ componentStructure T E = g ≫ componentStructure T E)
    (hr : ∀ x, componentProjection T E (f x) = componentProjection T E (g x)) :
    f = g := by
  apply W.affineCover.hom_ext
  intro i
  apply component_affine_ext E
  · simpa only [Category.assoc] using congrArg (fun k ↦ W.affineCover.f i ≫ k) hb
  · exact fun x ↦ hr (W.affineCover.f i x)

private theorem component_scheme_lift {T W : Scheme.{u}} [IsAffine T]
    (f : W ⟶ T) (E : Over (componentProfinite T)) (r : C(W, E.left))
    (hr : ∀ x, ConnectedComponents.mk (f x) = E.hom (r x)) :
    ∃ g : W ⟶ componentScheme T E,
      g ≫ componentStructure T E = f ∧ ∀ x, componentProjection T E (g x) = r x := by
  choose a ha hb using fun i ↦ component_affine_lift (W.affineCover.f i ≫ f) E
    (r.comp ⟨W.affineCover.f i, (W.affineCover.f i).continuous⟩)
    (fun x ↦ hr (W.affineCover.f i x))
  have hc : ∀ i j, pullback.fst (W.affineCover.f i) (W.affineCover.f j) ≫ a i =
      pullback.snd (W.affineCover.f i) (W.affineCover.f j) ≫ a j := by
    intro i j
    apply component_scheme_ext E
    · rw [Category.assoc, ha i, Category.assoc, ha j,
        ← Category.assoc, pullback.condition, Category.assoc]
    · intro x
      change componentProjection T E
        (a i (pullback.fst (W.affineCover.f i) (W.affineCover.f j) x)) =
        componentProjection T E
          (a j (pullback.snd (W.affineCover.f i) (W.affineCover.f j) x))
      rw [hb, hb]
      exact congrArg r (congrArg
        (fun k : pullback (W.affineCover.f i) (W.affineCover.f j) ⟶ W ↦ k x)
        (pullback.condition (f := W.affineCover.f i) (g := W.affineCover.f j)))
  refine ⟨W.affineCover.glueMorphisms a hc, ?_, ?_⟩
  · apply W.affineCover.hom_ext
    intro i
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, ha]
  · intro x
    obtain ⟨i, y, rfl⟩ := W.affineCover.exists_eq x
    have he := congrArg (fun k ↦ k y) (W.affineCover.ι_glueMorphisms a hc i)
    change componentProjection T E ((W.affineCover.f i ≫
      W.affineCover.glueMorphisms a hc) y) = r (W.affineCover.f i y)
    rw [he]
    exact hb i y

-- Continuous lifts represent the same Hom functor even for non-qcqs sources.
private noncomputable def componentTopObject (T : Scheme.{u}) [IsAffine T]
    (W : T.ProEt) : Over (TopCat.of (componentProfinite T)) :=
  Over.mk (TopCat.ofHom ⟨fun x ↦ ConnectedComponents.mk (W.hom x),
    ConnectedComponents.continuous_coe.comp W.hom.continuous⟩)

private noncomputable def componentTopHom {T : Scheme.{u}} [IsAffine T]
    (W : T.ProEt) (E : Over (componentProfinite T))
    (a : W ⟶ (componentFunctor T).obj E) :
    componentTopObject T W ⟶ (Over.post Profinite.toTopCat).obj E :=
  Over.homMk (TopCat.ofHom ((componentProjection T E).comp ⟨a.left, a.left.continuous⟩)) (by
    ext x
    have hp := (componentFiberHomeo T E (a.left x)).2
    change ConnectedComponents.mk (componentFiberHomeo T E (a.left x)).1.1 =
      E.hom (componentFiberHomeo T E (a.left x)).1.2 at hp
    rw [componentFiberHomeo_fst, componentFiberHomeo_snd] at hp
    exact hp.symm.trans (congrArg ConnectedComponents.mk
      (congrArg (fun k : W.left ⟶ T ↦ k x) a.w)))

private noncomputable def componentTopEquiv {T : Scheme.{u}} [IsAffine T]
    (W : T.ProEt) (E : Over (componentProfinite T)) :
    (W ⟶ (componentFunctor T).obj E) ≃
      (componentTopObject T W ⟶ (Over.post Profinite.toTopCat).obj E) :=
  Equiv.ofBijective (componentTopHom W E) (by
    constructor
    · intro a b hab
      apply MorphismProperty.Over.Hom.ext
      apply component_scheme_ext E a.left b.left (a.w.trans b.w.symm)
      exact fun x ↦ ConcreteCategory.congr_hom (congrArg Over.Hom.left hab) x
    · intro a
      obtain ⟨g, hg, hr⟩ := component_scheme_lift (T := T) (W := W.left) W.hom E a.left.hom (by
        intro x
        exact (ConcreteCategory.congr_hom a.w x).symm)
      refine ⟨MorphismProperty.Over.homMk g hg, ?_⟩
      apply Over.OverMorphism.ext
      ext x
      exact hr x)

private theorem componentTopEquiv_natural {T : Scheme.{u}} [IsAffine T]
    (W : T.ProEt) {E E' : Over (componentProfinite T)} (a : E ⟶ E')
    (b : W ⟶ (componentFunctor T).obj E) :
    componentTopEquiv W E' (b ≫ (componentFunctor T).map a) =
      componentTopEquiv W E b ≫ (Over.post Profinite.toTopCat).map a := by
  apply Over.OverMorphism.ext
  ext x
  exact componentProEtMap_projection a (b.left x)

private noncomputable def componentHomIso (T : Scheme.{u}) [IsAffine T]
    (W : T.ProEt) :
    componentFunctor T ⋙ coyoneda.obj (op W) ≅
      Over.post Profinite.toTopCat ⋙ coyoneda.obj (op (componentTopObject T W)) :=
  NatIso.ofComponents (fun E ↦ (componentTopEquiv W E).toIso) (by
    intro E E' a
    ext b
    exact componentTopEquiv_natural W a b)

private theorem componentFunctor_finiteLimits (T : Scheme.{u}) [IsAffine T] :
    PreservesFiniteLimits (componentFunctor T) := by
  constructor
  intro J _ _
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨?_⟩
  apply coyonedaJointlyReflectsLimits
  intro W
  exact (IsLimit.mapConeEquiv (componentHomIso T W.unop).symm
    (isLimitOfPreserves
      (Over.post Profinite.toTopCat ⋙ coyoneda.obj (op (componentTopObject T W.unop))) hc))

private theorem componentStructure_indEtale (T : Scheme.{u}) [IsAffine T]
    (E : Over (componentProfinite T)) :
    RingHom.IndEtaleAcrossUniverses (componentStructure T E).appTop.hom := by
  have hr : RingHom.RespectsIso RingHom.IndEtale :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  have hi : (algebraMap Γ(T, ⊤) (componentAlgebra T E)).IndEtale :=
    (RingHom.IndEtale.algebraMap_iff Γ(T, ⊤) (componentAlgebra T E)).mpr inferInstance
  have hp : (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, ⊤) (componentAlgebra T E)))).appTop.hom.IndEtale := by
    rw [RingHom.IndEtale.iff_ind_etale] at hi ⊢
    exact ((MorphismProperty.ind CommRingCat.etale).arrow_mk_iso_iff
      (arrowIsoΓSpecOfIsAffine _)).mp hi
  have ht : (componentStructure T E).appTop.hom.IndEtale := by
    dsimp only [componentStructure]
    rw [Scheme.Hom.comp_appTop]
    exact (hr.cancel_left_isIso T.isoSpec.inv.appTop _).mpr hp
  exact hr.1 _ ULift.ringEquiv.symm (hr.2 _ ULift.ringEquiv ht)

private theorem component_map_weaklyEtale {T : Scheme.{u}} [IsAffine T]
    {E E' : Over (componentProfinite T)} (a : E ⟶ E') :
    WeaklyEtale ((componentFunctor T).map a).left := by
  apply MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
    ((componentFunctor T).map a).left (componentStructure T E')
  · exact componentStructure_weaklyEtale T E'
  · rw [show ((componentFunctor T).map a).left ≫ componentStructure T E' =
        componentStructure T E from ((componentFunctor T).map a).w]
    exact componentStructure_weaklyEtale T E

private theorem component_joint_surjective {T : Scheme.{u}} [IsAffine T]
    {I : Type v} (E : I → Over (componentProfinite T)) (E' : Over (componentProfinite T))
    (a : ∀ i, E i ⟶ E') (ha : ∀ e : E'.left, ∃ i x, (a i).left x = e) :
    ∀ x : componentScheme T E', ∃ i y, ((componentFunctor T).map (a i)).left y = x := by
  intro x
  obtain ⟨i, e, he⟩ := ha (componentProjection T E' x)
  have hp : ConnectedComponents.mk (componentStructure T E' x) = (E i).hom e := by
    have hp := (componentFiberHomeo T E' x).2
    change ConnectedComponents.mk (componentFiberHomeo T E' x).1.1 =
      E'.hom (componentFiberHomeo T E' x).1.2 at hp
    rw [componentFiberHomeo_fst, componentFiberHomeo_snd, ← he] at hp
    exact hp.trans (ConcreteCategory.congr_hom (a i).w e)
  let y := (componentFiberHomeo T (E i)).symm ⟨(componentStructure T E' x, e), hp⟩
  refine ⟨i, y, ?_⟩
  apply (componentFiberHomeo T E').injective
  apply Subtype.ext
  apply Prod.ext
  · rw [componentFiberHomeo_fst, componentFiberHomeo_fst]
    have hw := congrArg (fun k : componentScheme T (E i) ⟶ T ↦ k y)
      ((componentFunctor T).map (a i)).w
    change componentStructure T E' (((componentFunctor T).map (a i)).left y) =
      componentStructure T (E i) y at hw
    rw [hw, ← componentFiberHomeo_fst]
    exact congrArg (fun z ↦ z.1.1) ((componentFiberHomeo T (E i)).apply_symm_apply _)
  · rw [componentFiberHomeo_snd, componentFiberHomeo_snd]
    change componentProjection T E' ((componentProEtMap (a i)).left y) = _
    rw [componentProEtMap_projection, ← he]
    congr 1
    rw [← componentFiberHomeo_snd]
    exact congrArg (fun z ↦ z.1.2) ((componentFiberHomeo T (E i)).apply_symm_apply _)

private theorem component_cover {T : Scheme.{u}} [IsAffine T]
    {I : Type v} [Finite I] (E : I → Over (componentProfinite T))
    (E' : Over (componentProfinite T)) (a : ∀ i, E i ⟶ E')
    (ha : ∀ e : E'.left, ∃ i x, (a i).left x = e) :
    Presieve.ofArrows (fun i ↦ (componentFunctor T).obj (E i))
      (fun i ↦ (componentFunctor T).map (a i)) ∈
        precoverage T ((componentFunctor T).obj E') := by
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  let V : (componentScheme T E').Cover (Scheme.precoverage @WeaklyEtale) :=
    { I₀ := I
      X i := componentScheme T (E i)
      f i := ((componentFunctor T).map (a i)).left
      mem₀ := (Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨component_joint_surjective E E' a ha, fun i ↦ component_map_weaklyEtale (a i)⟩ }
  have : Finite V.I₀ := inferInstanceAs (Finite I)
  have : ∀ i, QuasiCompact (V.f i) := fun i ↦ by
    change QuasiCompact (Spec.map (CommRingCat.ofHom
      (componentAlgebraMap (a i)).toRingHom))
    infer_instance
  have : QuasiCompactCover V.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr this, V.mem₀⟩

private theorem component_coverPreserving (T : Scheme.{u}) [IsAffine T] :
    CoverPreserving ((coherentTopology Profinite.{u}).over (componentProfinite T))
      (topology T) (componentFunctor T) := by
  constructor
  intro E R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨I, hI, V, f, hf, hm⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hR
  let E₀ : I → Over (componentProfinite T) := fun i ↦ Over.mk (f i ≫ E.hom)
  let a : ∀ i, E₀ i ⟶ E := fun i ↦ Over.homMk (f i) rfl
  have hjs : ∀ e : E.left, ∃ i x, (a i).left x = e :=
    ((Profinite.effectiveEpiFamily_tfae V f).out 1 3).mp hf
  have hc := component_cover E₀ E a hjs
  apply (topology T).superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hc)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W g hg
  obtain ⟨i⟩ := hg
  exact ⟨E₀ i, a i, 𝟙 _, (Sieve.overEquiv_iff R (f i)).mp (hm i),
    (Category.id_comp _).symm⟩

private theorem component_continuous (T : Scheme.{u}) [IsAffine T] :
    (componentFunctor T).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) := by
  let := componentFunctor_finiteLimits T
  let : RepresentablyFlat (componentFunctor T) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (component_coverPreserving T)

private noncomputable def componentFactor {T : Scheme.{u}} [IsAffine T]
    (W : Qcqs T) (E : Over (componentProfinite T))
    (a : W.obj ⟶ (componentFunctor T).obj E) : componentObject T W ⟶ E := by
  let r := (componentProjection T E).comp ⟨a.left, a.left.continuous⟩
  refine Over.homMk (ConcreteCategory.ofHom
    ⟨r.continuous.connectedComponentsLift,
      r.continuous.connectedComponentsLift_continuous⟩) ?_
  ext z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  exact ConcreteCategory.congr_hom (componentTopHom W.obj E a).w x

private theorem componentFactor_apply {T : Scheme.{u}} [IsAffine T]
    (W : Qcqs T) (E : Over (componentProfinite T))
    (a : W.obj ⟶ (componentFunctor T).obj E) (x : W.obj.left) :
    (componentFactor W E a).left (ConnectedComponents.mk x) =
      componentProjection T E (a.left x) := rfl

private noncomputable def componentFactorEquiv {T : Scheme.{u}} [IsAffine T]
    (W : Qcqs T) (E : Over (componentProfinite T)) :
    (W.obj ⟶ (componentFunctor T).obj E) ≃ (componentObject T W ⟶ E) :=
  Equiv.ofBijective (componentFactor W E) (by
    constructor
    · intro a b hab
      apply (componentTopEquiv W.obj E).injective
      apply Over.OverMorphism.ext
      ext x
      exact ConcreteCategory.congr_hom (congrArg Over.Hom.left hab) (ConnectedComponents.mk x)
    · intro a
      let t : componentTopObject T W.obj ⟶ (Over.post Profinite.toTopCat).obj E :=
        Over.homMk (TopCat.ofHom ⟨fun x ↦ a.left (ConnectedComponents.mk x),
          a.left.hom.hom.continuous.comp ConnectedComponents.continuous_coe⟩) (by
            ext x
            exact ConcreteCategory.congr_hom a.w (ConnectedComponents.mk x))
      obtain ⟨b, hb⟩ := (componentTopEquiv W.obj E).surjective t
      refine ⟨b, ?_⟩
      apply Over.OverMorphism.ext
      ext z
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
      exact ConcreteCategory.congr_hom (congrArg Over.Hom.left hb) x)

private theorem componentFactor_natural {T : Scheme.{u}} [IsAffine T]
    (W : Qcqs T) {E E' : Over (componentProfinite T)} (a : E ⟶ E')
    (b : W.obj ⟶ (componentFunctor T).obj E) :
    componentFactor W E' (b ≫ (componentFunctor T).map a) = componentFactor W E b ≫ a := by
  apply Over.OverMorphism.ext
  ext z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  exact componentProEtMap_projection a (b.left x)

private theorem componentFactor_source {T : Scheme.{u}} [IsAffine T]
    {V W : Qcqs T} (a : V ⟶ W) (E : Over (componentProfinite T))
    (b : W.obj ⟶ (componentFunctor T).obj E) :
    componentFactor V E (a.hom ≫ b) = componentObjectMap a ≫ componentFactor W E b := by
  apply Over.OverMorphism.ext
  ext z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  rfl

private def kanTerminal {A B : Type*} [Category* A] [Category* B]
    (L : A ⥤ B) (U : B) (T : A)
    (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
    (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
      b S' (f ≫ L.map g) = b S f ≫ g) :
    IsTerminal (CostructuredArrow.mk ((b T).symm (𝟙 T)).op :
      CostructuredArrow L.op (op U)) := by
  let q := (b T).symm (𝟙 T)
  have hq : b T q = 𝟙 T := (b T).apply_symm_apply _
  refine IsTerminal.ofUniqueHom (fun s ↦
    CostructuredArrow.homMk (b s.left.unop s.hom.unop).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change q ≫ L.map (b _ s.hom.unop) = s.hom.unop
    apply (b _).injective
    rw [hb, hq, Category.id_comp]
  · intro s m
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    have hm : q ≫ L.map m.left.unop = s.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w m)
    have := congrArg (b s.left.unop) hm
    change m.left.unop = b s.left.unop s.hom.unop
    simpa only [hb, hq, Category.id_comp] using this

set_option backward.isDefEq.respectTransparency false in
private theorem kanEvaluation {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (L : A ⥤ B) (U : B) (T : A)
    (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
    (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
      b S' (f ≫ L.map g) = b S f ≫ g)
    (F : Aᵒᵖ ⥤ C) (P : Bᵒᵖ ⥤ C) (η : F ⟶ L.op ⋙ P)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension) :
    ∃ e : P.obj (op U) ≅ F.obj (op T),
      ∀ (S : A) (f : U ⟶ L.obj S),
        η.app (op S) ≫ P.map f.op ≫ e.hom = F.map (b S f).op := by
  let t : CostructuredArrow L.op (op U) :=
    CostructuredArrow.mk ((b T).symm (𝟙 T)).op
  let ht : IsTerminal t := kanTerminal L U T b hb
  let c := (Functor.LeftExtension.mk P η).coconeAt (op U)
  have : IsIso (c.ι.app t) := (hP (op U)).isIso_ι_app_of_isTerminal t ht
  refine ⟨(asIso (c.ι.app t)).symm, ?_⟩
  intro S f
  let s : CostructuredArrow L.op (op U) := CostructuredArrow.mk f.op
  have h := c.w (ht.from s)
  change η.app (op S) ≫ P.map f.op ≫ inv (c.ι.app t) = _
  have hm : (ht.from s).left = (b S f).op := rfl
  change F.map (ht.from s).left ≫ c.ι.app t = η.app (op S) ≫ P.map f.op at h
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hm]

-- A sheaf on the coherent slice carries finite coproducts to products.
private instance component_slice_extensive (P : Profinite.{u}) :
    FinitaryExtensive (Over P) := by
  let : HasFiniteCoproducts Profinite.{u} :=
    ⟨fun n ↦ inferInstanceAs (HasColimitsOfShape (Discrete (Fin n)) Profinite.{u})⟩
  let : FinitaryExtensive Profinite.{u} := inferInstance
  let : HasFiniteCoproducts (Over P) := inferInstance
  let : HasPullbacks (Over P) := inferInstance
  let : PreservesColimitsOfShape (Discrete WalkingPair) (Over.forget P) := inferInstance
  exact finitaryExtensive_of_preserves_and_reflects_isomorphism
    (C := Over P) (D := Profinite.{u}) (Over.forget P)

private theorem component_slice_extensiveTopology (P : Profinite.{u}) :
    extensiveTopology (Over P) ≤ (coherentTopology Profinite.{u}).over P := by
  let := component_slice_extensive P
  intro E S hS
  obtain ⟨I, hI, V, a, ⟨hc⟩, ha⟩ :=
    (extensiveTopology.mem_sieves_iff_contains_colimit_cofan S).mp hS
  have hc' : IsColimit (Cofan.mk E.left (fun i ↦ (a i).left)) :=
    (Cofan.isColimitMapCoconeEquiv (Over.forget P) _ _)
      (isColimitOfPreserves (Over.forget P) hc)
  have hi : IsIso (Sigma.desc (fun i ↦ (a i).left)) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨hc'⟩
  have hef : EffectiveEpiFamily (fun i ↦ (V i).left) (fun i ↦ (a i).left) :=
    (effectiveEpi_desc_iff_effectiveEpiFamily _ _).mp inferInstance
  rw [GrothendieckTopology.mem_over_iff]
  apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  refine ⟨I, hI, fun i ↦ (V i).left, fun i ↦ (a i).left, hef, ?_⟩
  intro i
  exact ⟨V i, a i, 𝟙 _, ha i, (Category.id_comp _).symm⟩

private theorem component_sheaf_products (P : Profinite.{u}) (C : Type w)
    [Category.{v} C] (F : Sheaf ((coherentTopology Profinite.{u}).over P) C) :
    PreservesFiniteProducts F.obj := by
  let := component_slice_extensive P
  apply (Presheaf.isSheaf_iff_preservesFiniteProducts F.obj).mp
  exact F.property.of_le (component_slice_extensiveTopology P)

set_option backward.isDefEq.respectTransparency false in
private theorem component_finite_products (X : Scheme.{u}) [IsAffine X]
    (C : Type w) [Category.{v} C]
    (F : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite X)) C)
    (P : X.ProEtᵒᵖ ⥤ C) (η : F.obj ⟶ (componentFunctor X).op ⋙ P)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (I : Type u) [Finite I] (V : I → Qcqs X) :
    ∃ c : Cofan (fun i ↦ (V i).obj), Nonempty (IsColimit c) ∧
      Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op))) := by
  classical
  let U : I → X.ProEt := fun i ↦ (V i).obj
  -- Combine the summand equivalences using the two coproduct universal properties.
  let coproductMapEquiv
      (L : Over (componentProfinite X) ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Over (componentProfinite X)) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S)) (S : Over (componentProfinite X)) :
      (c.pt ⟶ L.obj S) ≃ (∐ T ⟶ S) := by
    exact
      { toFun := fun f ↦ Sigma.desc (fun i ↦ b i S (c.inj i ≫ f))
        invFun := fun g ↦ Cofan.IsColimit.desc hc (fun i ↦ (b i S).symm (Sigma.ι T i ≫ g))
        left_inv := fun f ↦ by
          apply Cofan.IsColimit.hom_ext hc
          intro i
          simp
        right_inv := fun g ↦ by
          apply Sigma.hom_ext
          intro i
          simp }
  have coproductMapEquiv_inj
      (L : Over (componentProfinite X) ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Over (componentProfinite X)) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S)) (S : Over (componentProfinite X))
      (f : c.pt ⟶ L.obj S) (i : I) :
      Sigma.ι T i ≫ coproductMapEquiv L U c hc T b S f = b i S (c.inj i ≫ f) := by
    exact Sigma.ι_comp_desc _ _
  have coproductMapEquiv_natural
      (L : Over (componentProfinite X) ⥤ X.ProEt)
      {I : Type u} (U : I → X.ProEt) (c : Cofan U) (hc : IsColimit c)
      (T : I → Over (componentProfinite X)) [HasCoproduct T]
      (b : ∀ i S, (U i ⟶ L.obj S) ≃ (T i ⟶ S))
      (hb : ∀ i S S' (g : S ⟶ S') (f : U i ⟶ L.obj S),
        b i S' (f ≫ L.map g) = b i S f ≫ g)
      (S S' : Over (componentProfinite X)) (g : S ⟶ S') (f : c.pt ⟶ L.obj S) :
      coproductMapEquiv L U c hc T b S' (f ≫ L.map g) =
        coproductMapEquiv L U c hc T b S f ≫ g := by
    apply Sigma.hom_ext
    intro i
    simp only [coproductMapEquiv, Equiv.coe_fn_mk, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    rw [← Category.assoc, hb]
  -- Construct the coproduct in the slice using descent on the scheme coproduct.
  let f : (∐ fun i ↦ (U i).left) ⟶ X := Sigma.desc (fun i ↦ (U i).hom)
  have hf : WeaklyEtale f :=
    IsZariskiLocalAtSource.sigmaDesc (fun i ↦ (U i).prop)
  let W : X.ProEt := Scheme.ProEt.mk f
  let ι : ∀ i, U i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (U i).left) i)
      (by dsimp [W]; simp [f])
  let c : Cofan U := Cofan.mk W ι
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun t ↦
      MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (t.inj i).left)) ?_) ?_ ?_
    · change Sigma.desc (fun i ↦ (t.inj i).left) ≫ t.pt.hom = f
      apply Sigma.hom_ext
      intro i
      simp [f, ← Category.assoc]
    · intro t i
      apply MorphismProperty.Over.Hom.ext
      exact Sigma.ι_comp_desc _ _
    · intro t m hm
      apply MorphismProperty.Over.Hom.ext
      apply Sigma.hom_ext
      intro i
      have h := congrArg (fun z ↦ z.left) (hm i)
      change Sigma.ι (fun i ↦ (U i).left) i ≫ m.left = (t.inj i).left at h
      simpa using h
  let T (i : I) : Over (componentProfinite X) := componentObject X (V i)
  let b (i : I) (S : Over (componentProfinite X)) :
      (U i ⟶ (componentFunctor X).obj S) ≃ (T i ⟶ S) := componentFactorEquiv (V i) S
  have hb (i : I) (S S' : Over (componentProfinite X)) (g : S ⟶ S')
      (f : U i ⟶ (componentFunctor X).obj S) :
      b i S' (f ≫ (componentFunctor X).map g) = b i S f ≫ g :=
    componentFactor_natural (V i) g f
  let bW := coproductMapEquiv (componentFunctor X) U c hc T b
  have hbW := coproductMapEquiv_natural (componentFunctor X) U c hc T b hb
  obtain ⟨eW, heW⟩ := kanEvaluation (componentFunctor X) W (∐ T) bW hbW F.obj P η hP
  have hi (i : I) := kanEvaluation (componentFunctor X) (U i) (T i) (b i) (hb i)
    F.obj P η hP
  choose ei hei using hi
  -- Kan cocone legs jointly detect the comparison with each summand restriction.
  have hcompat (i : I) : P.map (c.inj i).op ≫ (ei i).hom =
      eW.hom ≫ F.obj.map (Sigma.ι T i).op := by
    apply (hP (op W)).hom_ext'
    intro S f
    cases S with | op S =>
      change η.app (op S) ≫ P.map f ≫ (P.map (c.inj i).op ≫ (ei i).hom) =
        η.app (op S) ≫ P.map f ≫ (eW.hom ≫ F.obj.map (Sigma.ι T i).op)
      calc
        _ = η.app (op S) ≫ P.map (c.inj i ≫ f.unop).op ≫ (ei i).hom := by
          simp only [op_comp, P.map_comp, Quiver.Hom.op_unop, Category.assoc]
        _ = F.obj.map (b i S (c.inj i ≫ f.unop)).op := hei i S _
        _ = F.obj.map (bW S f.unop).op ≫ F.obj.map (Sigma.ι T i).op := by
          rw [← F.obj.map_comp, ← op_comp, coproductMapEquiv_inj]
        _ = _ := by
          have h := heW S f.unop
          change η.app (op S) ≫ P.map f ≫ eW.hom = F.obj.map (bW S f.unop).op at h
          rw [← h]
          simp only [Category.assoc]
  -- Transport the product preserved by the coherent sheaf through the evaluation isos.
  have : PreservesFiniteProducts F.obj := component_sheaf_products _ C F
  let d := Fan.mk (F.obj.obj (op (∐ T))) (fun i ↦ F.obj.map (Sigma.ι T i).op)
  have hd : IsLimit d := isLimitFanMkObjOfIsLimit F.obj (fun i ↦ op (T i)) _
    (Cofan.IsColimit.op (coproductIsCoproduct T))
  refine ⟨c, ⟨hc⟩, ⟨?_⟩⟩
  refine Fan.IsLimit.mk _ (fun s ↦
    Fan.IsLimit.lift hd (fun i ↦ s.proj i ≫ (ei i).hom) ≫ eW.inv) ?_ ?_
  · intro s i
    apply (cancel_mono (ei i).hom).mp
    change ((Fan.IsLimit.lift hd (fun i ↦ s.proj i ≫ (ei i).hom) ≫ eW.inv) ≫
      P.map (c.inj i).op) ≫ (ei i).hom = _
    simp only [Category.assoc, hcompat, Iso.inv_hom_id_assoc]
    exact Fan.IsLimit.fac hd _ i
  · intro s m hm
    apply (cancel_mono eW.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Fan.IsLimit.hom_ext hd
    intro i
    rw [Fan.IsLimit.fac]
    change (m ≫ eW.hom) ≫ F.obj.map (Sigma.ι T i).op = _
    rw [Category.assoc, ← hcompat, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ (ei i).hom) (hm i)

set_option backward.isDefEq.respectTransparency false in
private theorem component_finite_refinement (X : Scheme.{u}) (U : Qcqs X)
    (S : Sieve U.obj) (hS : S ∈ topology X U.obj) :
    ∃ (n : ℕ) (V : Fin n → Qcqs X) (f : ∀ i, (V i).obj ⟶ U.obj),
      Presieve.ofArrows (fun i ↦ (V i).obj) f ∈ precoverage X U.obj ∧ ∀ i, S (f i) := by
  classical
  let : CompactSpace U.obj.left := U.property.1
  let : QuasiSeparatedSpace U.obj.left := U.property.2
  obtain ⟨P, hP, hPS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (Scheme.ProEt.mem_precoverage_iff.1 hP)
  have hmem (i : 𝒰.I₀) :
      P.map (ProEt.forget X ⋙ Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  obtain ⟨𝒱, g, hfin, _⟩ := AlgebraicGeometry.QuasiCompactCover.exists_hom.{u + 1, u} 𝒰
  let : Finite 𝒱.I₀ := hfin
  let : Finite 𝒱.cover.I₀ := inferInstanceAs (Finite 𝒱.I₀)
  have (j : 𝒱.I₀) : QuasiCompact (𝒱.f j) := by infer_instance
  let : QuasiCompactCover 𝒱.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
  let e : Fin (Nat.card 𝒱.I₀) ≃ 𝒱.I₀ := (Finite.equivFin 𝒱.I₀).symm
  have (j : 𝒱.I₀) : WeaklyEtale (𝒱.f j) := 𝒱.map_prop j
  let V (j : Fin (Nat.card 𝒱.I₀)) : Qcqs X :=
    ⟨ProEt.mk (𝒱.f (e j) ≫ U.obj.hom),
      inferInstanceAs (CompactSpace (Spec (𝒱.X (e j)))),
      inferInstanceAs (QuasiSeparatedSpace (Spec (𝒱.X (e j))))⟩
  let f (j : Fin (Nat.card 𝒱.I₀)) : (V j).obj ⟶ U.obj :=
    MorphismProperty.Over.homMk (𝒱.f (e j))
  refine ⟨_, V, f, ?_, ?_⟩
  · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows (fun j ↦ Spec (𝒱.X (e j)))
      (fun j ↦ 𝒱.f (e j)) ∈ Scheme.proetalePrecoverage U.obj.left
    have hh := Presieve.ofArrows_comp_eq_of_surjective
      (fun j ↦ 𝒱.f j) (a := fun j ↦ e j) e.surjective
    exact hh.symm ▸ 𝒱.cover.ofQuasiCompactCover.mem₀
  · intro j
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : (V j).obj.left ⟶ (Z (g.s₀ (e j))).left :=
      g.h₀ (e j) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (e j))).left = (f j).left := by
      dsimp [d]
      rw [ha']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact g.w₀ (e j)
    have hf : f j = MorphismProperty.Over.homMk d (by
        calc
          d ≫ (Z (g.s₀ (e j))).hom = d ≫ (a (g.s₀ (e j))).left ≫ U.obj.hom := by
            rw [MorphismProperty.Over.w]
          _ = (f j).left ≫ U.obj.hom := by rw [← Category.assoc, hd]
          _ = (V j).obj.hom := MorphismProperty.Over.w (f j)) ≫ a (g.s₀ (e j)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hf]
    exact S.downward_closed (hPS _ _ (ha _)) _

set_option backward.isDefEq.respectTransparency false in
private theorem component_split_refinement (X : Scheme.{u}) (U : Qcqs X)
    (hU : HasSplitFiniteQcqsCovers U) (S : Sieve U.obj) (hS : S ∈ topology X U.obj) :
    ∃ (I : Type u) (_ : Finite I) (W : I → Qcqs X) (c : Cofan (fun i ↦ (W i).obj)),
      Nonempty (IsColimit c) ∧
      (∀ H : Sheaf (topology X) (Type (u + 1)),
        Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
          fun i ↦ H.obj.map (c.inj i).op t)) ∧
      ∃ (p : c.pt ⟶ U.obj) (σ : U.obj ⟶ c.pt),
        σ ≫ p = 𝟙 U.obj ∧ ∀ i, S (c.inj i ≫ p) := by
  classical
  obtain ⟨n, V, f, hcov, hf⟩ := component_finite_refinement X U S hS
  obtain ⟨s, hs⟩ := hU n V f hcov
  let eI : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let W : ULift.{u} (Fin n) → Qcqs X := V ∘ eI
  have hqc (i) : CompactSpace (W i).obj.left := (W i).property.1
  have hqs (i) : QuasiSeparatedSpace (W i).obj.left := (W i).property.2
  obtain ⟨B, ι, e, hι, _, _, _, ⟨hr⟩, _, hsec, _, _⟩ :=
    finite_coproduct_evaluation.{u, u, u + 1} X _ (fun i ↦ (W i).obj) hqc hqs
  let c : Cofan (fun i ↦ (W i).obj) := Cofan.mk B ι
  let yon := (topology X).uliftYoneda.{u + 1}
  have hc : IsColimit c := isColimitOfReflects yon
    ((Cofan.isColimitMapCoconeEquiv yon _ c).symm hr)
  let p : B ⟶ U.obj := Cofan.IsColimit.desc hc (fun i ↦ f (eI i))
  have hfac (i) : ι i ≫ p = f (eI i) := Cofan.IsColimit.fac hc _ i
  let h : (∐ fun i ↦ (V i).obj.left) ⟶ B.left := Sigma.desc (fun i ↦ (ι ⟨i⟩).left)
  have hp : h ≫ p.left = Sigma.desc (fun i ↦ (f i).left) := by
    apply Sigma.hom_ext
    intro i
    have hh := congrArg (fun k ↦ k.left) (hfac ⟨i⟩)
    change (ι ⟨i⟩).left ≫ p.left = (f i).left at hh
    simpa [h, ← Category.assoc] using hh
  let σ : U.obj ⟶ B := MorphismProperty.Over.homMk (s ≫ h) (by
    rw [← MorphismProperty.Over.w p]
    calc
      (s ≫ h) ≫ (p.left ≫ U.obj.hom) = (s ≫ (h ≫ p.left)) ≫ U.obj.hom := by
        simp only [Category.assoc]
      _ = U.obj.hom := by rw [hp, hs, Category.id_comp])
  have hσ : σ ≫ p = 𝟙 U.obj := by
    apply MorphismProperty.Over.Hom.ext
    change (s ≫ h) ≫ p.left = 𝟙 _
    rw [Category.assoc, hp, hs]
  exact ⟨_, inferInstance, W, c, ⟨hc⟩, hsec, p, σ, hσ,
    fun i ↦ (hfac i).symm ▸ hf (eI i)⟩

private theorem product_transfer (X : Scheme.{u})
    (C : Type w) [Category.{v} C] (P : X.ProEtᵒᵖ ⥤ C)
    (I : Type u) (W : I → X.ProEt) (U : X.ProEt) (f : ∀ i, W i ⟶ U)
    (hc : IsColimit (Cofan.mk U f))
    (he : ∃ c : Cofan W, Nonempty (IsColimit c) ∧
      Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op)))) :
    Nonempty (IsLimit (Fan.mk (P.obj (op U)) (fun i ↦ P.map (f i).op))) := by
  obtain ⟨c, ⟨hc'⟩, ⟨hp⟩⟩ := he
  let e : c.pt ≅ U := hc'.coconePointUniqueUpToIso hc
  refine ⟨hp.ofIsoLimit (Cone.ext (P.mapIso e.symm.op) ?_)⟩
  intro i
  dsimp
  rw [← P.map_comp]
  change P.map (c.inj i.as).op = P.map (f i.as ≫ e.inv).op
  rw [show f i.as ≫ e.inv = c.inj i.as from
    hc'.comp_coconePointUniqueUpToIso_inv hc i]

open CategoryTheory.Limits Scheme in
private theorem fan_bijective {I : Type u} {A : Type (u + 1)}
    {B : I → Type (u + 1)} (f : ∀ i, A ⟶ B i)
    (h : IsLimit (Fan.mk A f)) : Function.Bijective (fun x i ↦ f i x) := by
  constructor
  · intro x y hxy
    have hh : (↾fun _ : PUnit.{u + 2} ↦ x) = (↾fun _ ↦ y) := by
      apply Fan.IsLimit.hom_ext h
      intro i
      ext t
      exact congrFun hxy i
    exact ConcreteCategory.congr_hom hh PUnit.unit
  · intro x
    refine ⟨Fan.IsLimit.lift h (fun i ↦ ↾fun _ : PUnit.{u + 2} ↦ x i) PUnit.unit, ?_⟩
    funext i
    exact ConcreteCategory.congr_hom (Fan.IsLimit.fac h _ i) PUnit.unit

set_option backward.isDefEq.respectTransparency false in
-- The split section is used to prove the unit is an isomorphism, never to define
-- the evaluation comparison. The latter remains canonical.
private theorem component_unit_iso (X : Scheme.{u}) [IsAffine X]
    (C : Type w) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type (u + 1)}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFiniteLimits (CategoryTheory.forget C)]
    [HasWeakSheafify (topology X) C]
    [(topology X).HasSheafCompose (CategoryTheory.forget C)]
    [(topology X).WEqualsLocallyBijective C]
    (F : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite X)) C)
    (P : X.ProEtᵒᵖ ⥤ C) (θ : F.obj ⟶ (componentFunctor X).op ⋙ P)
    (hP : (Functor.LeftExtension.mk P θ).IsPointwiseLeftKanExtension)
    (U : Qcqs X) (hU : HasSplitFiniteQcqsCovers U) :
    IsIso ((toSheafify (topology X) P).app (op U.obj)) := by
  let J := Scheme.ProEt.topology X
  let η := toSheafify J P
  have hb (I : Type u) [Finite I] (W : I → Qcqs X) (c : Cofan (fun i ↦ (W i).obj))
      (hc : IsColimit c) :
      Function.Bijective (fun x : CC (P.obj (op c.pt)) ↦
        fun i ↦ P.map (c.inj i).op x) := by
    obtain ⟨h⟩ := product_transfer X C P I (fun i ↦ (W i).obj) c.pt c.inj
      (hc.ofIsoColimit (Cocone.ext (Iso.refl _))) (component_finite_products X C F P θ hP I W)
    exact fan_bijective (fun i ↦ (CategoryTheory.forget C).map (P.map (c.inj i).op))
      (Fan.isLimitMapConeEquiv (CategoryTheory.forget C) _ _
        (isLimitOfPreserves (CategoryTheory.forget C) h))
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    obtain ⟨I, hI, W, c, ⟨hc⟩, _, p, σ, hσ, hf⟩ :=
      component_split_refinement X U hU _ (Presheaf.equalizerSieve_mem J η x y hxy)
    have heq : P.map p.op x = P.map p.op y := by
      apply (hb I W c hc).1
      funext i
      have hi : P.map (c.inj i ≫ p).op x = P.map (c.inj i ≫ p).op y := hf i
      simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hi
    have heq' := congrArg (fun t ↦ P.map σ.op t) heq
    have hcomp : P.map p.op ≫ P.map σ.op = 𝟙 (P.obj (op U.obj)) := by
      rw [← Functor.map_comp, ← op_comp, hσ]
      exact P.map_id (op U.obj)
    simpa only [← ConcreteCategory.comp_apply, hcomp, ConcreteCategory.id_apply] using heq'
  · intro t
    obtain ⟨I, hI, W, c, ⟨hc⟩, hsec, p, σ, hσ, hf⟩ :=
      component_split_refinement X U hU _ (Presheaf.imageSieve_mem J η t)
    choose x hx using hf
    obtain ⟨s, hs⟩ := (hb I W c hc).2 x
    have heq : η.app (op c.pt) s = (sheafify J P).map p.op t := by
      apply (hsec ((sheafCompose J (CategoryTheory.forget C)).obj ((presheafToSheaf J C).obj P))).1
      funext i
      change (sheafify J P).map (c.inj i).op (η.app (op c.pt) s) =
        (sheafify J P).map (c.inj i).op ((sheafify J P).map p.op t)
      have hs' : P.map (c.inj i).op s = x i := congrFun hs i
      rw [← NatTrans.naturality_apply, hs', hx i]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    refine ⟨P.map σ.op s, ?_⟩
    rw [NatTrans.naturality_apply, heq]
    change (sheafify J P).map σ.op ((sheafify J P).map p.op t) = t
    have hcomp : (sheafify J P).map p.op ≫ (sheafify J P).map σ.op =
        𝟙 ((sheafify J P).obj (op U.obj)) := by
      rw [← Functor.map_comp, ← op_comp, hσ]
      exact (sheafify J P).map_id (op U.obj)
    rw [← ConcreteCategory.comp_apply, hcomp, ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem component_kan_naturality (X : Scheme.{u}) [IsAffine X]
    (C : Type w) [Category.{v} C]
    (F G : Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite X)) C)
    (P Q : X.ProEtᵒᵖ ⥤ C)
    (η : F.obj ⟶ (componentFunctor X).op ⋙ P)
    (θ : G.obj ⟶ (componentFunctor X).op ⋙ Q)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (α : F ⟶ G) (β : P ⟶ Q)
    (hβ : η ≫ Functor.whiskerLeft (componentFunctor X).op β = α.hom ≫ θ)
    (V W : Qcqs X) (a : V ⟶ W)
    (eF : P.obj (op W.obj) ≅ F.obj.obj (op (componentObject X W)))
    (eG : Q.obj (op V.obj) ≅ G.obj.obj (op (componentObject X V)))
    (heF : ∀ E (f : W.obj ⟶ (componentFunctor X).obj E),
      η.app (op E) ≫ P.map f.op ≫ eF.hom = F.obj.map (componentFactor W E f).op)
    (heG : ∀ E (f : V.obj ⟶ (componentFunctor X).obj E),
      θ.app (op E) ≫ Q.map f.op ≫ eG.hom = G.obj.map (componentFactor V E f).op) :
    P.map a.hom.op ≫ β.app (op V.obj) ≫ eG.hom =
      eF.hom ≫ F.obj.map (componentObjectMap a).op ≫
        α.hom.app (op (componentObject X V)) := by
  apply (hP (op W.obj)).hom_ext'
  intro E f
  cases E with | op E =>
    have hβE := congrArg (fun z ↦ z.app (op E)) hβ
    change η.app (op E) ≫ β.app ((componentFunctor X).op.obj (op E)) =
      α.hom.app (op E) ≫ θ.app (op E) at hβE
    change η.app (op E) ≫ P.map f ≫ (P.map a.hom.op ≫ β.app (op V.obj) ≫ eG.hom) =
      η.app (op E) ≫ P.map f ≫ eF.hom ≫ F.obj.map (componentObjectMap a).op ≫
        α.hom.app (op (componentObject X V))
    calc
      _ = η.app (op E) ≫ P.map (f ≫ a.hom.op) ≫ β.app (op V.obj) ≫ eG.hom := by
        simp only [P.map_comp, Category.assoc]
      _ = α.hom.app (op E) ≫ θ.app (op E) ≫ Q.map (f ≫ a.hom.op) ≫ eG.hom := by
        rw [β.naturality_assoc, ← Category.assoc, hβE, Category.assoc]
      _ = α.hom.app (op E) ≫ G.obj.map (componentFactor V E (a.hom ≫ f.unop)).op := by
        rw [← heG E (a.hom ≫ f.unop)]
        rfl
      _ = F.obj.map (componentFactor W E f.unop).op ≫
          F.obj.map (componentObjectMap a).op ≫ α.hom.app (op (componentObject X V)) := by
        rw [componentFactor_source]
        rw [op_comp, G.obj.map_comp, ← Category.assoc, ← α.hom.naturality]
        rw [Category.assoc, ← α.hom.naturality]
      _ = _ := by
        rw [← heF E f.unop]
        simp only [Quiver.Hom.op_unop, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
-- Construct the inverse image directly in the coefficient category. This also
-- makes the abelian-group and ring comparisons preserve their operations.
private theorem component_evaluation (X : Scheme.{u}) [IsAffine X]
    (hU : (componentFunctor X).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite X)) (topology X))
    (C : Type w) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type (u + 1)}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesFiniteLimits (CategoryTheory.forget C)]
    [ReflectsFiniteLimits (CategoryTheory.forget C)] [HasFiniteLimits C]
    [HasColimitsOfSize.{u, u + 1} C]
    [PreservesFilteredColimitsOfSize.{u, u + 1} (CategoryTheory.forget C)]
    [HasSheafify (topology X) C]
    [HasSheafify ((coherentTopology Profinite.{u}).over (componentProfinite X)) C]
    [(topology X).HasSheafCompose (CategoryTheory.forget C)]
    [(topology X).WEqualsLocallyBijective C] :
    ComponentSiteEvaluation X (componentFunctor X) (componentProjection X) hU C := by
  classical
  let U := componentFunctor X
  let J := (coherentTopology Profinite.{u}).over (componentProfinite X)
  let K := topology X
  let : U.IsContinuous J K := hU
  let : PreservesFiniteLimits U := componentFunctor_finiteLimits X
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  let : AB5OfSize.{u, u + 1} C :=
    ⟨fun I ↦ HasExactColimitsOfShape.domain_of_functor I (CategoryTheory.forget C)⟩
  let L := Functor.sheafPullbackConstruction.sheafPullback U C J K
  let R := U.sheafPushforwardContinuous C J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U C J K
  let g : GeometricMorphism (Sheaf K C) (Sheaf J C) :=
    ⟨L, R, adj, inferInstance⟩
  let P (F : Sheaf J C) := U.op.leftKanExtension F.obj
  let θ (F : Sheaf J C) := U.op.leftKanExtensionUnit F.obj
  have hP (F : Sheaf J C) : (Functor.LeftExtension.mk (P F) (θ F)).IsPointwiseLeftKanExtension :=
    Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit U.op F.obj
  have heval (F : Sheaf J C) (W : Qcqs X) :=
    kanEvaluation U W.obj (componentObject X W) (componentFactorEquiv W)
      (fun _ _ a b ↦ componentFactor_natural W a b) F.obj (P F) (θ F) (hP F)
  choose e he using heval
  have hη (F : Sheaf J C) (W : Qcqs X) (hW : HasSplitFiniteQcqsCovers W) :
      IsIso ((toSheafify K (P F)).app (op W.obj)) :=
    component_unit_iso X C F (P F) (θ F) (hP F) W hW
  let e' (F : Sheaf J C) (W : Qcqs X) (hW : HasSplitFiniteQcqsCovers W) :
      (L.obj F).obj.obj (op W.obj) ≅ F.obj.obj (op (componentObject X W)) :=
    let := hη F W hW
    (asIso ((toSheafify K (P F)).app (op W.obj))).symm ≪≫ e F W
  have hu (F : Sheaf J C) (E : Over (componentProfinite X)) :
      (adj.unit.app F).hom.app (op E) =
        (θ F).app (op E) ≫ (toSheafify K (P F)).app (op (U.obj E)) := by
    dsimp [adj, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Functor.lan, ObjectProperty.ι_obj, Functor.id_obj, Adjunction.comp_unit_app,
      Functor.lanAdjunction_unit, sheafificationAdjunction_unit_app,
      Functor.whiskeringLeft_obj_map, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom,
      Category.assoc]
    erw [Functor.whiskerLeft_id', Category.comp_id, Category.comp_id]
    rfl
  refine ⟨g, Iso.refl _, componentFactor, componentFactor_apply, e', ?_, ?_⟩
  · intro F W hW E a
    let := hη F W hW
    change ((adj.unit.app F).hom.app (op E) ≫ 𝟙 _) ≫
      (sheafify K (P F)).map a.op ≫
        (inv ((toSheafify K (P F)).app (op W.obj)) ≫ (e F W).hom) = _
    rw [Category.comp_id]
    rw [hu, Category.assoc, ← NatTrans.naturality_assoc]
    simp only [IsIso.hom_inv_id_assoc]
    exact he F W E a
  · intro F G α V W hV hW a
    let := hη F W hW
    let := hη G V hV
    let β : P F ⟶ P G := U.op.lan.map α.hom
    have hβ : θ F ≫ Functor.whiskerLeft U.op β = α.hom ≫ θ G := by
      exact (U.op.lanUnit.naturality α.hom).symm
    have hn := component_kan_naturality X C F G (P F) (P G) (θ F) (θ G) (hP F)
      α β hβ V W a (e F W) (e G V) (he F W) (he G V)
    dsimp only [e', Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    change (sheafify K (P F)).map a.hom.op ≫
      ((presheafToSheaf K C).map β).hom.app (op V.obj) ≫
        inv ((toSheafify K (P G)).app (op V.obj)) ≫ (e G V).hom =
      inv ((toSheafify K (P F)).app (op W.obj)) ≫ (e F W).hom ≫
        F.obj.map (componentObjectMap a).op ≫ α.hom.app (op (componentObject X V))
    apply (cancel_epi ((toSheafify K (P F)).app (op W.obj))).mp
    have hnat := (NatTrans.congr_app (toSheafify_naturality K β) (op V.obj)).symm
    change (toSheafify K (P F)).app (op V.obj) ≫
      ((presheafToSheaf K C).map β).hom.app (op V.obj) =
        β.app (op V.obj) ≫ (toSheafify K (P G)).app (op V.obj) at hnat
    simp only [IsIso.hom_inv_id_assoc]
    rw [← NatTrans.naturality_assoc, reassoc_of% hnat]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hn

/-- The affine component functor, its geometric morphism, and its split-cover evaluation.
Source: Bhatt--Scholze, Lemma 2.2.8 and Lemma 4.2.13(1), with the corrected
split-cover hypothesis; Stacks Tags 00WB and 00WK
(blueprint: lem-zl-affine-component-site-projection).

Proof for stage 3 (the thirteen steps of the node):
1. Write $T=\operatorname{Spec}A$ and $q:|T|\to P$. By [lem-weil-pbc-qcqs-scheme-spectral] and
[lem-pe-spectral-components-profinite], $P$ is profinite. For a profinite $E$ put
$D=\operatorname{LC}(E,A)$. By [lem-weil-pbc-locally-constant-prime-spectrum],
$\operatorname{Spec}D=E\times|T|$, with the structure map to $T$ given by projection. Each
locally constant function has finite image on the compact space $E$ and factors through its
finite clopen partition into fibres. Two such presentations agree on their common refinement.
Thus $D$ is the filtered colimit of the finite products $A^{E_i}$. These are finite products of
the principal localization $A_1$, so $A\to D$ is ind-Zariski and ind-etale by
[definition-ind-etale-pro-etale-weakly].
2. The map $E\times|T|\to E\times P$, $(e,t)\mapsto(e,q(t))$, is a quotient map: it is a
continuous surjection from a quasi-compact space to a Hausdorff space and is closed, since each
closed subset of its source is quasi-compact. Its fibres are the connected components of $|T|$.
Conversely a connected subset has constant image in each of the totally disconnected spaces $E$
and $P$, so these fibres are exactly the connected components of $E\times|T|$. Consequently
$\pi_0(\operatorname{Spec}D)=E\times P$. For $f:E\to P$, its graph $G=\{(e,f(e)):e\in E\}$ is
closed. Put $Z=\{(e,t):q(t)=f(e)\}$, the inverse image of $G$. It is a closed union of
components of $\operatorname{Spec}D$.
3. Let $M$ be the multiplicative set of idempotents $a\in D$ such that $Z\subseteq D(a)$, and
define the actual algebra $B=M^{-1}D$ and $T_E=\operatorname{Spec}B$. Products stay in $M$, and
$1\in M$; if $Z=\varnothing$, $0\in M$ and $B=0$. By [lem-weil-pbc-spec-clopen-idempotent] and
[lem-weil-pbc-profinite-clopen-basis], the intersection of these clopen neighbourhoods is
exactly $Z$: a point outside $Z$ maps outside the closed subset $G$ of the profinite space
$E\times P$, so a clopen containing $G$ excludes it. By
[lem-weil-pbc-localization-spectrum-embedding], $\operatorname{Spec}B\to\operatorname{Spec}D$ is
a homeomorphism onto precisely this intersection. The localization $B$ is the filtered colimit
of $D_a$, $a\in M$, since finitely many denominators combine by multiplication. Therefore $D\to
B$ is ind-Zariski and ind-etale; [lemma-stability] makes $A\to B$ ind-etale.
This constructs the required affine object without choosing unspecified existence data.
4. At a point $(e,\mathfrak p)$ of $\operatorname{Spec}D$, evaluation identifies
$D_{(e,\mathfrak p)}$ with $A_{\mathfrak p}$. Indeed every locally constant function is constant
on a clopen neighbourhood of $e$; its characteristic idempotent is outside the prime and hence
becomes $1$ in this local ring. Thus every fraction is the fraction of its two values at $e$;
conversely constant functions define the inverse homomorphism. Further localization by $M$
leaves these local rings unchanged at points of $Z$, by the fraction formulas of
[def-weil-pbc-localization-at-prime]. Hence the structure morphism induces isomorphisms on all
stalks of the inverse-image structure sheaf from $T$. Applying
[lem-weil-pbc-sets-sheaf-iso-on-stalks] to the underlying sheaves identifies this structure
sheaf with $\mathcal O_{T_E}$; the inverse maps preserve ring operations because the original
maps do. The ringed space is therefore exactly $|T|\times_P E$ with the inverse-image sheaf
specified in the statement.
5. The projection $|T_E|\to E$ is surjective and has connected fibres $q^{-1}(f(e))$. A
connected subset has constant image in $E$, so these fibres are exactly the connected
components. The space $|T_E|$ is quasi-compact, and its projection to the Hausdorff space $E$ is
closed (closed subsets are quasi-compact). It is therefore a quotient map and induces the
canonical homeomorphism $\pi_0(|T_E|)\cong E$. For any scheme $W\to T$, a continuous lift
$|W|\to |T|\times_P E$ over $|T|$ gives a unique scheme map $W\to T_E$: pull back the given
structure-sheaf map of $W\to T$ through the identified inverse-image sheaf. It is local on
stalks because the stalks on the target are those of $T$. Conversely every scheme map gives that
lift. If $W$ is qcqs, such lifts are precisely continuous $P$-maps $\pi_0(|W|)\to E$, by the
quotient topology and total disconnectedness of $E$. This proves the mapping bijection,
including its naturality by composition.
6. A continuous $P$-map $E\to E'$ now gives the unique $T$-map $T_E\to T_{E'}$ inducing it;
uniqueness gives identities and composition. The same mapping description proves preservation of
finite limits: maps from any scheme $W\to T$ into a finite limiting cone correspond to
continuous lifts into the corresponding finite limit of profinite spaces over $P$, hence to one
unique map to its $T_E$. In particular $T_P=T$ and $T_{E_1\times_E
E_2}=T_{E_1}\times_{T_E}T_{E_2}$. For a finite jointly surjective family $E_i\to E$, every point
$(t,e)$ lifts to some $(t,e_i)$. Each induced arrow is ind-etale by the last algebra-map clause
of [lemma-stability], since both algebras are ind-etale over $A$. It is weakly
etale by that node. By [lem-weil-pbc-morphism-affine-schemes-affine], these arrows between
affine schemes are affine: over every affine open of the target, their inverse images are
affine. They remain jointly surjective over that open. Since the family is finite, these inverse
images give exactly the finite affine source opens required by [definition-small-pro-etale-site--1].
This proves preservation of coverings, also when all spaces are empty.
7. Take the small skeletons and the larger sheaf-value universe of [prose-01-10].
The category of profinite spaces over $P$ has finite limits: they are the usual finite products
and closed equalizer subspaces in compact Hausdorff totally disconnected spaces, with terminal
object $P\to P$. Apply [lem-weil-pbc-left-exact-site-inverse-image-tensor] to $u:E\mapsto T_E$,
using step 6. This gives the geometric morphism $\pi_T$, whose inverse image is presheaf left
Kan extension followed by sheafification, and whose direct image is restriction along $u^{op}$.
This invocation supplies both the adjunction and left exactness; neither is inferred just from a
pointwise formula.
8. Let $F$ be a sheaf of sets on $\mathbf{Prof}/P$ and $W\to T$ be qcqs. In the Kan formula of
[situation-conventions], the index category before taking the opposite
consists of pairs $(E,W\to T_E)$. Step 5 gives its initial object $(\pi_0(|W|)\to P,W\to
T_{\pi_0(|W|)})$: the unique arrow to $(E,a)$ is the component map corresponding to $a$. Its
opposite is terminal. The colimit is therefore $F(\pi_0(|W|)\to P)$: every element represented
in $F(E)$ maps there by that unique arrow, and the universal cocone equations force precisely
these maps. Composition on $W$ and maps of $F$ preserve the component factorizations, so this
identification is natural in both variables. This computes the presheaf inverse image on all
qcqs objects, before sheafification.
9. Let $K$ be the presheaf Kan inverse image of step 8 and $\eta:K\to K^\#$ its sheafification
unit. By [lem-weil-pbc-proetale-qcqs-finite-family-geometry], finite disjoint unions of qcqs
objects are qcqs. Connected components commute with finite disjoint unions, directly from their
quotient topology. For such a union $V=\coprod_i V_i$, step 8 and the sheaf axiom of $F$ for the
clopen summand cover give $K(V)=F(\coprod_i\pi_0(V_i)\to P)=\prod_i K(V_i)$, by the restriction
maps. The same geometry node states $K^\#(V)=\prod_i K^\#(V_i)$ for the sheaf $K^\#$. These
identifications commute with $\eta$ by its naturality. This includes the empty family: both
presheaves have singleton value on the empty scheme.
10. Every covering of a qcqs $W$ has a finite affine refinement. Namely take a finite affine
open cover of $W$; on each affine target open the covering condition of
[definition-small-pro-etale-site--1] provides finitely many affine source opens mapping into it and
covering it. Their composites give the required refinement, and their sources are qcqs by
[lem-weil-pbc-proetale-qcqs-finite-family-geometry]. Hence every covering used to test local
equality or local representability of sections at $W$ can be replaced by a finite qcqs covering
$\{W_i\to W\}$. By the hypothesis in the corrected statement, $p:V=\coprod_iW_i\to W$ then has a
section $\sigma$. This hypothesis is imposed only here, after the general construction and Kan
calculation; it is not asserted for arbitrary qcqs schemes.
11. Suppose $a,b\in K(W)$ have the same image under $\eta_W$. By
[lem-weil-pbc-site-sheafification-sections-local], they agree after a covering of $W$. Refine as
in step 10 to a finite qcqs covering and write $p:V\to W$, $p\sigma=\operatorname{id}_W$. Their
pullbacks agree on each summand, so step 9 gives $p^*a=p^*b$ in $K(V)$. Pulling back by $\sigma$
gives $a=\sigma^*p^*a=\sigma^*p^*b=b$. Thus $\eta_W$ is injective. This uses injectivity of the
finite-product restriction of $K$; it does not assume that $K$ is already separated on arbitrary
objects.
12. Given $t\in K^\#(W)$, [lem-weil-pbc-site-sheafification-sections-local] supplies a cover and
local lifts. Refine it by step 10 to finite qcqs $W_i$, with lifts $a_i\in K(W_i)$ and split
$p:V=\coprod_iW_i\to W$. By step 9 there is a unique $a\in K(V)$ restricting to all $a_i$. The
two sections $\eta_V(a)$ and $p^*t$ of $K^\#(V)$ have the same restrictions on every summand;
the sheaf product formula in step 9 implies their equality. Consequently
$\eta_W(\sigma^*a)=\sigma^*\eta_V(a)=\sigma^*p^*t=t$. Thus $\eta_W$ is bijective. By step 7,
$K^\#=\pi_T^{-1}F$; compose $\eta_W^{-1}$ with step 8 to obtain the asserted formula. Naturality
follows from that of $\eta$ and step 8, for maps between eligible objects. The section $\sigma$
proves bijectivity only and does not enter this canonical identification.
13. For an abelian-group or ring sheaf, use [situation-conventions] to
regard its operations as maps out of finite powers of its underlying sheaf of sets. The inverse
image preserves these powers by step 7. Naturality of the set-valued identification in step 12,
applied to addition, zero, negation, multiplication and one, identifies the induced operations
with those on $F(\pi_0(|W|)\to P)$. For example the addition square identifies the two maps from
$F(\pi_0(|W|))^2$ with the given addition on $F(\pi_0(|W|))$; the nullary maps similarly give
zero and one. The equations for the operations are preserved functorially. Thus the canonical
identification is one of abelian groups or rings, and is natural in their sheaves and in
eligible $W$.
-/
theorem affine_component_site_projection (T : Scheme.{u}) [IsAffine T] :
    ∃ (U : Over (componentProfinite T) ⥤ T.ProEt)
      (r : ∀ E : Over (componentProfinite T), C((U.obj E).left, E.left)),
      (∀ E : Over (componentProfinite T),
        IsAffine (U.obj E).left ∧
        RingHom.IndEtaleAcrossUniverses (U.obj E).hom.appTop.hom ∧
        (∀ x : (U.obj E).left, IsIso ((U.obj E).hom.stalkMap x)) ∧
        (∃ h : (U.obj E).left ≃ₜ
            {p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2},
          (∀ x, (h x).val.1 = (U.obj E).hom x) ∧
          (∀ x, (h x).val.2 = r E x)) ∧
        (∃ e : ConnectedComponents (U.obj E).left ≃ₜ E.left,
          ∀ x : (U.obj E).left, e (ConnectedComponents.mk x) = r E x)) ∧
      (∀ (E E' : Over (componentProfinite T)) (a : E ⟶ E')
        (x : (U.obj E).left), r E' ((U.map a).left x) = a.left (r E x)) ∧
      PreservesFiniteLimits U ∧
      (∀ (n : ℕ) (E : Fin n → Over (componentProfinite T))
        (B : Over (componentProfinite T)) (a : ∀ i, E i ⟶ B),
        (∀ x : B.left, ∃ (i : Fin n) (y : (E i).left), (a i).left y = x) →
          Presieve.ofArrows (fun i ↦ U.obj (E i)) (fun i ↦ U.map (a i)) ∈
            precoverage T (U.obj B)) ∧
      ∃ hU : U.IsContinuous
          ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T),
        ComponentSiteEvaluation T U r hU (Type (u + 1)) ∧
        ComponentSiteEvaluation T U r hU AddCommGrpCat.{u + 1} ∧
        ComponentSiteEvaluation T U r hU CommRingCat.{u + 1} := by
  refine ⟨componentFunctor T, componentProjection T, ?_, ?_,
    componentFunctor_finiteLimits T, ?_, component_continuous T, ?_, ?_, ?_⟩
  · intro E
    refine ⟨componentScheme_isAffine T E, componentStructure_indEtale T E,
      componentStructure_stalk T E, ?_, ?_⟩
    · exact ⟨componentFiberHomeo T E, componentFiberHomeo_fst T E,
        componentFiberHomeo_snd T E⟩
    · exact ⟨componentComponentsHomeo T E, fun _ ↦ rfl⟩
  · intro E E' a x
    exact componentProEtMap_projection a x
  · intro n E B a ha
    exact component_cover E B a ha
  · exact component_evaluation T (component_continuous T) (Type (u + 1))
  · let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    exact component_evaluation T (component_continuous T) AddCommGrpCat.{u + 1}
  · let : HasColimitsOfSize.{u, u + 1} CommRingCat.{u + 1} :=
      hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget CommRingCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    exact component_evaluation T (component_continuous T) CommRingCat.{u + 1}

end AlgebraicGeometry.Scheme.ProEt
