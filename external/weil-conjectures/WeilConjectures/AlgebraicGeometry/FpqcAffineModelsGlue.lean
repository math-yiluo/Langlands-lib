/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FpqcAffineModelTransitions
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! Gluing the locally effective models and their projections. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem fpqc_singleton_base_change
    {A B X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (q : A ⟶ B) (a : A ⟶ X) (b : B ⟶ S) (h : IsPullback q a b f) :
    Presieve.singleton q ∈ Scheme.fpqcPrecoverage B := by
  rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
  exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} => f) hf b
    (fun _ => q) (fun _ => a) (fun _ => h)

private theorem effectiveEpi_of_fpqc_singleton
    {A B : Scheme.{u}} (q : A ⟶ B)
    (hq : Presieve.singleton q ∈ Scheme.fpqcPrecoverage B) : EffectiveEpi q := by
  rw [← Sieve.effectiveEpimorphic_singleton,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck hq)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem glue_relative_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) {V : Over X}
    (d : Scheme.Cover.RelativeGluingData S.directedAffineCover)
    (r : ∀ U : S.affineOpens,
      pullback V.hom (pullback.fst f U.1.ι) ⟶ d.functor.obj U)
    (hp : ∀ U, IsPullback (r U) (pullback.snd V.hom (pullback.fst f U.1.ι))
      (d.natTrans.app U) (pullback.snd f U.1.ι))
    (tr : ∀ {U B : S.affineOpens} (i : U ⟶ B),
      Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫ r B =
        r U ≫ d.functor.map i) :
    ∃ q : V.left ⟶ d.glued, IsPullback q V.hom d.toBase f ∧
      ∀ U : S.affineOpens,
        pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q =
          r U ≫ colimit.ι d.functor U := by
  let C : V.left.OpenCover := (S.directedAffineCover.pullback₁ f).pullback₁ V.hom
  have hc : ∀ {U B : S.affineOpens} (i : U ⟶ B),
      C.trans i ≫ (r B ≫ colimit.ι d.functor B) = r U ≫ colimit.ι d.functor U := by
    intro U B i
    rw [← Category.assoc, tr i, Category.assoc]
    rw [colimit.w]
  let q : V.left ⟶ d.glued :=
    C.glueMorphismsOfLocallyDirected (fun U => r U ≫ colimit.ι d.functor U) hc
  have hq (U : S.affineOpens) :
      pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q = r U ≫ colimit.ι d.functor U :=
    C.map_glueMorphismsOfLocallyDirected _ hc U
  refine ⟨q, ?_, hq⟩
  apply IsPullback.flip
  apply Scheme.isPullback_of_openCover V.hom q f d.toBase
    (S.directedAffineCover.pullback₁ f)
  intro U
  have H := ((hp U).paste_horiz (d.isPullback_natTrans_ι_toBase U).flip).flip
  change IsPullback (pullback.snd V.hom (pullback.fst f U.1.ι))
    (pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q)
    (pullback.fst f U.1.ι ≫ f) d.toBase
  rw [hq]
  simpa only [Scheme.directedAffineCover_f, ← pullback.condition] using H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Effective affine-open models give a global pullback projection, invariant locally.
Source: Stacks Project, Descent, Tag 02W3, general-base part of the proof, and
Schemes, Tag 01LH.
(blueprint: lem-galois-fpqc-affine-models-glue)

For each affine open U choose the effective model of E_U. For an inclusion of
an affine open B into U, pull back the U-model to B. The two effective models
over B have canonically isomorphic pullbacks to X_B, compatibly with transport:
the compatibility equation in hlocal identifies both transports with D after
projection to V. Full faithfulness of fpqc descent of morphisms (02W0) descends
this isomorphism uniquely. Uniqueness proves the identity and composition laws.
The resulting natural transformation from the diagram of models to the
locally directed affine open cover of S is equifibered. Relative gluing (01LH)
therefore constructs a scheme W over S. The local isomorphisms from the
restrictions of V to W times_S X agree on intersections by uniqueness of
morphism descent. Glue these isomorphisms and their inverses to obtain a global
pullback square. The local projections to W glue to q. On a test scheme mapping
to an affine open U, transport invariance of q
follows from effectivity of E_U and the displayed compatibility equation.
This is precisely the local invariance asserted below; global invariance is
a separate locality argument. All constructions
use open covers, so the argument includes empty bases and empty objects. -/
theorem fpqc_affine_effective_models_glue
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V)
    (hlocal : ∀ U : S.affineOpens,
      ∃ E : Over.DescentDatum (pullback.snd f U.1.ι)
          (Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
        E.IsEffective ∧
        ∀ {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
          (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
          (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
          (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
            (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
              ← Category.assoc, hab])
            (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
              (by simpa [Category.assoc, pullback.condition] using
                  congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left =
            (E.transport a b hab x).left ≫ pullback.fst V.hom (pullback.fst f U.1.ι)) :
    ∃ (W : Over S) (q : V.left ⟶ W.left), IsPullback q V.hom W.hom f ∧
      ∀ (U : S.affineOpens) {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
        (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
        (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
        (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
          (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
            ← Category.assoc, hab])
          (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
            (by simpa [Category.assoc, pullback.condition] using
              congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left ≫ q =
          x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q := by
  classical
  choose E hE hcompat using hlocal
  choose W r hp hinv using hE
  let C : V.left.OpenCover := (S.directedAffineCover.pullback₁ f).pullback₁ V.hom
  have hepi (U : S.affineOpens) : Epi (r U) := by
    have hU := fpqc_singleton_base_change f hf (pullback.snd f U.1.ι)
      (pullback.fst f U.1.ι) U.1.ι (IsPullback.of_hasPullback f U.1.ι).flip
    have hr := fpqc_singleton_base_change (pullback.snd f U.1.ι) hU (r U)
      (pullback.snd V.hom (pullback.fst f U.1.ι)) (W U).hom (hp U)
    have : EffectiveEpi (r U) := effectiveEpi_of_fpqc_singleton (r U) hr
    infer_instance
  have ht : ∀ (U B : S.affineOpens) (i : U ⟶ B),
      ∃ t : (W U).left ⟶ (W B).left,
        IsPullback t (W U).hom (W B).hom (S.directedAffineCover.trans i) ∧
        C.trans i ≫ r B = r U ≫ t := by
    intro U B i
    exact fpqc_affine_model_transition f hf D E hcompat W r hp hinv i
  choose t tpb tr using ht
  have tid (U : S.affineOpens) : t U U (𝟙 U) = 𝟙 (W U).left := by
    apply (cancel_epi (r U)).mp
    rw [← tr U U (𝟙 U), C.trans_id]
    simp
  have tcomp {U B A : S.affineOpens} (i : U ⟶ B) (j : B ⟶ A) :
      t U A (i ≫ j) = t U B i ≫ t B A j := by
    apply (cancel_epi (r U)).mp
    rw [← tr U A (i ≫ j), C.trans_comp, Category.assoc, tr B A j,
      ← Category.assoc, tr U B i, Category.assoc]
  have tw {U B : S.affineOpens} (i : U ⟶ B) :
      t U B i ≫ (W B).hom = (W U).hom ≫ S.directedAffineCover.trans i :=
    (tpb U B i).w
  let F : S.affineOpens ⥤ Scheme.{u} :=
    { obj := fun U => (W U).left
      map := fun {U B} i => t U B i
      map_id := tid
      map_comp := fun i j => tcomp i j }
  let d : Scheme.Cover.RelativeGluingData S.directedAffineCover :=
    { functor := F
      natTrans := { app := fun U => (W U).hom, naturality := fun _ _ i => tw i }
      equifibered := fun U B i => tpb U B i }
  obtain ⟨q, hp', hq⟩ := glue_relative_pullback f d r hp (fun {U B} i => tr U B i)
  refine ⟨Over.mk d.toBase, q, hp', ?_⟩
  intro U T a b hab x
  rw [hcompat U a b hab x]
  simp only [Category.assoc, hq]
  rw [← Category.assoc, hinv U a b hab x, Category.assoc]

end AlgebraicGeometry
