/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRadicialNeighbourhoodModel
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.Finite.FinitePresentationChainDescent
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
import WeilConjectures.AlgebraicGeometry.Finite.FiniteImagesNeighbourhoodShrinking
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Descent of the unmarked finite curve diagram

## References

* Stacks Project, Tag 0GK7, diagram descent before the marked-open paragraph
* Stacks Project, Tag 0GK7, from reduction of the base through diagram descent, before the paragraph
  beginning with W
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem fieldPoint_descResidueField_isIso
    {L : Type u} [Field L] {T : Scheme.{u}} (h : Spec (.of L) ⟶ T)
    [SurjectiveOnStalks h] :
    IsIso (T.descResidueField (Scheme.stalkClosedPointTo h)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(T.descResidueField (Scheme.stalkClosedPointTo h)).hom.injective, ?_⟩
  have hh : Function.Surjective (Scheme.stalkClosedPointTo h) :=
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of L)).hom).2.comp
      (h.stalkMap_surjective (IsLocalRing.closedPoint L))
  intro y
  obtain ⟨x, hx⟩ := hh y
  refine ⟨T.residue _ x, ?_⟩
  change (T.residue _ ≫ T.descResidueField (Scheme.stalkClosedPointTo h)) x = y
  simpa only [Scheme.residue_descResidueField] using hx

private theorem curve_fibre_of_fieldPoint
    {L : Type u} [Field L] {B Y T : Scheme.{u}}
    (q : B ⟶ Spec (.of L)) (p : Y ⟶ T)
    (hB : B ⟶ Y) (hT : Spec (.of L) ⟶ T)
    [SurjectiveOnStalks hT] [GeometricallyIrreducible q]
    (H : IsPullback hB q p hT) (hdim : topologicalKrullDim B ≤ 1) :
    GeometricallyConnected (p.fiberToSpecResidueField (hT (IsLocalRing.closedPoint L))) ∧
      topologicalKrullDim (p.fiber (hT (IsLocalRing.closedPoint L))) ≤ 1 := by
  let s : T := hT (IsLocalRing.closedPoint L)
  let φ := T.descResidueField (Scheme.stalkClosedPointTo hT)
  have : IsIso φ := fieldPoint_descResidueField_isIso hT
  have hfac : Spec.map φ ≫ T.fromSpecResidueField s = hT :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L T hT
  let a : B ⟶ p.fiber s := pullback.lift hB (q ≫ Spec.map φ) (by
    rw [Category.assoc, hfac]
    exact H.w)
  have Ha : IsPullback a q (p.fiberToSpecResidueField s) (Spec.map φ) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback p
      (T.fromSpecResidueField s))
    · simpa only [a, pullback.lift_fst, hfac] using H
    · simp only [a, pullback.lift_snd]
  have : IsIso a := Ha.isIso_fst_of_isIso
  have hgc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h ↦ by
      have := GeometricallyIrreducible.geometrically_irreducibleSpace
        (f := q) y fst snd h
      infer_instance⟩
  refine ⟨?_, ?_⟩
  · apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      a (p.fiberToSpecResidueField s)).mp
    rw [Ha.w]
    exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
      q (Spec.map φ)).mpr hgc
  · exact (a.homeomorph.isHomeomorph.topologicalKrullDim_eq a).symm.trans_le hdim

private theorem genericPoint_preimage_homeomorph
    {R S : Scheme.{u}} (r : R ⟶ S) (hr : Topology.IsOpenEmbedding r) (x : R)
    (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint (r x) Z) :
    ∃ Z ∈ irreducibleComponents R, IsGenericPoint x Z := by
  obtain ⟨Z, hZ, hx⟩ := hη
  refine ⟨r ⁻¹' Z, preimage_mem_irreducibleComponents hZ hr
    ⟨r x, hx.mem, x, rfl⟩, ?_⟩
  change closure {x} = r ⁻¹' Z
  rw [hr.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, hx.def]

private theorem residueFieldMap_isIso_of_surjectiveOnStalks
    {R S : Scheme.{u}} (r : R ⟶ S) [SurjectiveOnStalks r] (x : R) :
    IsIso (r.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(r.residueFieldMap x).hom.injective, ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := R.residue_surjective x y
  obtain ⟨z, rfl⟩ := r.stalkMap_surjective x z
  refine ⟨S.residue (r x) z, ?_⟩
  change (S.residue (r x) ≫ r.residueFieldMap x) z = _
  rw [Scheme.residue_residueFieldMap]
  rfl

private theorem finite_purelyInseparable_specMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [IsPurelyInseparable k K] :
    let q := Spec.map (CommRingCat.ofHom (algebraMap k K))
    IsFinite q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      UniversallyInjective q := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨(IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance),
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)),
    ⟨Function.surjective_to_subsingleton _⟩, ?_⟩
  apply ((tfae_universallyInjective q).out 2 1).mp
  intro Ω _ g₁ g₂ hg
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap k K Ω
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective (by
    simpa only [q, ← Spec.map_comp] using hg))

private theorem exists_generic_radicial_neighbourhood
    (S : Scheme.{u}) (η : S)
    (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K] :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme)
      (σ : Spec (.of K) ⟶ V),
      IsReduced V ∧ IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      SurjectiveOnStalks σ ∧
      σ ≫ g ≫ U.ι = Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField η) K)) ≫ S.fromSpecResidueField η := by
  classical
  let R := S.nilradical.subscheme
  have : IsReduced R :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism S).1
  let r : R ⟶ S := S.nilradical.subschemeι
  have hr : Surjective r :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism S).2.2.1
  have : IsUniversalHomeomorphism r := inferInstance
  let e := IsUniversalHomeomorphism.homeomorph r
  obtain ⟨x, rfl⟩ := r.surjective η
  have hx := genericPoint_preimage_homeomorph r r.isHomeomorph.isOpenEmbedding x hη
  obtain ⟨Z, hZ, hxZ⟩ := hx
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents R x
    (hxZ.def.symm ▸ hZ)
  let := hfield.toField
  have hρ : IsIso (R.residue x) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(R.residue x).hom.injective, R.residue_surjective x⟩
  have hδ : IsIso (r.residueFieldMap x) :=
    residueFieldMap_isIso_of_surjectiveOnStalks r x
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (r x)) K))
  obtain ⟨hqf, hqfp, hqs, hqu⟩ :=
    finite_purelyInseparable_specMap (S.residueField (r x)) K
  let q := q₀ ≫ Spec.map (inv (r.residueFieldMap x)) ≫ Spec.map (R.residue x)
  have : IsFinite q := by dsimp [q]; infer_instance
  have : LocallyOfFinitePresentation q := by dsimp [q]; infer_instance
  have : Surjective q := by dsimp [q]; infer_instance
  have : UniversallyInjective q := by
    exact (MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective q₀
      (Spec.map (inv (r.residueFieldMap x)) ≫ Spec.map (R.residue x))).mpr hqu
  obtain ⟨W, hxW, hW, V₀, p, a, hpfp, hpf, hps, hpu, ha, h, H⟩ :=
    exists_finite_radicial_neighbourhood_model R x q
  let U : S.Opens := ⟨e.symm ⁻¹' (W : Set R), W.isOpen.preimage e.symm.continuous⟩
  have hWU : r ⁻¹ᵁ U = W := by
    ext z
    change e.symm (r z) ∈ W ↔ z ∈ W
    simp only [show r z = e z from rfl, e.symm_apply_apply]
  let er := R.isoOfEq hWU
  let rW : W.toScheme ⟶ U.toScheme := er.inv ≫ r ∣_ U
  have Hr : IsPullback W.ι rW r U.ι := by
    exact (isPullback_morphismRestrict r U).flip.of_iso er (Iso.refl _)
      (Iso.refl _) (Iso.refl _)
      (by simp [er]) (by simp [rW]) (by simp) (by simp)
  have : IsFinite rW := MorphismProperty.of_isPullback Hr inferInstance
  have : Surjective rW := MorphismProperty.of_isPullback Hr hr
  have : UniversallyInjective rW := MorphismProperty.of_isPullback Hr inferInstance
  have ha' : IsPreimmersion a := by
    have : IsPreimmersion (a ≫ W.ι) := ha.symm ▸ inferInstance
    exact IsPreimmersion.of_comp a W.ι
  have hh : IsPreimmersion h := MorphismProperty.of_isPullback H.flip ha'
  have hbase : h ≫ p ≫ rW ≫ U.ι = q₀ ≫ S.fromSpecResidueField (r x) := by
    calc
      _ = h ≫ p ≫ W.ι ≫ r := by rw [Hr.w]
      _ = q ≫ R.fromSpecStalk x ≫ r := by
        calc
          _ = q ≫ a ≫ W.ι ≫ r := by
            simpa only [Category.assoc] using congrArg (· ≫ W.ι ≫ r) H.w
          _ = _ := by rw [← Category.assoc a, ha]
      _ = q₀ ≫ S.fromSpecResidueField (r x) := by
        dsimp only [q]
        simp only [Category.assoc]
        change q₀ ≫ Spec.map (inv (r.residueFieldMap x)) ≫
          R.fromSpecResidueField x ≫ r = _
        rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
          ← Category.assoc (Spec.map (inv (r.residueFieldMap x))),
          ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  let V := V₀.nilradical.subscheme
  let b : V ⟶ V₀ := V₀.nilradical.subschemeι
  have hb : Surjective b :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism V₀).2.2.1
  let σ := h.liftNilradical
  let g := b ≫ p ≫ rW
  have : UniversallyInjective g :=
    MorphismProperty.comp_mem _ _ _ inferInstance
      (MorphismProperty.comp_mem _ _ _ hpu inferInstance)
  have hσ : σ ≫ b = h := Scheme.Hom.liftNilradical_subschemeι h
  have : SurjectiveOnStalks σ := by
    have : SurjectiveOnStalks (σ ≫ b) := hσ.symm ▸ inferInstance
    exact SurjectiveOnStalks.of_comp σ b
  refine ⟨U, ?_, V, g, σ, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  · change e.symm (r x) ∈ W
    simpa only [show r x = e x from rfl, e.symm_apply_apply] using hxW
  · dsimp only [g]
    simp only [Category.assoc]
    rw [← Category.assoc σ b, hσ]
    exact hbase

private theorem fieldPoint_stalk_isIso
    {K : Type u} [Field K] {V : Scheme.{u}} (σ : Spec (.of K) ⟶ V)
    [SurjectiveOnStalks σ]
    (hf : IsField (V.presheaf.stalk (σ (IsLocalRing.closedPoint K)))) :
    IsIso (Scheme.stalkClosedPointTo σ) := by
  let := hf.toField
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(Scheme.stalkClosedPointTo σ).hom.injective,
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (σ.stalkMap_surjective (IsLocalRing.closedPoint K))⟩

open Opposite TopologicalSpace in
private theorem exists_affine_neighbourhood_limit_over (X : Scheme.{u}) (x : X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
      (e : Spec (X.presheaf.stalk x) ≅ c.pt),
      Nonempty (IsLimit c) ∧ (∀ i, IsAffine (D.obj i)) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      ∃ (U : I → X.Opens) (_ : ∀ i, x ∈ U i) (_ : ∀ i, IsAffineOpen (U i))
        (eU : ∀ i, D.obj (Opposite.op i) ≅ (U i).toScheme),
        (∀ i, e.hom ≫ c.π.app (Opposite.op i) ≫ (eU i).hom ≫ (U i).ι =
          X.fromSpecStalk x) ∧
        ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
          D.map a ≫ (eU j.unop).hom ≫ (U j.unop).ι =
            (eU i.unop).hom ≫ (U i.unop).ι := by
  classical
  let N := {U : X.Opens // IsAffineOpen U ∧ x ∈ U}
  have hex {V : X.Opens} (hx : x ∈ V) : ∃ U : N, U.1 ≤ V := by
    obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    exact ⟨⟨U, hU, hxU⟩, hUV⟩
  let : Nonempty N := ⟨(hex (V := ⊤) trivial).choose⟩
  let : IsDirected N (· ≥ ·) := ⟨fun U V ↦ by
    obtain ⟨W, hW⟩ := hex (V := U.1 ⊓ V.1) ⟨U.2.2, V.2.2⟩
    exact ⟨W, hW.trans inf_le_left, hW.trans inf_le_right⟩⟩
  let F : N ⥤ OpenNhds x :=
    (show Monotone (fun U : N ↦ (⟨U.1, U.2.2⟩ : OpenNhds x)) from
      fun _ _ h ↦ h).functor
  have : F.op.Final := Functor.final_of_exists_of_isFiltered _
    (fun V ↦ by
      obtain ⟨U, hU⟩ := hex V.unop.2
      exact ⟨op U, ⟨(homOfLE hU).op⟩⟩)
    (fun s s' ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let R := F.op ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf
  let C : Cocone R :=
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker F.op
  have hC : IsColimit C :=
    (Functor.Final.isColimitWhiskerEquiv F.op _).symm (colimit.isColimit _)
  let A := R.rightOp ⋙ Scheme.Spec
  let a : Cone A := Scheme.Spec.mapCone (coneRightOpOfCocone C)
  have ha : IsLimit a :=
    isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hC)
  let E := (orderDualEquivalence N).op.trans (opOpEquivalence N)
  let D := E.functor ⋙ A
  let c := a.whisker E.functor
  refine ⟨Nᵒᵈ, inferInstance, inferInstance, inferInstance, D, c, Iso.refl _,
    ⟨ha.whiskerEquivalence E⟩, ?_, ?_, ?_⟩
  · intro i
    exact inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj i).1)))
  · intro i j f
    have : IsAffine (D.obj i) :=
      inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj i).1)))
    have : IsAffine (D.obj j) :=
      inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj j).1)))
    infer_instance
  · refine ⟨fun i ↦ (E.functor.obj (op i)).1,
      fun i ↦ (E.functor.obj (op i)).2.2,
      fun i ↦ (E.functor.obj (op i)).2.1,
      fun i ↦ (E.functor.obj (op i)).2.1.isoSpec.symm, ?_, ?_⟩
    · intro i
      let U := E.functor.obj (op i)
      change 𝟙 _ ≫ Spec.map (X.presheaf.germ U.1 x U.2.2) ≫
        U.2.1.isoSpec.inv ≫ U.1.ι = _
      simpa only [Category.id_comp, IsAffineOpen.isoSpec_inv_ι,
        IsAffineOpen.fromSpecStalk] using
        U.2.1.fromSpecStalk_eq_fromSpecStalk U.2.2
    · intro i j a
      change Spec.map (X.presheaf.map _) ≫
        (E.functor.obj j).2.1.isoSpec.inv ≫ (E.functor.obj j).1.ι =
          (E.functor.obj i).2.1.isoSpec.inv ≫ (E.functor.obj i).1.ι
      have heq : (OpenNhds.inclusion x).op.map (F.op.map (E.functor.map a).op) =
          (E.functor.map a).op := Subsingleton.elim _ _
      rw [heq]
      exact IsAffineOpen.map_fromSpec (E.functor.obj j).2.1
        (E.functor.obj i).2.1 ((E.functor.map a).op)

private theorem exists_chain_neighbourhood
    {K : Type u} [Field K] {V X S X₀ : Scheme.{u}}
    (σ : Spec (.of K) ⟶ V) [IsIso (Scheme.stalkClosedPointTo σ)]
    (b : V ⟶ S) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (p₀ : X₀ ⟶ Spec (.of K)) (x₀ : X₀ ⟶ X)
    (HX₀ : IsPullback x₀ p₀ f (σ ≫ b))
    {κ : Type v} [Finite κ] (A B C : κ → Scheme.{u})
    (j₀ : ∀ i, A i ⟶ B i) (q₀ : ∀ i, B i ⟶ C i)
    (t₀ : ∀ i, C i ⟶ Spec (.of K))
    [∀ i, LocallyOfFinitePresentation (j₀ i ≫ q₀ i ≫ t₀ i)]
    [∀ i, QuasiCompact (j₀ i ≫ q₀ i ≫ t₀ i)]
    [∀ i, QuasiSeparated (j₀ i ≫ q₀ i ≫ t₀ i)]
    [∀ i, LocallyOfFinitePresentation (q₀ i ≫ t₀ i)]
    [∀ i, QuasiCompact (q₀ i ≫ t₀ i)]
    [∀ i, QuasiSeparated (q₀ i ≫ t₀ i)]
    [∀ i, LocallyOfFinitePresentation (t₀ i)]
    [∀ i, QuasiCompact (t₀ i)] [∀ i, QuasiSeparated (t₀ i)]
    (ν₀ : (∐ A) ⟶ X₀) (hν₀ : IsFinite ν₀ ∧ Surjective ν₀)
    (hcomm : ∀ i, Sigma.ι A i ≫ ν₀ ≫ p₀ = j₀ i ≫ q₀ i ≫ t₀ i)
    (ht₀ : ∀ i, IsFinite (t₀ i) ∧ Etale (t₀ i))
    (hj₀ : ∀ i, IsOpenImmersion (j₀ i))
    (hq₀ : ∀ i, Smooth (q₀ i) ∧ IsProper (q₀ i)) :
    ∃ (W : V.Opens) (σW : Spec (.of K) ⟶ W.toScheme),
      σW ≫ W.ι = σ ∧
      ∃ (T Y Ybar : κ → Scheme.{u}) (t : ∀ i, T i ⟶ W.toScheme)
        (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (W.ι ≫ b)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd _ _ = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧ (∀ i, Smooth (p i) ∧ IsProper (p i)) ∧
        ∃ (hA : ∀ i, A i ⟶ Y i) (hB : ∀ i, B i ⟶ Ybar i)
          (hC : ∀ i, C i ⟶ T i),
          (∀ i, IsPullback (hA i) (j₀ i ≫ q₀ i ≫ t₀ i)
              (j i ≫ p i ≫ t i) σW ∧
            IsPullback (hB i) (q₀ i ≫ t₀ i) (p i ≫ t i) σW ∧
            IsPullback (hC i) (t₀ i) (t i) σW ∧
            hA i ≫ j i = j₀ i ≫ hB i ∧ hB i ≫ p i = q₀ i ≫ hC i) ∧
          ∃ aX : X₀ ⟶ pullback f (W.ι ≫ b),
            IsPullback (Limits.Sigma.map hA) ν₀ ν aX ∧
              aX ≫ pullback.snd _ _ = p₀ ≫ σW := by
  classical
  obtain ⟨I, hI, hd, hn, D, c, e, ⟨hc⟩, haff, htrans,
    W, hw, hW, eW, heW, hnat⟩ :=
    exists_affine_neighbourhood_limit_over V (σ (IsLocalRing.closedPoint K))
  let := hI
  let := hd
  let := hn
  let := haff
  let : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := htrans
  have : ∀ i, CompactSpace (D.obj i) := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun _ ↦ inferInstance
  let k := Spec.map (Scheme.stalkClosedPointTo σ) ≫ e.hom
  let cK := c.extend k
  have hcK : IsLimit cK := hc.extendIso k
  let i₀ : Iᵒᵖ := Opposite.op (Classical.choice hn)
  let d (i : Iᵒᵖ) : D.obj i ⟶ V := (eW i.unop).hom ≫ (W i.unop).ι
  have hdσ (i : Iᵒᵖ) : cK.π.app i ≫ d i = σ := by
    change (Spec.map (Scheme.stalkClosedPointTo σ) ≫ e.hom) ≫
      c.π.app i ≫ (eW i.unop).hom ≫ (W i.unop).ι = σ
    rw [Category.assoc, heW]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk σ
  let E := pullback f (d i₀ ≫ b)
  let qE : E ⟶ D.obj i₀ := pullback.snd f (d i₀ ≫ b)
  let xE : X₀ ⟶ E := pullback.lift x₀ (p₀ ≫ cK.π.app i₀) (by
    rw [Category.assoc, ← Category.assoc (cK.π.app i₀), hdσ]
    exact HX₀.w)
  have HE : IsPullback xE p₀ qE (cK.π.app i₀) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f (d i₀ ≫ b))
    · simpa only [xE, pullback.lift_fst, ← Category.assoc (cK.π.app i₀), hdσ]
        using HX₀
    · simp only [xE, pullback.lift_snd]
  let νE := ν₀ ≫ HE.isoPullback.hom
  have hνE : IsFinite νE ∧ Surjective νE := by
    have := hν₀.1
    have := hν₀.2
    exact ⟨inferInstance, inferInstance⟩
  have hcommE (i : κ) : Sigma.ι A i ≫ νE ≫ pullback.snd _ _ =
      j₀ i ≫ q₀ i ≫ t₀ i := by
    simpa only [νE, Category.assoc, HE.isoPullback_hom_snd] using hcomm i
  obtain ⟨i, a, T, Y, Ybar, t, j, p, ν, hνf, hνs, hνc, ht, hj, hp,
    hA, hB, hC, H, aE, Hν, haE⟩ :=
    exists_finitePresentation_chain_stage D cK hcK i₀ E qE A B C j₀ q₀ t₀
      νE hνE hcommE ht₀ hj₀ hq₀
  let W' := W i.unop
  let σW : Spec (.of K) ⟶ W'.toScheme := cK.π.app i ≫ (eW i.unop).hom
  let t' (z : κ) := t z ≫ (eW i.unop).hom
  have hσW : σW ≫ W'.ι = σ := by
    exact hdσ i
  have hdi : D.map a ≫ d i₀ = d i := hnat a
  have HEX : IsPullback
      (pullback.fst qE (D.map a) ≫ pullback.fst f (d i₀ ≫ b))
      (pullback.snd qE (D.map a) ≫ (eW i.unop).hom) f (W'.ι ≫ b) := by
    have H₀ := (IsPullback.of_hasPullback qE (D.map a)).paste_horiz
      (IsPullback.of_hasPullback f (d i₀ ≫ b))
    have Hd : D.map a ≫ (d i₀ ≫ b) = d i ≫ b := by
      rw [← Category.assoc, hdi]
    rw [Hd] at H₀
    exact H₀.of_iso (Iso.refl _) (Iso.refl _) (eW i.unop) (Iso.refl _)
      (by simp) (by simp) (by simp) (by rfl)
  let eX := HEX.isoPullback
  let ν' := ν ≫ eX.hom
  have hν' : IsFinite ν' ∧ Surjective ν' := by
    have := hνf
    have := hνs
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨W', σW, hσW, T, Y, Ybar, t', j, p, ν', hν'.1, hν'.2,
    ?_, ?_, hj, hp, hA, hB, hC, ?_, HE.isoPullback.hom ≫ aE ≫ eX.hom, ?_⟩
  · intro z
    change Sigma.ι Y z ≫ ν ≫ HEX.isoPullback.hom ≫ pullback.snd _ _ = _
    rw [HEX.isoPullback_hom_snd]
    simpa only [t', Category.assoc] using congrArg (· ≫ (eW i.unop).hom) (hνc z)
  · intro z
    have := (ht z).1
    have := (ht z).2
    exact ⟨inferInstance, inferInstance⟩
  · intro z
    obtain ⟨HA, HB, HC, hjc, hpc⟩ := H z
    refine ⟨?_, ?_, ?_, hjc, hpc⟩
    · exact HA.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eW i.unop)
        (by simp) (by simp) (by simp [t', Category.assoc]) (by rfl)
    · exact HB.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eW i.unop)
        (by simp) (by simp) (by simp [t', Category.assoc]) (by rfl)
    · exact HC.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eW i.unop)
        (by simp) (by simp) (by rfl) (by rfl)
  · refine ⟨Hν.of_iso (Iso.refl _) (Iso.refl _) HE.isoPullback.symm eX
      (by simp) (by simp [νE]) (by simp [ν']) (by simp), ?_⟩
    change HE.isoPullback.hom ≫ aE ≫ HEX.isoPullback.hom ≫ pullback.snd _ _ = _
    rw [HEX.isoPullback_hom_snd, ← Category.assoc aE, haE]
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc]
    rfl

private theorem restriction_chain_map_isPullback {A B V V' : Scheme.{u}}
    (h : A ⟶ B) (b : B ⟶ V) (a : V' ⟶ V) :
    IsPullback (pullback.fst (h ≫ b) a)
      (pullback.lift (pullback.fst (h ≫ b) a ≫ h) (pullback.snd (h ≫ b) a)
        (by simp [pullback.condition])) h (pullback.fst b a) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback b a)
  simpa only [pullback.lift_snd] using IsPullback.of_hasPullback (h ≫ b) a

private theorem restrict_chain_to_base
    {X S V V' X₀ : Scheme.{u}} (f : X ⟶ S) (b : V ⟶ S) (b' : V' ⟶ S)
    (aV : V' ⟶ V) (haV : aV ≫ b = b')
    {K : Type u} [Field K] (σ : Spec (.of K) ⟶ V)
    (σ' : Spec (.of K) ⟶ V') (hσ : σ' ≫ aV = σ)
    (p₀ : X₀ ⟶ Spec (.of K))
    (n : ℕ) (A B C T Y Ybar : Fin n → Scheme.{u})
    (j₀ : ∀ i, A i ⟶ B i) (q₀ : ∀ i, B i ⟶ C i)
    (t₀ : ∀ i, C i ⟶ Spec (.of K))
    (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)
    (ν₀ : (∐ A) ⟶ X₀) (ν : (∐ Y) ⟶ pullback f b)
    [IsFinite ν] [Surjective ν]
    (hcomm₀ : ∀ i, Sigma.ι A i ≫ ν₀ ≫ p₀ = j₀ i ≫ q₀ i ≫ t₀ i)
    (hcomm : ∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd _ _ = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i)) (hp : ∀ i, Smooth (p i) ∧ IsProper (p i))
    (hA : ∀ i, A i ⟶ Y i) (hB : ∀ i, B i ⟶ Ybar i) (hC : ∀ i, C i ⟶ T i)
    (H : ∀ i, IsPullback (hA i) (j₀ i ≫ q₀ i ≫ t₀ i) (j i ≫ p i ≫ t i) σ ∧
      IsPullback (hB i) (q₀ i ≫ t₀ i) (p i ≫ t i) σ ∧
      IsPullback (hC i) (t₀ i) (t i) σ ∧
      hA i ≫ j i = j₀ i ≫ hB i ∧ hB i ≫ p i = q₀ i ≫ hC i)
    (aX₀ : X₀ ⟶ pullback f b)
    (Hν₀ : IsPullback (Limits.Sigma.map hA) ν₀ ν aX₀)
    (haX₀ : aX₀ ≫ pullback.snd _ _ = p₀ ≫ σ) :
    ∃ (T' Y' B' : Fin n → Scheme.{u}) (t' : ∀ i, T' i ⟶ V')
      (j' : ∀ i, Y' i ⟶ B' i) (p' : ∀ i, B' i ⟶ T' i)
      (ν' : (∐ Y') ⟶ pullback f b'),
      IsFinite ν' ∧ Surjective ν' ∧
      (∀ i, Sigma.ι Y' i ≫ ν' ≫ pullback.snd _ _ = j' i ≫ p' i ≫ t' i) ∧
      (∀ i, IsFinite (t' i) ∧ Etale (t' i)) ∧
      (∀ i, IsOpenImmersion (j' i)) ∧ (∀ i, Smooth (p' i) ∧ IsProper (p' i)) ∧
      ∃ (hA' : ∀ i, A i ⟶ Y' i) (hB' : ∀ i, B i ⟶ B' i)
        (hC' : ∀ i, C i ⟶ T' i),
        (∀ i, IsPullback (hA' i) (j₀ i ≫ q₀ i ≫ t₀ i)
            (j' i ≫ p' i ≫ t' i) σ' ∧
          IsPullback (hB' i) (q₀ i ≫ t₀ i) (p' i ≫ t' i) σ' ∧
          IsPullback (hC' i) (t₀ i) (t' i) σ' ∧
          hA' i ≫ j' i = j₀ i ≫ hB' i ∧ hB' i ≫ p' i = q₀ i ≫ hC' i) ∧
        ∃ aX : X₀ ⟶ pullback f b', IsPullback (Limits.Sigma.map hA') ν₀ ν' aX := by
  classical
  let T' (i : Fin n) := pullback (t i) aV
  let B' (i : Fin n) := pullback (p i ≫ t i) aV
  let Y' (i : Fin n) := pullback (j i ≫ p i ≫ t i) aV
  let aT (i : Fin n) : T' i ⟶ T i := pullback.fst (t i) aV
  let aB (i : Fin n) : B' i ⟶ Ybar i := pullback.fst (p i ≫ t i) aV
  let aY (i : Fin n) : Y' i ⟶ Y i := pullback.fst (j i ≫ p i ≫ t i) aV
  let t' (i : Fin n) : T' i ⟶ V' := pullback.snd (t i) aV
  let q' (i : Fin n) : B' i ⟶ V' := pullback.snd (p i ≫ t i) aV
  let r' (i : Fin n) : Y' i ⟶ V' := pullback.snd (j i ≫ p i ≫ t i) aV
  let p' (i : Fin n) : B' i ⟶ T' i :=
    pullback.lift (aB i ≫ p i) (q' i) (by simp [aB, q', pullback.condition])
  let j' (i : Fin n) : Y' i ⟶ B' i :=
    pullback.lift (aY i ≫ j i) (r' i) (by simp [aY, r', pullback.condition])
  have hpT (i : Fin n) : p' i ≫ t' i = q' i := by simp [p', t']
  have hjT (i : Fin n) : j' i ≫ p' i ≫ t' i = r' i := by
    rw [hpT]; simp [j', q']
  have hpB (i : Fin n) : IsPullback (aB i) (p' i) (p i) (aT i) :=
    restriction_chain_map_isPullback (p i) (t i) aV
  have hjB (i : Fin n) : IsPullback (aY i) (j' i) (j i) (aB i) :=
    restriction_chain_map_isPullback (j i) (p i ≫ t i) aV
  have ht' (i : Fin n) : IsFinite (t' i) ∧ Etale (t' i) :=
    ⟨MorphismProperty.of_isPullback (.of_hasPullback _ _) (ht i).1,
      MorphismProperty.of_isPullback (.of_hasPullback _ _) (ht i).2⟩
  have hj' (i : Fin n) : IsOpenImmersion (j' i) :=
    MorphismProperty.of_isPullback (hjB i) (hj i)
  have hp' (i : Fin n) : Smooth (p' i) ∧ IsProper (p' i) :=
    ⟨MorphismProperty.of_isPullback (hpB i) (hp i).1,
      MorphismProperty.of_isPullback (hpB i) (hp i).2⟩
  let F := pullback.snd f b
  let F' := pullback.snd f b'
  let aX : pullback f b' ⟶ pullback f b :=
    pullback.lift (pullback.fst _ _) (F' ≫ aV) (by
      rw [Category.assoc, haV]
      exact pullback.condition)
  have HX : IsPullback aX F' F aV := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f b) (h₂₂ := b)
    · simpa only [aX, pullback.lift_fst, haV] using IsPullback.of_hasPullback f b'
    · simp [aX, F]
    · exact .of_hasPullback _ _
  let v' (i : Fin n) : Y' i ⟶ pullback f b' :=
    HX.lift (aY i ≫ Sigma.ι Y i ≫ ν) (r' i) (by
      rw [Category.assoc, Category.assoc, hcomm i]
      exact pullback.condition)
  let ν' : (∐ Y') ⟶ pullback f b' := Sigma.desc v'
  have hνcomm (i : Fin n) : Sigma.ι Y' i ≫ ν' ≫ F' = j' i ≫ p' i ≫ t' i := by
    simp only [ν', Sigma.ι_comp_desc_assoc, v', IsPullback.lift_snd]
    exact (hjT i).symm
  have HY (i : Fin n) : IsPullback (aY i) (r' i) (j i ≫ p i ≫ t i) aV :=
    .of_hasPullback _ _
  have Hνi (i : Fin n) : IsPullback (aY i) (v' i) (Sigma.ι Y i ≫ ν) aX := by
    refine IsPullback.of_bot ?_ (by simp [v']) HX
    simpa only [v', IsPullback.lift_snd, Category.assoc, F, hcomm i] using HY i
  have Hν : IsPullback (Limits.Sigma.map aY) ν' ν aX := by
    have Hσ := isPullback_sigmaDesc (fun i ↦ Sigma.ι Y i ≫ ν) v' aY aX Hνi
    have he : Sigma.desc (fun i ↦ Sigma.ι Y i ≫ ν) = ν := by
      apply Sigma.hom_ext
      intro i
      exact Sigma.ι_comp_desc _ _
    simpa only [he] using Hσ
  have hνfinite : IsFinite ν' := MorphismProperty.of_isPullback Hν inferInstance
  have hνsurjective : Surjective ν' := MorphismProperty.of_isPullback Hν inferInstance
  let hA' (i : Fin n) : A i ⟶ Y' i := pullback.lift (hA i)
    (j₀ i ≫ q₀ i ≫ t₀ i ≫ σ') (by
      rw [Category.assoc, Category.assoc, Category.assoc, hσ]
      exact (H i).1.w)
  let hB' (i : Fin n) : B i ⟶ B' i := pullback.lift (hB i)
    (q₀ i ≫ t₀ i ≫ σ') (by
      rw [Category.assoc, Category.assoc, hσ]
      exact (H i).2.1.w)
  let hC' (i : Fin n) : C i ⟶ T' i := pullback.lift (hC i) (t₀ i ≫ σ') (by
    rw [Category.assoc, hσ]
    exact (H i).2.2.1.w)
  have HA' (i : Fin n) : IsPullback (hA' i) (j₀ i ≫ q₀ i ≫ t₀ i) (r' i) σ' := by
    apply IsPullback.of_right (t := HY i)
    · simpa only [hA', aY, pullback.lift_fst, hσ] using (H i).1
    · simp [hA', r']
  have HB' (i : Fin n) : IsPullback (hB' i) (q₀ i ≫ t₀ i) (q' i) σ' := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback (p i ≫ t i) aV)
    · simpa only [hB', pullback.lift_fst, hσ] using (H i).2.1
    · simp [hB']
  have HC' (i : Fin n) : IsPullback (hC' i) (t₀ i) (t' i) σ' := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback (t i) aV)
    · simpa only [hC', pullback.lift_fst, hσ] using (H i).2.2.1
    · simp [hC']
  let aX' := HX.lift aX₀ (p₀ ≫ σ') (by rw [Category.assoc, hσ, haX₀])
  have Hν' : IsPullback (Limits.Sigma.map hA') ν₀ ν' aX' := by
    apply IsPullback.of_right (t := Hν)
    · have hmap : Limits.Sigma.map hA' ≫ Limits.Sigma.map aY = Limits.Sigma.map hA := by
        apply Sigma.hom_ext
        intro i
        simp [hA', aY]
      simpa only [hmap, aX', IsPullback.lift_fst] using Hν₀
    · apply Sigma.hom_ext
      intro i
      apply HX.hom_ext
      · simp only [Category.assoc, Limits.Sigma.ι_map_assoc, ν', Sigma.ι_comp_desc,
          v', IsPullback.lift_fst, aX', hA', aY, pullback.lift_fst_assoc]
        simpa only [Limits.Sigma.ι_map_assoc] using
          congrArg (Sigma.ι A i ≫ ·) Hν₀.w
      · simp only [Category.assoc, Limits.Sigma.ι_map_assoc, hνcomm,
          aX', IsPullback.lift_snd, hA', hjT, r', pullback.lift_snd]
        simpa only [Category.assoc] using
          congrArg (· ≫ σ') (hcomm₀ i).symm
  refine ⟨T', Y', B', t', j', p', ν', hνfinite, hνsurjective,
    hνcomm, ht', hj', hp', hA', hB', hC', ?_, aX', Hν'⟩
  intro i
  refine ⟨?_, ?_, HC' i, ?_, ?_⟩
  · rw [hjT]; exact HA' i
  · rw [hpT]; exact HB' i
  · apply pullback.hom_ext
    · simpa [hA', hB', j', aB, aY] using (H i).2.2.2.1
    · simp [hA', hB', j', r', Category.assoc]
  · apply pullback.hom_ext
    · simpa [hB', hC', p', aB, aT] using (H i).2.2.2.2
    · simp [hB', hC', p', q', Category.assoc]

/-- Descend the unmarked finite curve diagram, preserving its finite comparison map.
No marked open, thickening or marked-image assertion is supplied or constructed.
-/
theorem exists_unmarked_curve_diagram_model
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (K : Type u) [Field K] [Algebra (S.residueField η) K]
    [Module.Finite (S.residueField η) K] [IsPurelyInseparable (S.residueField η) K]
    (n : ℕ) (L : Fin n → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (A B : Fin n → Scheme.{u}) (j₀ : ∀ i, A i ⟶ B i)
    (q₀ : ∀ i, B i ⟶ Spec (.of (L i)))
    (ν₀ : (∐ A) ⟶ pullback (f.fiberToSpecResidueField η)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))))
    (hν₀ : IsFinite ν₀ ∧ Surjective ν₀)
    (hcomm : ∀ i, Sigma.ι A i ≫ ν₀ ≫ pullback.snd _ _ =
      j₀ i ≫ q₀ i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
    (hL : ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i))
    (hj₀ : ∀ i, IsOpenImmersion (j₀ i) ∧ Nonempty (A i))
    (hq₀ : ∀ i, Smooth (q₀ i) ∧ IsProper (q₀ i) ∧
      GeometricallyIrreducible (q₀ i) ∧ topologicalKrullDim (B i) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i)) ∧
        ∃ (σK : Spec (.of K) ⟶ V)
          (hA : ∀ i, A i ⟶ Y i) (hB : ∀ i, B i ⟶ Ybar i)
          (hT : ∀ i, Spec (.of (L i)) ⟶ T i),
          σK ≫ g ≫ U.ι = Spec.map (CommRingCat.ofHom
            (algebraMap (S.residueField η) K)) ≫ S.fromSpecResidueField η ∧
          (∀ i,
            IsPullback (hA i) (j₀ i ≫ q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (j i ≫ p i ≫ t i) σK ∧
            IsPullback (hB i) (q₀ i ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) (p i ≫ t i) σK ∧
            IsPullback (hT i) (Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
              (t i) σK ∧
            hA i ≫ j i = j₀ i ≫ hB i ∧ hB i ≫ p i = q₀ i ≫ hT i) ∧
        (∃ aX : pullback (f.fiberToSpecResidueField η)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))) ⟶
            pullback f (g ≫ U.ι),
          IsPullback (Limits.Sigma.map hA) ν₀ ν aX) ∧
        ∀ i (s : T i), (t i ≫ g ≫ U.ι) s = η →
            GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1 := by
  classical
  obtain ⟨U, hηU, V, g, σ, hVred, hgf, hgs, hgu, hσs, hσbase⟩ :=
    exists_generic_radicial_neighbourhood S η hη K
  have hpoint : (g ≫ U.ι) (σ (IsLocalRing.closedPoint K)) = η := by
    have hh := congrArg (fun h : Spec (.of K) ⟶ S ↦ h (IsLocalRing.closedPoint K)) hσbase
    change (g ≫ U.ι) (σ (IsLocalRing.closedPoint K)) =
      S.fromSpecResidueField η _ at hh
    exact hh.trans (Scheme.fromSpecResidueField_apply η _)
  have : IsUniversalHomeomorphism g := {}
  have hgopen : Topology.IsOpenEmbedding (g ≫ U.ι) :=
    U.ι.isOpenEmbedding.comp g.isHomeomorph.isOpenEmbedding
  have hvgen := genericPoint_preimage_homeomorph (g ≫ U.ι) hgopen
    (σ (IsLocalRing.closedPoint K)) (hpoint.symm ▸ hη)
  obtain ⟨Z, hZ, hvZ⟩ := hvgen
  have hvfield := isField_stalk_of_closure_mem_irreducibleComponents V
    (σ (IsLocalRing.closedPoint K)) (hvZ.def.symm ▸ hZ)
  have hσiso : IsIso (Scheme.stalkClosedPointTo σ) := fieldPoint_stalk_isIso σ hvfield
  let C (i : Fin n) := Spec (.of (L i))
  let t₀ (i : Fin n) : C i ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (L i)))
  have ht₀ (i : Fin n) : IsFinite (t₀ i) ∧ Etale (t₀ i) := by
    have := (hL i).1
    have := (hL i).2
    have hfe : Algebra.FormallyEtale K (L i) := Algebra.FormallyEtale.of_isSeparable K (L i)
    have : Algebra.FinitePresentation K (L i) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale K (L i) := ⟨hfe, inferInstance⟩
    exact ⟨(IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance),
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)⟩
  have : ∀ i, IsOpenImmersion (j₀ i) := fun i ↦ (hj₀ i).1
  have : ∀ i, Smooth (q₀ i) := fun i ↦ (hq₀ i).1
  have : ∀ i, IsProper (q₀ i) := fun i ↦ (hq₀ i).2.1
  have : ∀ i, Etale (t₀ i) := fun i ↦ (ht₀ i).2
  have : ∀ i, IsFinite (t₀ i) := fun i ↦ (ht₀ i).1
  have : ∀ i, IsNoetherian (B i) := fun i ↦ isNoetherian_of_locallyOfFiniteType (q₀ i)
  have : ∀ i, TopologicalSpace.NoetherianSpace (A i) := fun i ↦
    (j₀ i).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : ∀ i, QuasiCompact (j₀ i) := fun i ↦ inferInstance
  have : ∀ i, LocallyOfFinitePresentation (j₀ i ≫ q₀ i ≫ t₀ i) :=
    fun i ↦ inferInstance
  have : ∀ i, QuasiCompact (j₀ i ≫ q₀ i ≫ t₀ i) := fun i ↦ inferInstance
  have : ∀ i, QuasiSeparated (j₀ i ≫ q₀ i ≫ t₀ i) := fun i ↦ inferInstance
  have : ∀ i, LocallyOfFinitePresentation (q₀ i ≫ t₀ i) := fun i ↦ inferInstance
  have : ∀ i, QuasiCompact (q₀ i ≫ t₀ i) := fun i ↦ inferInstance
  have : ∀ i, QuasiSeparated (q₀ i ≫ t₀ i) := fun i ↦ inferInstance
  have : ∀ i, LocallyOfFinitePresentation (t₀ i) := fun i ↦ inferInstance
  have : ∀ i, QuasiCompact (t₀ i) := fun i ↦ inferInstance
  have : ∀ i, QuasiSeparated (t₀ i) := fun i ↦ inferInstance
  let aK := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) K))
  let X₀ := pullback (f.fiberToSpecResidueField η) aK
  let p₀ : X₀ ⟶ Spec (.of K) := pullback.snd _ _
  let x₀ : X₀ ⟶ X := pullback.fst _ _ ≫ f.fiberι η
  have HX₀ : IsPullback x₀ p₀ f (σ ≫ (g ≫ U.ι)) := by
    rw [hσbase]
    exact (IsPullback.of_hasPullback (f.fiberToSpecResidueField η) aK).paste_horiz
      (IsPullback.of_hasPullback f (S.fromSpecResidueField η))
  have hq₀' (i : Fin n) : Smooth (q₀ i) ∧ IsProper (q₀ i) :=
    ⟨(hq₀ i).1, (hq₀ i).2.1⟩
  obtain ⟨W, σW, hσW, T, Y, Ybar, t, j, p, ν, hνf, hνs, hνc, ht, hj, hp,
    hA, hB, hT, H, aX₀, Hν₀, haX₀⟩ :=
    exists_chain_neighbourhood σ (g ≫ U.ι) f p₀ x₀ HX₀ (κ := Fin n) A B C
      j₀ (fun i : Fin n ↦ (q₀ i : B i ⟶ C i)) t₀ ν₀ hν₀ hcomm ht₀
      (fun i ↦ (hj₀ i).1) hq₀'
  have hvW : σ (IsLocalRing.closedPoint K) ∈ W := by
    rw [← hσW]
    exact (σW (IsLocalRing.closedPoint K)).2
  let ηU : U.toScheme := ⟨η, hηU⟩
  have hgσ : g (σ (IsLocalRing.closedPoint K)) = ηU :=
    U.ι.isOpenEmbedding.injective hpoint
  obtain ⟨U₀, hη₀, _, hU₀⟩ := exists_affine_neighbourhood_below_finite_maps
    U.toScheme ηU 1 (fun _ ↦ V) (fun _ ↦ g) (fun _ ↦ W) (by
      intro _ v hv
      have : v = σ (IsLocalRing.closedPoint K) := g.injective (hv.trans hgσ.symm)
      exact this ▸ hvW)
  let V' := g ⁻¹ᵁ U₀
  let U' := U.ι ''ᵁ U₀
  let eU := U.ι.isoImage U₀
  let g' : V'.toScheme ⟶ U'.toScheme := g ∣_ U₀ ≫ eU.hom
  have hg'f : IsFinite g' := by dsimp [g']; infer_instance
  have hg's : Surjective g' := by
    have : Surjective (g ∣_ U₀) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict g U₀).flip hgs
    dsimp [g']; infer_instance
  have hg'u : UniversallyInjective g' :=
    (MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective _ eU.hom).mpr
      (MorphismProperty.of_isPullback (isPullback_morphismRestrict g U₀).flip hgu)
  have hη' : η ∈ U' := ⟨ηU, hη₀, rfl⟩
  have hb' : V'.ι ≫ g ≫ U.ι = g' ≫ U'.ι := by
    change V'.ι ≫ g ≫ U.ι =
      g ∣_ U₀ ≫ (U.ι.isoImage U₀).hom ≫ (U.ι ''ᵁ U₀).ι
    rw [Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι_assoc]
  let aW : V'.toScheme ⟶ W.toScheme :=
    V.homOfLE (hU₀ 0)
  have haW : aW ≫ W.ι = V'.ι := Scheme.homOfLE_ι _ _
  have hσrange : Set.range σ ⊆ Set.range V'.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨σ z, ?_⟩, rfl⟩
    change g (σ z) ∈ U₀
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz, hgσ]
    exact hη₀
  let σ' := IsOpenImmersion.lift V'.ι σ hσrange
  have hσ' : σ' ≫ V'.ι = σ := IsOpenImmersion.lift_fac _ _ _
  have hσW' : σ' ≫ aW = σW := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, haW, hσ', hσW]
  have hbase' : aW ≫ (W.ι ≫ g ≫ U.ι) = g' ≫ U'.ι := by
    rw [← Category.assoc, haW]
    exact hb'
  obtain ⟨T', Y', B', t', j', p', ν', hν'f, hν's, hν'c, ht', hj', hp',
    hA', hB', hT', H', aX', Hν'⟩ :=
    restrict_chain_to_base f (W.ι ≫ g ≫ U.ι) (g' ≫ U'.ι) aW hbase'
      σW σ' hσW' p₀ n A B C T Y Ybar j₀ q₀ t₀ t j p ν₀ ν
      hcomm hνc ht hj hp hA hB hT H aX₀ Hν₀ haX₀
  have hσ'base : σ' ≫ g' ≫ U'.ι = aK ≫ S.fromSpecResidueField η := by
    rw [← hb', ← Category.assoc σ', hσ']
    exact hσbase
  refine ⟨U', hη', V'.toScheme, g', hg'f, hg's, hg'u,
    T', Y', B', t', j', p', ν', hν'f, hν's, hν'c, ht', hj', hp',
    σ', hA', hB', hT', hσ'base, H', ⟨aX', Hν'⟩, ?_⟩
  have hσ's : SurjectiveOnStalks σ' := by
    have : SurjectiveOnStalks (σ' ≫ V'.ι) := hσ'.symm ▸ hσs
    exact SurjectiveOnStalks.of_comp σ' V'.ι
  intro i s hs
  have hg'inj : Function.Injective (g' ≫ U'.ι) :=
    U'.ι.isOpenEmbedding.injective.comp g'.injective
  have hsbase : t' i s = σ' (IsLocalRing.closedPoint K) := by
    apply hg'inj
    have hpoint' : (g' ≫ U'.ι) (σ' (IsLocalRing.closedPoint K)) = η := by
      have hh := congrArg (fun h : Spec (.of K) ⟶ S ↦
        h (IsLocalRing.closedPoint K)) hσ'base
      change (g' ≫ U'.ι) (σ' (IsLocalRing.closedPoint K)) =
        S.fromSpecResidueField η _ at hh
      exact hh.trans (Scheme.fromSpecResidueField_apply η _)
    exact hs.trans hpoint'.symm
  have hCT : IsPullback (hT' i) (t₀ i) (t' i) σ' := (H' i).2.2.1
  have hT's : SurjectiveOnStalks (hT' i) :=
    MorphismProperty.of_isPullback hCT.flip hσ's
  obtain ⟨z, hzs, _⟩ := Scheme.exists_preimage_of_isPullback hCT s
    (IsLocalRing.closedPoint K) hsbase
  have hz : z = IsLocalRing.closedPoint (L i) := Subsingleton.elim _ _
  subst z
  rw [← hzs]
  have HBi : IsPullback (hB' i) (q₀ i) (p' i) (hT' i) :=
    IsPullback.of_bot (H' i).2.1 (H' i).2.2.2.2 hCT
  have : GeometricallyIrreducible (q₀ i) := (hq₀ i).2.2.1
  exact curve_fibre_of_fieldPoint (q₀ i) (p' i) (hB' i) (hT' i) HBi
    (hq₀ i).2.2.2

end AlgebraicGeometry
