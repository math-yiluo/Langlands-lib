import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantOpenDescent
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianPushout
import Langlands.AlgebraicGeometry.ULiftIntAlgebra

/-! # Affine quotients descend along cofiltered cartesian diagrams -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

namespace AffineLimit

/-- Two supplied pullbacks identify the induced base-change map as an
isomorphism. -/
lemma isIso_baseChangeMap_of_isPullback
    {S X Y T R : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}
    (f : X ⟶ Y) (w : f ≫ b = a) {p : T ⟶ S}
    {x : R ⟶ X} {r : R ⟶ T}
    (hX : IsPullback x r a p) (hY : IsPullback (x ≫ f) r b p) :
    IsIso (baseChangeMap a b f w p) := by
  have heq : baseChangeMap a b f w p =
      hX.flip.isoPullback.inv ≫ hY.flip.isoPullback.hom := by
    apply pullback.hom_ext
    · simp
    · simp [Category.assoc]
  rw [heq]
  infer_instance

end AffineLimit

namespace EtaleEquivalenceRelation

/-- A finite-type ring spectrum is finitely presented over the absolute
terminal scheme in its own universe. -/
lemma locallyOfFinitePresentation_toSpecULiftZ (B : Type u) [CommRing B]
    [Algebra.FiniteType ℤ B] :
    LocallyOfFinitePresentation (specULiftZIsTerminal.from (Spec (CommRingCat.of B))) := by
  let : Algebra (ULift.{u} ℤ) B := Langlands.ULiftInt.algebra B
  let := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ULift.{u} ℤ) (A := B)
    (Subsingleton.elim _ _)
  have : Algebra.FiniteType (ULift.{u} ℤ) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ULift.{u} ℤ) B
  have hft : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) B))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have heq : specULiftZIsTerminal.from (Spec (CommRingCat.of B)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) B)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [heq]
  infer_instance

/-- An affine quotient admits a cartesian comparison to the kernel pair
of an étale surjection between affine schemes whose object is absolutely
finitely presented. -/
lemma exists_finitelyPresented_kernel_square (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] [IsAffine E.R] (hq : E.HasAffineQuotient) :
    ∃ (U M : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine M)
      (q : U ⟶ M) (_ : Etale q) (_ : Surjective q) (f : E.U ⟶ U),
      LocallyOfFinitePresentation (specULiftZIsTerminal.from U) ∧
      LocallyOfFinitePresentation (specULiftZIsTerminal.from M) ∧
      IsPullback (E.t ≫ f) E.s q (f ≫ q) := by
  obtain ⟨A, B, _, _, _, hA, hB, het, hff, φ, F, hF, hbij⟩ :=
    E.exists_fg_pushout_of_hasAffineQuotient hq
  let : Algebra A Γ(E.U, ⊤) := (φ.comp (algebraMap A B)).toAlgebra
  let : Algebra.Etale A B := het
  let : Module.FaithfullyFlat A B := hff
  let : Algebra.FiniteType ℤ A := hA
  let : Algebra.FiniteType ℤ B := hB
  let q := specAlgebraMap A B
  let f := E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)
  refine ⟨Spec (CommRingCat.of B), Spec (CommRingCat.of A), inferInstance,
    inferInstance, q, inferInstance, inferInstance, f,
    locallyOfFinitePresentation_toSpecULiftZ B,
    locallyOfFinitePresentation_toSpecULiftZ A, ?_⟩
  have hpo := CommRingCat.isPushout_of_bijective (E.t.appTop.hom.comp φ)
    E.s.appTop.hom F hF hbij
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  refine hpb.of_iso E.R.isoSpec.symm (Iso.refl _) E.U.isoSpec.symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    dsimp [f]
    rw [reassoc_of% (Scheme.isoSpec_hom_naturality E.t).symm,
      Iso.inv_hom_id_assoc, ← Spec.map_comp]
  · simpa only [Iso.symm_hom, CommRingCat.ofHom_hom] using
      Scheme.isoSpec_inv_naturality E.s
  · rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    dsimp [f, q, specAlgebraMap]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl

end EtaleEquivalenceRelation

namespace EtaleEquivalenceRelation.CartesianDiagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D)
  [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
  (hc : IsLimit (objectFunctor.mapCone c))

include hc in
/-- A kernel-pair comparison that is cartesian at the limit becomes
cartesian at a later level, once its commutativity equation is present. -/
lemma exists_kernel_square {U M : Scheme.{u}} [IsAffine U] [IsAffine M]
    (q : U ⟶ M) [Etale q] (i : I) (f : (D.obj i).U ⟶ U)
    (hw : ((D.obj i).t ≫ f) ≫ q = ((D.obj i).s ≫ f) ≫ q)
    (h : IsPullback (c.pt.t ≫ ((c.π.app i).objMap ≫ f)) c.pt.s
      q (((c.π.app i).objMap ≫ f) ≫ q)) :
    ∃ (j : I) (r : j ⟶ i),
      IsPullback ((D.obj j).t ≫ ((D.map r).objMap ≫ f)) (D.obj j).s
        q (((D.map r).objMap ≫ f) ≫ q) := by
  let B := pullback q (f ≫ q)
  let b : B ⟶ (D.obj i).U := pullback.snd q (f ≫ q)
  let F : (D.obj i).R ⟶ B :=
    pullback.lift ((D.obj i).t ≫ f) (D.obj i).s
      (by simpa only [Category.assoc] using hw)
  have hF : F ≫ b = (D.obj i).s := pullback.lift_snd _ _ _
  let p := (c.π.app i).objMap
  have hs : IsPullback (c.π.app i).relMap c.pt.s (D.obj i).s p :=
    (c.π.app i).isCartesian.2
  have houter : IsPullback (((c.π.app i).relMap ≫ F) ≫
      pullback.fst q (f ≫ q)) c.pt.s q (p ≫ (f ≫ q)) := by
    have heq : ((c.π.app i).relMap ≫ F) ≫ pullback.fst q (f ≫ q) =
        c.pt.t ≫ (p ≫ f) := by
      simp only [F, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, (c.π.app i).isCartesian.1, Category.assoc]
      rfl
    rw [heq]
    exact h
  have ht : IsPullback ((c.π.app i).relMap ≫ F) c.pt.s b p :=
    houter.of_right (by rw [Category.assoc, hF]; exact hs.w)
      (IsPullback.of_hasPullback q (f ≫ q))
  have : IsIso (AffineLimit.baseChangeMap (D.obj i).s b F hF p) :=
    AffineLimit.isIso_baseChangeMap_of_isPullback F hF hs ht
  let A := above D i ⋙ objectFunctor
  let t := objectComparison D i
  let ci := objectFunctor.mapCone (c.whisker (Over.forget i))
  have hci : IsLimit ci := isLimitObjectAbove D i c hc
  have hp : ∀ k : Over i, ci.π.app k ≫ t.app k = p :=
    fun k => cone_comparison D i c k
  have (k : Over i) : IsAffine (A.obj k) :=
    inferInstanceAs (IsAffine (D.obj k.left).U)
  let : Etale (D.obj i).s := (D.obj i).etale_s
  let : Etale b := inferInstanceAs (Etale (pullback.snd q (f ≫ q)))
  obtain ⟨j, hj⟩ := AffineLimit.exists_isIso_baseChangeMap
    A t (D.obj i).s b F hF ci hci p hp
  let r := j.hom
  let pj := (D.map r).objMap
  let Rj := (D.map r).relMap
  have hsj : IsPullback Rj (D.obj j.left).s (D.obj i).s pj :=
    (D.map r).isCartesian.2
  let v := AffineLimit.baseChangeMap (D.obj i).s b F hF pj
  have hv : IsIso v := hj
  let e : (D.obj j.left).R ≅ pullback pj b := hsj.flip.isoPullback ≪≫ asIso v
  have hfst : e.hom ≫ pullback.fst pj b = (D.obj j.left).s := by
    simp [e, v]
  have hsnd : e.hom ≫ pullback.snd pj b = Rj ≫ F := by
    simp [e, v, Category.assoc]
  have hjb : IsPullback (Rj ≫ F) (D.obj j.left).s b pj := by
    exact (IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, hF]; exact hsj.w.symm⟩ e hfst hsnd).flip
  have hjouter := hjb.paste_horiz (IsPullback.of_hasPullback q (f ≫ q))
  refine ⟨j.left, r, ?_⟩
  have heq : (Rj ≫ F) ≫ pullback.fst q (f ≫ q) =
      (D.obj j.left).t ≫ (pj ≫ f) := by
    simp only [F, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, (D.map r).isCartesian.1, Category.assoc]
  rw [heq] at hjouter
  exact hjouter

include hc in
/-- An affine quotient of the limit of a cartesian affine relation diagram
exists already at some level. -/
lemma exists_hasAffineQuotient (hq : c.pt.HasAffineQuotient) :
    ∃ i : I, (D.obj i).HasAffineQuotient := by
  have (i : I) : IsAffine ((D ⋙ objectFunctor).obj i) :=
    inferInstanceAs (IsAffine (D.obj i).U)
  have (i : I) : IsAffine ((D ⋙ relationFunctor).obj i) :=
    inferInstanceAs (IsAffine (D.obj i).R)
  let : IsAffine c.pt.U := Scheme.isAffine_of_isLimit (objectFunctor.mapCone c) hc
  let : IsAffine c.pt.R :=
    Scheme.isAffine_of_isLimit (relationFunctor.mapCone c) (isLimitRelation D c hc)
  obtain ⟨U, M, _, _, q, _, _, f, hU, hM, hpb⟩ :=
    c.pt.exists_finitelyPresented_kernel_square hq
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let t : D ⋙ objectFunctor ⟶ (Functor.const I).obj Z :=
    { app := fun i => specULiftZIsTerminal.from (D.obj i).U
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let : LocallyOfFinitePresentation (specULiftZIsTerminal.from U) := hU
  let : LocallyOfFinitePresentation (specULiftZIsTerminal.from M) := hM
  obtain ⟨i, fi, hfi, _⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (D ⋙ objectFunctor) t (specULiftZIsTerminal.from U)
    (objectFunctor.mapCone c) hc f (by
      ext i
      exact specULiftZIsTerminal.hom_ext _ _)
  change (D.obj i).U ⟶ U at fi
  change (c.π.app i).objMap ≫ fi = f at hfi
  let tR : D ⋙ relationFunctor ⟶ (Functor.const I).obj Z :=
    { app := fun i => specULiftZIsTerminal.from (D.obj i).R
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  have heq : (c.π.app i).relMap ≫ (((D.obj i).t ≫ fi) ≫ q) =
      (c.π.app i).relMap ≫ (((D.obj i).s ≫ fi) ≫ q) := by
    simp only [← Category.assoc]
    rw [(c.π.app i).isCartesian.1, (c.π.app i).isCartesian.2.w]
    simp only [Category.assoc]
    rw [reassoc_of% hfi]
    simpa only [Functor.const_obj_obj, Category.assoc] using hpb.w
  obtain ⟨j, r, hr⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (D ⋙ relationFunctor) tR (specULiftZIsTerminal.from M)
    (relationFunctor.mapCone c) (isLimitRelation D c hc)
    (((D.obj i).t ≫ fi) ≫ q) (((D.obj i).s ≫ fi) ≫ q)
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _) heq
  let fj := (D.map r).objMap ≫ fi
  have hfj : (c.π.app j).objMap ≫ fj = f := by
    dsimp [fj]
    rw [← Category.assoc, ← comp_objMap, c.w r]
    exact hfi
  have hjw : ((D.obj j).t ≫ fj) ≫ q = ((D.obj j).s ≫ fj) ≫ q := by
    change (D.map r).relMap ≫ _ = (D.map r).relMap ≫ _ at hr
    simp only [← Category.assoc] at hr
    rw [(D.map r).isCartesian.1, (D.map r).isCartesian.2.w] at hr
    simpa only [fj, Category.assoc] using hr
  obtain ⟨k, a, ha⟩ := exists_kernel_square D c hc q j fj hjw (by
    rw [hfj]
    exact hpb)
  exact ⟨k, hasAffineQuotient_of_isPullback_kernelPair q (D.obj k)
    ((D.map a).objMap ≫ fj) ha⟩

/-- Choose one level admitting an affine quotient. -/
noncomputable def affineQuotientLevel (hq : c.pt.HasAffineQuotient) : I :=
  Classical.choose (exists_hasAffineQuotient D c hc hq)

lemma hasAffineQuotient_affineQuotientLevel (hq : c.pt.HasAffineQuotient) :
    (D.obj (affineQuotientLevel D c hc hq)).HasAffineQuotient :=
  Classical.choose_spec (exists_hasAffineQuotient D c hc hq)

/-- Every level above a chosen quotient level also has an affine quotient. -/
lemma hasAffineQuotient_of_above_affineQuotientLevel
    (hq : c.pt.HasAffineQuotient) {j : I}
    (r : j ⟶ affineQuotientLevel D c hc hq) : (D.obj j).HasAffineQuotient := by
  exact etaleEquivalenceRelationCartesianAffineQuotient (D.obj j)
    (D.obj (affineQuotientLevel D c hc hq)) (D.map r).objMap (D.map r).relMap
    (D.map r).isCartesian inferInstance inferInstance
    (hasAffineQuotient_affineQuotientLevel D c hc hq)

end EtaleEquivalenceRelation.CartesianDiagram

end Langlands.AlgebraicGeometry
