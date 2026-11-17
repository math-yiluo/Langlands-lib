import Langlands.GroupScheme.Rational.SolvableRadicalComparison
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.Absolute.SolvableBijectiveBaseChange
import Langlands.GroupScheme.Absolute.BorelTransport

/-! # Represented solvable radicals under isomorphisms and field extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Transport

variable {k : Type u} [Field k]
  {G G' R R' : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented solvable radical transports through an ambient isomorphism,
including its all-test normality and greatestness. -/
theorem IsSolvableRadical.comp_iso {r : R ⟶ G}
    (hr : IsSolvableRadical r) (e : G ≅ G') :
    IsSolvableRadical (r ≫ e.hom) := by
  refine ⟨hr.isClosedSubgroup.comp_iso e, hr.smooth, hr.connectedSpace,
    hr.isSolvableGroupScheme, ?_, ?_⟩
  · rw [SubgroupFunctor.range_comp_iso]
    exact hr.isNormal.comap e.inv
  · intro H j hj hs hc hsol hn
    have hn' : (SubgroupFunctor.range (j ≫ e.inv)).IsNormal := by
      have hrange : SubgroupFunctor.range (j ≫ e.inv) =
          (SubgroupFunctor.range j).comap e.hom := by
        simpa only [Iso.symm_hom, Iso.symm_inv] using
          SubgroupFunctor.range_comp_iso j e.symm
      rw [hrange]
      exact hn.comap e.hom
    have hle := hr.greatest H (j ≫ e.inv) (hj.comp_iso e.symm) hs hc hsol hn'
    have hle' := SubgroupFunctor.range_comp_mono hle e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hle'

/-- A represented solvable radical transports through an isomorphism of its source. -/
theorem IsSolvableRadical.precomp_iso {r : R ⟶ G}
    (hr : IsSolvableRadical r) (e : R' ≅ R) :
    IsSolvableRadical (e.hom ≫ r) := by
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  let : Smooth R.X.hom := hr.smooth
  have hs : Smooth R'.X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  have hrange := SubgroupFunctor.range_iso_precomp e r
  refine ⟨(IsClosedSubgroup.of_iso e).comp hr.isClosedSubgroup, hs,
    (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hr.connectedSpace,
    hr.isSolvableGroupScheme.of_iso e, ?_, ?_⟩
  · rw [hrange]
    exact hr.isNormal
  · intro H j hj hsm hc hsol hn
    rw [hrange]
    exact hr.greatest H j hj hsm hc hsol hn

end Transport

section FieldIso

variable {k K : Type u} [Field k] [Field K]
  {G R : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented ground-field solvable radical is preserved by an actual
isomorphism of the ground fields. -/
theorem IsSolvableRadical.baseChange_ringEquiv
    {r : R ⟶ G} [IsAffineHom G.X.hom] (hr : IsSolvableRadical r)
    (f : k ≃+* K) :
    IsSolvableRadical ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom f.toRingHom))).map r) := by
  let b := Spec.map (CommRingCat.ofHom f.toRingHom)
  let a := Spec.map (CommRingCat.ofHom f.symm.toRingHom)
  have ha : a ≫ b = 𝟙 _ := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    change Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom) = _
    have h : CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom f.symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
      ext x
      exact f.symm_apply_apply x
    rw [h, Spec.map_id]
  have : IsIso b := isIso_SpecMap_iff.mpr f.bijective
  have : IsIso a := isIso_SpecMap_iff.mpr f.symm.bijective
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hr.smooth
  have hs : Smooth ((GroupScheme.baseChange b).obj R).X.hom := by
    change Smooth (pullback.snd R.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  refine ⟨hr.isClosedSubgroup.baseChange b, hs,
    RadicalFieldTransport.connectedSpace_map b R hr.connectedSpace,
    IsSolvableGroupScheme.baseChange_of_bijective f.toRingHom f.bijective
      hr.isSolvableGroupScheme, ?_, ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal.baseChange b
  · intro H j hj hs hc hsol hn
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsAffineHom H.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    let : Smooth H.X.hom := hs
    let e := baseChangeSectionIso b a ha G
    have hj' := (hj.baseChange a).comp_iso e
    have hn' : (SubgroupFunctor.range
        ((GroupScheme.baseChange a).map j ≫ e.hom)).IsNormal := by
      rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
      exact (hn.baseChange a).comap e.inv
    have hle := hr.greatest ((GroupScheme.baseChange a).obj H)
      ((GroupScheme.baseChange a).map j ≫ e.hom) hj'
      (show Smooth (pullback.snd H.X.hom a) from inferInstance)
      (RadicalFieldTransport.connectedSpace_map a H hc)
      (IsSolvableGroupScheme.baseChange_of_bijective f.symm.toRingHom
        f.symm.bijective hsol) hn'
    let : IsClosedImmersion ((GroupScheme.baseChange b).map r).hom.hom.left :=
      hr.isClosedSubgroup.baseChange b
    let : Mono ((GroupScheme.baseChange b).map r).hom.hom :=
      Over.mono_of_mono_left _
    exact RadicalFieldTransport.range_le_of_section b a ha r j hle

end FieldIso

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {R : GroupScheme (Spec (CommRingCat.of K))}
    {r : R ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- Canonical Galois transport preserves a represented solvable radical of the
base change of a ground-field group. -/
theorem IsSolvableRadical.galoisTransport [IsAffineHom G.X.hom]
    (hr : IsSolvableRadical r) (σ : K ≃ₐ[k] K) :
    IsSolvableRadical (radicalGaloisHom r σ) := by
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  exact (hr.baseChange_ringEquiv σ.toRingEquiv).comp_iso
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G)

/-- A represented solvable radical and its canonical Galois translate have the
same image on every relative test scheme. -/
theorem IsSolvableRadical.range_galoisTransport [IsAffineHom G.X.hom]
    (hr : IsSolvableRadical r) (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.range (radicalGaloisHom r σ) = SubgroupFunctor.range r :=
  (hr.galoisTransport σ).range_eq hr

end Galois

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G R : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {r : R ⟶ G}

/-- The greatestness condition reflects from a field extension as soon as the
original inclusion is closed. -/
theorem IsSolvableRadical.greatest_of_baseChange
    (hr : IsSolvableRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r))
    (hclosed : IsClosedSubgroup r)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
    (hj : IsClosedSubgroup j) (hs : Smooth H.X.hom)
    (hc : ConnectedSpace H.X.left) (hsol : IsSolvableGroupScheme H)
    (hn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range r := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsClosedImmersion r.hom.hom.left := hclosed
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hc
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  apply SubgroupFunctor.le_range_of_baseChange_le b r
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  exact hr.greatest ((GroupScheme.baseChange b).obj H)
    ((GroupScheme.baseChange b).map j) (hj.baseChange b)
    (show Smooth (pullback.snd H.X.hom b) from inferInstance)
    (H.connectedSpace_baseChange_of_smooth_affine b)
    (solvableFieldExtensionStatement k K b H hs hsol)
    (by rw [SubgroupFunctor.range_baseChangeHom]; exact hn.baseChange b)

/-- A closed inclusion whose field-extension pullback is a represented solvable
radical already satisfies the complete represented solvable-radical predicate. -/
theorem IsSolvableRadical.of_baseChange
    (hr : IsSolvableRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r))
    (hclosed : IsClosedSubgroup r) : IsSolvableRadical r := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsClosedImmersion r.hom.hom.left := hclosed
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  have haff : IsAffineHom ((GroupScheme.baseChange b).obj R).X.hom := by
    change IsAffineHom (pullback.snd R.X.hom b)
    infer_instance
  refine ⟨hclosed, smooth_of_baseChange b R hr.smooth,
    connectedSpace_of_baseChange b R hr.connectedSpace,
    IsSolvableGroupScheme.of_baseChange b hr.smooth haff hr.isSolvableGroupScheme,
    ?_, hr.greatest_of_baseChange hclosed⟩
  apply SubgroupFunctor.isNormal_range_of_baseChange b r
  rw [← SubgroupFunctor.range_baseChangeHom]
  exact hr.isNormal

end Field

end Langlands.GroupScheme
