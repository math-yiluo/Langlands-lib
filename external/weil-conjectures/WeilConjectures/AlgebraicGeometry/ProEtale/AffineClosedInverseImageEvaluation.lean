/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Inverse-image evaluation for an affine closed immersion

## References

* Stacks Project, Tag 09BL, (1) and (2)
* Stacks Project, Tag 09BL, (2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

set_option backward.isDefEq.respectTransparency false in
private theorem precoverage_cover {S : Scheme.{u}} {V : S.AffineProEt}
    {R : Presieve V} (hR : R ∈ precoverage V) :
    Sieve.generate R ∈ topology S V := by
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.generate_map_eq_functorPushforward]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [precoverage, ProEt.precoverage, Precoverage.mem_comap_iff,
    Presieve.map_comp, Functor.comp_obj] using hR

set_option backward.isDefEq.respectTransparency false in
private theorem finite_cover_precoverage {S : Scheme.{u}} {V : S.AffineProEt}
    {ι : Type u} [Finite ι] (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
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
  simpa only [precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Functor.comp_obj, Functor.comp_map, toProEt_obj_left, toProEt_map,
    ProEt.forget_obj, ProEt.forget_map, Over.forget_obj, Over.forget_map, E,
    PreZeroHypercover.presieve₀, ProEt.forget, toProEt,
    MorphismProperty.Comma.forget, MorphismProperty.Over.changeProp,
    MorphismProperty.Comma.changeProp] using hE

private noncomputable def sigmaCover_colimit {S : Scheme.{u}} {V : S.AffineProEt}
    {ι : Type u} [Finite ι] (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
    [(topology S).Subcanonical] :
    IsColimit (Cofan.mk (sigmaCover U f) (sigmaCoverι U f)) := by
  classical
  apply Cofan.IsColimit.ofBijective
  intro Y
  let H := (topology S).uliftYoneda.{u + 1}.obj Y
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h : (ULift.up a : H.obj.obj (op (sigmaCover U f))) = ULift.up b :=
      sigmaCover_ext U f H.property (fun j ↦ congrArg ULift.up (congrFun hab j))
    exact congrArg ULift.down h
  · intro a
    obtain ⟨b, hb⟩ := exists_sigmaCover_glue U f H.property (fun j ↦ ULift.up (a j))
    exact ⟨b.down, funext (fun j ↦ congrArg ULift.down (hb j))⟩

private theorem leftAdjoint_sigmaCover_glue {S T : Scheme.{u}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    {V : S.AffineProEt} {ι : Type u} [Finite ι]
    (U : ι → S.AffineProEt) (f : ∀ j, U j ⟶ V)
    (H : Sheaf (topology T) (Type (u + 1))) (x : ∀ j, H.obj.obj (op (v.obj (U j)))) :
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

private theorem cover_split {S : Scheme.{u}} [(topology S).Subcanonical]
    (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V)))
    {W : S.AffineProEt} (q : W ⟶ V) (hq : Surjective q.left) :
    ∃ σ : V ⟶ W, σ ≫ q = 𝟙 V := by
  let J := topology S
  let H := J.uliftYoneda.{u + 1}
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

private theorem precomposition_unit_injective {S T : Scheme.{u}}
    (v : S.AffineProEt ⥤ T.AffineProEt)
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) (Type (u + 1))) (V : S.AffineProEt) :
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

private theorem precomposition_unit_surjective {S T : Scheme.{u}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (H : Sheaf (topology T) (Type (u + 1))) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (f : P ⟶ Q),
      Epi f → Function.Surjective (f.hom.app (op V))) :
    Function.Surjective ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  classical
  let P := v.op ⋙ H.obj
  let G := (presheafToSheaf (topology S) (Type (u + 1))).obj P
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

/-- Restricting the closed inverse image along `Spec (A ⧸ I) ⟶ Spec A` to the affine
ind-etale basis is naturally isomorphic to sheafified evaluation along the canonical lift,
and on weakly contractible basis objects (evaluation surjective on all epimorphisms) the
sheafification unit is bijective, giving an evaluation isomorphism natural in both variables. -/
theorem affine_closed_inverseImage_evaluation (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty
      (proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
          (Type (u + 1)) ⋙
        (toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous (Type (u + 1))
          (topology (Spec (.of (A ⧸ I)))) (ProEt.topology (Spec (.of (A ⧸ I)))) ≅
      sheafToPresheaf (ProEt.topology (Spec (.of A))) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
          (closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙
        presheafToSheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) ∧
    (∀ (F : Sheaf (ProEt.topology (Spec (.of A))) (Type (u + 1)))
      (V : (Spec (.of (A ⧸ I))).AffineProEt),
      (∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) (f : P ⟶ Q),
        Epi f → Function.Surjective (f.hom.app (op V))) →
      Function.Bijective
        ((toSheafify (topology (Spec (.of (A ⧸ I))))
          ((closedSiteLift A I ⋙ toProEt (Spec (.of A))).op ⋙ F.obj)).app (op V))) := by
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
  let RX := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous (Type (u + 1))
    (topology Z) (ProEt.topology Z)
  let L := sheafToPresheaf (topology X) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ (Type (u + 1))).obj v.op ⋙
    presheafToSheaf (topology Z) (Type (u + 1))
  let R := u.sheafPushforwardContinuous (Type (u + 1)) (topology X) (topology Z)
  have a : L ⊣ R :=
    ((adj.op.whiskerLeft (Type (u + 1))).comp
      (sheafificationAdjunction (topology Z) (Type (u + 1)))).restrictFullyFaithful
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
  let beta : proEtaleSheafDirectImage i (Type (u + 1)) ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X) (proEtaleBaseChange i)
      (Type (u + 1)) (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm (Type (u + 1))
      (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp u (toProEt Z) (Type (u + 1))
      (topology X) (topology Z) (ProEt.topology Z)).symm
  let alpha := ((mateEquiv (proEtaleSheafAdjunction i (Type (u + 1))) a).symm
    beta.hom)
  have : IsIso alpha :=
    isIso_inverseMate_of_equivalences (proEtaleSheafAdjunction i (Type (u + 1))) a beta
  refine ⟨?_, ?_⟩
  · exact ⟨(asIso alpha).symm⟩
  · let : (topology Z).Subcanonical :=
      GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt Z)
        (topology Z) (ProEt.topology Z)
    intro F V hV
    let H := RX.obj F
    exact ⟨precomposition_unit_injective v hcov H V,
      precomposition_unit_surjective v adj H V hV⟩

end AlgebraicGeometry.Scheme.AffineProEt
