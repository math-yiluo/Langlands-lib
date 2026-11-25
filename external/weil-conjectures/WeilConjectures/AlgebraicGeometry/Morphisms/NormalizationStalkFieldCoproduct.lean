/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange

/-! # Normalization of a finite field coproduct over a stalk

## References

* Stacks Project, Tags 0307 and 035I
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem exists_normalization_iso
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (ex : X ≅ X') (ey : Y ≅ Y') (h : ex.hom ≫ f' = f ≫ ey.hom) :
    ∃ en : f.normalization ≅ f'.normalization,
      en.hom ≫ f'.fromNormalization = f.fromNormalization ≫ ey.hom ∧
        f.toNormalization ≫ en.hom = ex.hom ≫ f'.toNormalization := by
  have h₁ : f = (ex.hom ≫ f'.toNormalization) ≫
      (f'.fromNormalization ≫ ey.inv) := by
    rw [Category.assoc, Hom.toNormalization_fromNormalization_assoc,
      ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ : f' = (ex.inv ≫ f.toNormalization) ≫
      (f.fromNormalization ≫ ey.hom) := by
    rw [Category.assoc, Hom.toNormalization_fromNormalization_assoc,
      ← h, Iso.inv_hom_id_assoc]
  let m := f.normalizationDesc (ex.hom ≫ f'.toNormalization)
    (f'.fromNormalization ≫ ey.inv) h₁
  let m' := f'.normalizationDesc (ex.inv ≫ f.toNormalization)
    (f.fromNormalization ≫ ey.hom) h₂
  have hm : m ≫ f'.fromNormalization = f.fromNormalization ≫ ey.hom := by
    rw [← cancel_mono ey.inv, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    exact f.normalizationDesc_comp ..
  have hm' : m' ≫ f.fromNormalization = f'.fromNormalization ≫ ey.inv := by
    rw [← cancel_mono ey.hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact f'.normalizationDesc_comp ..
  have hmi : m ≫ m' = 𝟙 _ := by
    apply Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simp [m, m', Category.assoc]
    · simp [Category.assoc, hm', reassoc_of% hm]
    · simp
  have him : m' ≫ m = 𝟙 _ := by
    apply Hom.normalization.hom_ext f' _ _ f'.fromNormalization
    · simp [m, m', Category.assoc]
    · simp [Category.assoc, hm, reassoc_of% hm']
    · simp
  exact ⟨⟨m, m', hmi, him⟩, hm, f.toNormalization_normalizationDesc _ _ h₁⟩

private theorem exists_stalk_normalization_iso
    {N P : Scheme.{u}} (a : P ⟶ N) [QuasiCompact a] [QuasiSeparated a] (s : N) :
    ∃ eb : pullback a.fromNormalization (N.fromSpecStalk s) ≅
        (pullback.snd a (N.fromSpecStalk s)).normalization,
      eb.hom ≫ (pullback.snd a (N.fromSpecStalk s)).fromNormalization =
        pullback.snd a.fromNormalization (N.fromSpecStalk s) := by
  let t := N.fromSpecStalk s
  let g := pullback.fst (𝟙 N) t
  let j := asIso (pullback.snd (𝟙 N) t)
  have hj : g = j.hom ≫ t := by
    simpa [g, j] using (pullback.condition (f := 𝟙 N) (g := t))
  let m := pullback.map a g a t (𝟙 P) j.hom (𝟙 N) (by simp) (by simpa using hj)
  let mn := pullback.map a.fromNormalization g a.fromNormalization t
    (𝟙 _) j.hom (𝟙 N) (by simp) (by simpa using hj)
  let ex := asIso m
  let en := asIso mn
  obtain ⟨ec, hc, _⟩ := exists_normalization_iso (pullback.snd a g)
    (pullback.snd a t) ex j (by simp [ex, m])
  have := Hom.isIso_normalizationPullback_stalk (𝟙 N) a s
  let eb := en.symm ≪≫ (asIso (a.normalizationPullback g)).symm ≪≫ ec
  refine ⟨eb, ?_⟩
  dsimp only [eb, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, hc]
  have hp : inv (a.normalizationPullback g) ≫ (pullback.snd a g).fromNormalization =
      pullback.snd a.fromNormalization g := by
    rw [IsIso.inv_comp_eq, Hom.normalizationPullback_snd]
  change inv mn ≫ inv (a.normalizationPullback g) ≫
    (pullback.snd a g).fromNormalization ≫ j.hom = _
  rw [← Category.assoc (inv (a.normalizationPullback g)), hp]
  rw [IsIso.inv_comp_eq]
  simp [mn, pullback.map, t]

private theorem isIntegral_pi_iff
    (R : Type u) [CommRing R] {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (x : Π i, B i) :
    _root_.IsIntegral R x ↔ ∀ i, _root_.IsIntegral R (x i) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R B i)
  · intro hx
    choose p hp hpx using hx
    refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ (fun i _ ↦ hp i), ?_⟩
    ext i
    change Polynomial.eval₂ (algebraMap R (Π i, B i)) x (∏ j, p j) i = 0
    change (Pi.evalRingHom B i)
      (Polynomial.eval₂ (algebraMap R (Π j, B j)) x (∏ j, p j)) = 0
    rw [Polynomial.hom_eval₂]
    change Polynomial.eval₂ (algebraMap R (B i)) (x i) (∏ j, p j) = 0
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hpx i)

private noncomputable def integralClosurePiEquiv
    (R : Type u) [CommRing R] {ι : Type*} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] :
    integralClosure R (Π i, B i) ≃ₐ[R] Π i, integralClosure R (B i) where
  toFun x i := ⟨x.1 i, (isIntegral_pi_iff R B x.1).mp x.2 i⟩
  invFun x := ⟨fun i ↦ (x i).1, (isIntegral_pi_iff R B _).mpr (fun i ↦ (x i).2)⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_mul' x y := by rfl
  map_add' x y := by rfl
  commutes' r := by rfl

private noncomputable def integralClosureRingEquiv
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (er : R ≃+* S) (ea : A ≃+* B)
    (h : (algebraMap S B).comp er.toRingHom = ea.toRingHom.comp (algebraMap R A)) :
    integralClosure R A ≃+* integralClosure S B := by
  have hi : (algebraMap R A).comp er.symm.toRingHom =
      ea.symm.toRingHom.comp (algebraMap S B) := by
    ext x
    apply ea.injective
    have hx := congrArg (fun k : R →+* B ↦ k (er.symm x)) h
    simpa using hx.symm
  exact
    { toFun := fun x ↦ ⟨ea x.1, x.2.map_of_comp_eq er.toRingHom ea.toRingHom h⟩
      invFun := fun x ↦ ⟨ea.symm x.1,
        x.2.map_of_comp_eq er.symm.toRingHom ea.symm.toRingHom hi⟩
      left_inv := fun x ↦ Subtype.ext (ea.symm_apply_apply x.1)
      right_inv := fun x ↦ Subtype.ext (ea.apply_symm_apply x.1)
      map_mul' := fun x y ↦ Subtype.ext (ea.map_mul x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (ea.map_add x.1 y.1) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_spec_normalization_iso
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ∃ en : (Spec.map (CommRingCat.ofHom (algebraMap R A))).normalization ≅
        Spec (CommRingCat.of (integralClosure R A)),
      en.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A))) =
        (Spec.map (CommRingCat.ofHom (algebraMap R A))).fromNormalization := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let U : (Spec (CommRingCat.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let C := Γ(Spec (CommRingCat.of A), f ⁻¹ᵁ U.1)
  let : Algebra Γ(Spec (CommRingCat.of R), U.1) C := (f.app U.1).hom.toAlgebra
  let er := (ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let ec : C ≅ CommRingCat.of A :=
    (Spec (CommRingCat.of A)).presheaf.mapIso (eqToIso (by simp [U])).op ≪≫ ΓSpecIso _
  have hec : ec.hom = (ΓSpecIso (CommRingCat.of A)).hom := by
    change (Spec (CommRingCat.of A)).presheaf.map
      (𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of A)).Opens))) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have h : (algebraMap R A).comp er.toRingHom =
      ec.commRingCatIsoToRingEquiv.toRingHom.comp
        (algebraMap Γ(Spec (CommRingCat.of R), U.1) C) := by
    change _ = ec.hom.hom.comp (f.app U.1).hom
    apply CommRingCat.hom_ext_iff.mp
    change (ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R A) =
      f.app U.1 ≫ ec.hom
    rw [hec]
    exact (ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A))).symm
  let eic := integralClosureRingEquiv er ec.commRingCatIsoToRingEquiv h
  let c := f.normalizationOpenCover.f U
  have hc : c.opensRange = ⊤ := by
    rw [← Hom.fromNormalization_preimage]
    simp [U]
  have := isIso_of_isOpenImmersion_of_opensRange_eq_top c hc
  let en := (asIso c).symm ≪≫ Scheme.Spec.mapIso eic.toCommRingCatIso.symm.op
  refine ⟨en, ?_⟩
  rw [← cancel_epi c]
  dsimp only [en, Iso.trans_hom, Iso.symm_hom]
  simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [Hom.ι_fromNormalization]
  change Spec.map (CommRingCat.ofHom eic.symm.toRingHom) ≫ Spec.map _ =
    Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ (isAffineOpen_top _).fromSpec
  rw [IsAffineOpen.fromSpec_top]
  have ht : (Spec (CommRingCat.of R)).isoSpec.inv =
      Spec.map (ΓSpecIso (CommRingCat.of R)).inv := by
    rw [← cancel_epi (Spec (CommRingCat.of R)).isoSpec.hom, Iso.hom_inv_id,
      isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [ht, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply eic.injective
  change eic (eic.symm (algebraMap R (integralClosure R A) r)) =
    eic (algebraMap _ _ (er.symm r))
  rw [eic.apply_symm_apply]
  apply Subtype.ext
  change algebraMap R A r = ec.hom (algebraMap _ C (er.symm r))
  have hr := congrArg (fun k : Γ(Spec (CommRingCat.of R), U.1) →+* A ↦ k (er.symm r)) h
  change algebraMap R A (er (er.symm r)) =
    ec.hom (algebraMap _ C (er.symm r)) at hr
  rwa [er.apply_symm_apply] at hr

private theorem sigmaSpec_structure
    (R : Type u) [CommRing R] (n : ℕ) (B : Fin n → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] :
    sigmaSpec (fun i ↦ CommRingCat.of (B i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Π i, B i))) =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap R (B i)))) := by
  ext i
  rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem isIso_sigmaSpec_fin
    (n : ℕ) (B : Fin n → Type u) [∀ i, CommRing (B i)] :
    IsIso (sigmaSpec (fun i ↦ CommRingCat.of (B i))) := by
  let j : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let es := Sigma.reindex j (fun i ↦ Spec (CommRingCat.of (B i)))
  let ep := RingEquiv.piCongrLeft B j
  let ec := es.symm ≪≫
    asIso (sigmaSpec (fun i : ULift.{u} (Fin n) ↦ CommRingCat.of (B i.down))) ≪≫
      Scheme.Spec.mapIso ep.symm.toCommRingCatIso.op
  have h : ec.hom = sigmaSpec (fun i ↦ CommRingCat.of (B i)) := by
    rw [← cancel_epi es.hom]
    dsimp only [ec, Iso.trans_hom, Iso.symm_hom]
    simp only [Iso.hom_inv_id_assoc, asIso_hom]
    ext i
    erw [ι_sigmaSpec_assoc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) ≫
      Spec.map (CommRingCat.ofHom ep.symm.toRingHom) = _
    rw [← Spec.map_comp]
    dsimp only [es]
    rw [Sigma.ι_reindex_hom_assoc, ι_sigmaSpec]
    congr 1
  rw [← h]
  infer_instance

/-- A field-coproduct presentation over a stalk induces the integral-closure
coproduct presentation of relative normalization over that stalk. -/
theorem normalization_stalk_field_coproduct
    {N P : Scheme.{u}} (a : P ⟶ N) [QuasiCompact a] [QuasiSeparated a]
    (s : N) (n : ℕ) (E : Fin n → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (N.presheaf.stalk s) (E i)]
    (e : pullback a (N.fromSpecStalk s) ≅
      ∐ fun i : Fin n ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin n ↦ Spec.map
      (CommRingCat.ofHom (algebraMap (N.presheaf.stalk s) (E i)))) =
        pullback.snd a (N.fromSpecStalk s)) :
    ∃ e' : pullback a.fromNormalization (N.fromSpecStalk s) ≅
        ∐ fun i : Fin n ↦
          Spec (CommRingCat.of (integralClosure (N.presheaf.stalk s) (E i))),
      e'.hom ≫ Sigma.desc (fun i : Fin n ↦ Spec.map (CommRingCat.ofHom
        (algebraMap (N.presheaf.stalk s) (integralClosure (N.presheaf.stalk s) (E i))))) =
          pullback.snd a.fromNormalization (N.fromSpecStalk s) := by
  let R := N.presheaf.stalk s
  let t := N.fromSpecStalk s
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Π i, E i)))
  have := isIso_sigmaSpec_fin n E
  have := isIso_sigmaSpec_fin n (fun i ↦ integralClosure R (E i))
  let ea := e ≪≫ asIso (sigmaSpec (fun i ↦ CommRingCat.of (E i)))
  have hea : ea.hom ≫ f = pullback.snd a t := by
    dsimp only [ea, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, sigmaSpec_structure]
    exact he
  obtain ⟨eb, hb⟩ := exists_stalk_normalization_iso a s
  obtain ⟨en, hn, _⟩ := exists_normalization_iso (pullback.snd a t) f ea
    (Iso.refl _) (by simpa using hea)
  obtain ⟨enA, hnA⟩ := exists_spec_normalization_iso R (Π i, E i)
  let ep := integralClosurePiEquiv R E
  let epS := Scheme.Spec.mapIso ep.toRingEquiv.toCommRingCatIso.symm.op
  let ef := (asIso (sigmaSpec (fun i ↦
    CommRingCat.of (integralClosure R (E i))))).symm
  let d := Sigma.desc (fun i : Fin n ↦ Spec.map (CommRingCat.ofHom
    (algebraMap R (integralClosure R (E i)))))
  have hef : ef.hom ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap R (Π i, integralClosure R (E i)))) := by
    change inv (sigmaSpec _) ≫ d = _
    rw [IsIso.inv_comp_eq, sigmaSpec_structure]
  have hep : epS.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Π i, integralClosure R (E i)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R (Π i, E i)))) := by
    change Spec.map (CommRingCat.ofHom ep.symm.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
  refine ⟨eb ≪≫ en ≪≫ enA ≪≫ epS ≪≫ ef, ?_⟩
  change (eb.hom ≫ en.hom ≫ enA.hom ≫ epS.hom ≫ ef.hom) ≫ d = _
  simp only [Category.assoc]
  rw [hef, hep, hnA, hn]
  simpa using hb

end AlgebraicGeometry.Scheme
