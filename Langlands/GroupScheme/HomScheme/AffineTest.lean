import Langlands.GroupScheme.HomScheme.Universal

/-! # Universal homomorphism families tested on affine schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}}

section OpenImmersion

variable (H : GroupScheme S) {T W : Over S} (a : W ⟶ T)

/-- The canonical projection `H_W ⟶ H_T` is the base change of `a`. -/
theorem isPullback_baseChangeProj :
    IsPullback (baseChangeProj H a) (pullback.snd H.X.hom W.hom)
      (pullback.snd H.X.hom T.hom) a.left := by
  refine IsPullback.of_right ?_ (baseChangeProj_snd H a)
    (IsPullback.of_hasPullback H.X.hom T.hom)
  rw [baseChangeProj_fst, Over.w a]
  exact IsPullback.of_hasPullback H.X.hom W.hom

instance [IsOpenImmersion a.left] : IsOpenImmersion (baseChangeProj H a) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_baseChangeProj H a).flip ‹_›

/-- The canonical projection `H_W ⟶ H_T` has image the preimage of the image of `a`. -/
theorem range_baseChangeProj :
    Set.range (baseChangeProj H a) =
      pullback.snd H.X.hom T.hom ⁻¹' Set.range a.left := by
  have h := isPullback_baseChangeProj H a
  rw [← Scheme.Pullback.range_fst]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.hom z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]
    rfl

end OpenImmersion

variable {H G : GroupScheme S}

/-- Relative homomorphisms agreeing on the members of an open cover of the test scheme are
equal. -/
theorem relativeHom_eq_of_locally {T : Over S} (i j : RelativeHom H G T)
    (h : ∀ x : T.left, ∃ (W : Over S) (a : W ⟶ T), IsOpenImmersion a.left ∧
      x ∈ Set.range a.left ∧ evaluate a i = evaluate a j) :
    i = j := by
  apply relativeHom_ext
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨W, a, ha, hx, hres⟩ := h (pullback.snd H.X.hom T.hom y)
  have hy : y ∈ Set.range (baseChangeProj H a) := by
    rw [range_baseChangeProj]
    exact hx
  refine ⟨(baseChangeProj H a).opensRange, hy, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp]
  simp only [Category.assoc]
  rw [← evaluate_fst a i, hres, evaluate_fst]

/-- A member of the affine open cover of a scheme over `S`, as a scheme over `S`. -/
abbrev affineCoverOver (T : Over S) (k : T.left.affineCover.I₀) : Over S :=
  Over.mk (T.left.affineCover.f k ≫ T.hom)

/-- The inclusion of a member of the affine open cover of a scheme over `S`. -/
abbrev affineCoverHom (T : Over S) (k : T.left.affineCover.I₀) : affineCoverOver T k ⟶ T :=
  Over.homMk (T.left.affineCover.f k)

instance (T : Over S) (k : T.left.affineCover.I₀) : IsAffine (affineCoverOver T k).left :=
  inferInstanceAs (IsAffine (Spec _))

instance (T : Over S) (k : T.left.affineCover.I₀) :
    IsOpenImmersion (affineCoverHom T k).left :=
  inferInstanceAs (IsOpenImmersion (T.left.affineCover.f k))

/-- Bijectivity of evaluation of a family is invariant under isomorphism of test schemes. -/
theorem bijective_evaluate_of_iso {M T T' : Over S} (i : RelativeHom H G M) (e : T ≅ T')
    (h : Function.Bijective (fun a : T' ⟶ M => evaluate a i)) :
    Function.Bijective (fun a : T ⟶ M => evaluate a i) := by
  let ev : RelativeHom H G T' ≃ RelativeHom H G T :=
    { toFun := evaluate e.hom
      invFun := evaluate e.inv
      left_inv := fun j => by rw [← evaluate_comp, e.inv_hom_id, evaluate_id]
      right_inv := fun j => by rw [← evaluate_comp, e.hom_inv_id, evaluate_id] }
  have hfun : (fun a : T ⟶ M => evaluate a i) =
      ev ∘ (fun a : T' ⟶ M => evaluate a i) ∘ ⇑(e.homCongr (Iso.refl M)) := by
    funext a
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      ev, Equiv.coe_fn_mk]
    rw [← evaluate_comp, Iso.hom_inv_id_assoc]
  rw [hfun]
  exact ev.bijective.comp (h.comp (Equiv.bijective _))

/-- A family is universal as soon as evaluation is bijective on every affine test scheme. -/
theorem isUniversal_of_affine {M : Over S} (i : RelativeHom H G M)
    (h : ∀ T : Over S, IsAffine T.left → Function.Bijective (fun a : T ⟶ M => evaluate a i)) :
    IsUniversal i := by
  intro T
  constructor
  · intro g g' hgg
    simp only at hgg
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun k => ?_
    have h1 : evaluate (affineCoverHom T k ≫ g) i = evaluate (affineCoverHom T k ≫ g') i := by
      rw [evaluate_comp, evaluate_comp, hgg]
    exact congrArg CommaMorphism.left ((h _ inferInstance).injective h1)
  · intro χ
    choose gi hgi using fun k : T.left.affineCover.I₀ =>
      (h (affineCoverOver T k) inferInstance).surjective (evaluate (affineCoverHom T k) χ)
    replace hgi : ∀ k, evaluate (gi k) i = evaluate (affineCoverHom T k) χ := hgi
    have hcompat : ∀ k l,
        pullback.fst (T.left.affineCover.f k) (T.left.affineCover.f l) ≫ (gi k).left =
          pullback.snd (T.left.affineCover.f k) (T.left.affineCover.f l) ≫ (gi l).left := by
      intro k l
      refine (pullback (T.left.affineCover.f k) (T.left.affineCover.f l)).affineCover.hom_ext
        _ _ fun n => ?_
      let V := pullback (T.left.affineCover.f k) (T.left.affineCover.f l)
      let W : Over S := Over.mk (V.affineCover.f n ≫
        pullback.fst (T.left.affineCover.f k) (T.left.affineCover.f l) ≫
        T.left.affineCover.f k ≫ T.hom)
      have : IsAffine W.left := inferInstanceAs (IsAffine (Spec _))
      let p : W ⟶ affineCoverOver T k := Over.homMk (V.affineCover.f n ≫
        pullback.fst (T.left.affineCover.f k) (T.left.affineCover.f l))
      let q : W ⟶ affineCoverOver T l := Over.homMk (V.affineCover.f n ≫
        pullback.snd (T.left.affineCover.f k) (T.left.affineCover.f l)) (by
          simp only [W, Over.mk_hom, Category.assoc]
          rw [← pullback.condition_assoc])
      have hpq : p ≫ affineCoverHom T k = q ≫ affineCoverHom T l := by
        apply Over.OverMorphism.ext
        show (V.affineCover.f n ≫
            pullback.fst (T.left.affineCover.f k) (T.left.affineCover.f l)) ≫
            T.left.affineCover.f k =
          (V.affineCover.f n ≫
            pullback.snd (T.left.affineCover.f k) (T.left.affineCover.f l)) ≫
            T.left.affineCover.f l
        rw [Category.assoc, Category.assoc, pullback.condition]
      have hpq' : p ≫ gi k = q ≫ gi l := by
        apply (h W this).injective
        simp only
        rw [evaluate_comp, evaluate_comp, hgi, hgi, ← evaluate_comp, ← evaluate_comp, hpq]
      have h3 : (V.affineCover.f n ≫
            pullback.fst (T.left.affineCover.f k) (T.left.affineCover.f l)) ≫ (gi k).left =
          (V.affineCover.f n ≫
            pullback.snd (T.left.affineCover.f k) (T.left.affineCover.f l)) ≫ (gi l).left :=
        congrArg CommaMorphism.left hpq'
      simpa only [Category.assoc] using h3
    let m := T.left.affineCover.glueMorphisms (fun k => (gi k).left) hcompat
    have hmk : ∀ k, T.left.affineCover.f k ≫ m = (gi k).left :=
      fun k => T.left.affineCover.ι_glueMorphisms _ hcompat k
    have hm : m ≫ M.hom = T.hom := by
      refine T.left.affineCover.hom_ext _ _ fun k => ?_
      rw [reassoc_of% (hmk k), Over.w (gi k)]
      rfl
    let g : T ⟶ M := Over.homMk m hm
    have hg : ∀ k, affineCoverHom T k ≫ g = gi k := fun k => Over.OverMorphism.ext (hmk k)
    refine ⟨g, relativeHom_eq_of_locally _ _ fun x => ?_⟩
    obtain ⟨k, y, hy⟩ := T.left.affineCover.exists_eq x
    refine ⟨_, affineCoverHom T k, inferInstance, ⟨y, hy⟩, ?_⟩
    simp only
    rw [← evaluate_comp, hg, hgi]

section Transport

variable {H' G' : GroupScheme S}

/-- Transport of a family of homomorphisms along isomorphisms of source and target. -/
def transport (eH : H' ≅ H) (eG : G ≅ G') {T : Over S} (i : RelativeHom H G T) :
    RelativeHom H' G' T :=
  (baseChange T.hom).map eH.hom ≫ i ≫ (baseChange T.hom).map eG.hom

@[reassoc]
theorem baseChange_map_left_fst {T : Scheme.{u}} (f : T ⟶ S) {G G' : GroupScheme S}
    (a : G ⟶ G') :
    ((baseChange f).map a).hom.hom.left ≫ pullback.fst G'.X.hom f =
      pullback.fst G.X.hom f ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem baseChange_map_left_snd {T : Scheme.{u}} (f : T ⟶ S) {G G' : GroupScheme S}
    (a : G ⟶ G') :
    ((baseChange f).map a).hom.hom.left ≫ pullback.snd G'.X.hom f = pullback.snd G.X.hom f :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem baseChangeProj_baseChange_map {T T' : Over S} (a : T' ⟶ T) (e : H' ⟶ H) :
    baseChangeProj H' a ≫ ((baseChange T.hom).map e).hom.hom.left =
      ((baseChange T'.hom).map e).hom.hom.left ≫ baseChangeProj H a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChange_map_left_fst, baseChangeProj_fst_assoc,
      baseChangeProj_fst]
  · simp only [Category.assoc, baseChange_map_left_snd, baseChangeProj_snd,
      baseChange_map_left_snd_assoc]

theorem evaluate_transport (eH : H' ≅ H) (eG : G ≅ G') {T T' : Over S} (a : T' ⟶ T)
    (i : RelativeHom H G T) :
    evaluate a (transport eH eG i) = transport eH eG (evaluate a i) := by
  apply relativeHom_ext
  rw [evaluate_fst]
  simp only [transport, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    baseChange_map_left_fst]
  rw [baseChangeProj_baseChange_map_assoc, evaluate_fst_assoc]

/-- Transport along isomorphisms is a bijection of families. -/
def transportEquiv (eH : H' ≅ H) (eG : G ≅ G') (T : Over S) :
    RelativeHom H G T ≃ RelativeHom H' G' T where
  toFun := transport eH eG
  invFun := transport eH.symm eG.symm
  left_inv i := by
    simp only [transport, Iso.symm_hom, Category.assoc, ← Functor.map_comp, eG.hom_inv_id,
      ← Functor.map_comp_assoc, eH.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  right_inv i := by
    simp only [transport, Iso.symm_hom, Category.assoc, ← Functor.map_comp, eG.inv_hom_id,
      ← Functor.map_comp_assoc, eH.hom_inv_id]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]

/-- Universality is invariant under transport along isomorphisms of source and target. -/
theorem IsUniversal.transport {M : Over S} {i : RelativeHom H G M} (hi : IsUniversal i)
    (eH : H' ≅ H) (eG : G ≅ G') : IsUniversal (HomScheme.transport eH eG i) := by
  intro T
  have hfun : (fun a : T ⟶ M => evaluate a (HomScheme.transport eH eG i)) =
      transportEquiv eH eG T ∘ (fun a : T ⟶ M => evaluate a i) := by
    funext a
    exact evaluate_transport eH eG a i
  rw [hfun]
  exact (transportEquiv eH eG T).bijective.comp (hi T)

end Transport

end Langlands.GroupScheme.HomScheme
