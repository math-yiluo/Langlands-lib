/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Quotient base change and its ideal sheaf

Source: Stacks Project, Schemes, Tags 01JU (1), 01I4, 01JQ and 01IN; Cohomology of
Schemes, Remark 088F (blueprint: lem-weil-pbc-quotient-base-change-closed-immersion-ideal).

The four statements give closedness and the affine description, products and powers,
the transition for nested ideals, and compatibility of extended ideals with base change.
The statements write out the existing Mathlib constructions; no new notion is defined.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

private instance quotient_spec_closed {A : Type u} [CommRing A] (K : Ideal A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

private lemma quotient_spec_ker {R : CommRingCat.{u}} (K : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker =
      Scheme.IdealSheafData.ofIdealTop
        (K.map (Scheme.ΓSpecIso R).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  rw [← RingHom.ker_equiv_comp _
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ K))).commRingCatIsoToRingEquiv]
  change RingHom.ker ((Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk K))).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ K))).hom).hom = _
  rw [Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
  change (RingHom.ker (Ideal.Quotient.mk K)).comap _ = _
  rw [Ideal.mk_ker]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).symm

private lemma closedImmersion_affine_quotient {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] (U : X.affineOpens) :
    ∃ e : (j ⁻¹ᵁ U.1).toScheme ≅ Spec (CommRingCat.of (Γ(X, U.1) ⧸ j.ker.ideal U)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (j.ker.ideal U))) ≫
        U.2.isoSpec.inv = j ∣_ U.1 := by
  let t := (j ∣_ U.1) ≫ U.2.isoSpec.hom
  have : IsClosedImmersion t := inferInstanceAs
    (IsClosedImmersion ((j ∣_ U.1) ≫ U.2.isoSpec.hom))
  obtain ⟨I, e, he⟩ :=
    (IsClosedImmersion.Spec_iff (f := t)).mp (inferInstance : IsClosedImmersion t)
  have ht : t.ker = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom) := by
    rw [he, Scheme.Hom.ker_comp_of_isIso, quotient_spec_ker]
  have hI : I = j.ker.ideal U := by
    have hh := congrArg (fun J ↦ J.ideal ⟨⊤, isAffineOpen_top _⟩) ht
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_top_ofIdealTop] at hh
    change RingHom.ker (((j ∣_ U.1) ≫ U.2.isoSpec.hom).appTop).hom = _ at hh
    rw [Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop] at hh
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comap_ker, ← Ideal.comap_comap] at hh
    have hr : RingHom.ker (j ∣_ U.1).appTop.hom =
        (j.ker.ideal U).comap U.1.topIso.hom.hom := by
      have ha : (j ∣_ U.1).appTop = U.1.topIso.hom ≫ j.app U.1 ≫
          (j ⁻¹ᵁ U.1).topIso.inv := by
        have ha := Scheme.Hom.resLE_app_top (f := j) (U := U.1)
          (V := j ⁻¹ᵁ U.1) (e := le_rfl)
        rw [Scheme.Hom.resLE_eq_morphismRestrict] at ha
        simpa only [Scheme.Hom.appTop, ← Scheme.Hom.app_eq_appLE] using ha
      rw [ha, CommRingCat.hom_comp, ← RingHom.comap_ker]
      rw [CommRingCat.hom_comp]
      have hpost := RingHom.ker_equiv_comp (j.app U.1).hom
        (j ⁻¹ᵁ U.1).topIso.symm.commRingCatIsoToRingEquiv
      change RingHom.ker ((j ⁻¹ᵁ U.1).topIso.inv.hom.comp (j.app U.1).hom) =
        RingHom.ker (j.app U.1).hom at hpost
      rw [hpost]
      rw [Scheme.Hom.ker_apply]
    simp only [hr, Ideal.comap_comap, ← CommRingCat.hom_comp,
      Iso.inv_hom_id, Category.comp_id] at hh
    have hm : I.map (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom =
        I.comap (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom :=
      Ideal.map_comap_of_equiv (Scheme.ΓSpecIso Γ(X, U.1)).symm.commRingCatIsoToRingEquiv
    rw [hm] at hh
    exact (Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, U.1)).hom).2 hh).symm
  subst I
  refine ⟨e, ?_⟩
  rw [← Category.assoc, ← he]
  simp [t]

/-- Clause (1), Stacks Tags 01JU (1), 01I4, 01JQ, 01IN
(blueprint: lem-weil-pbc-quotient-base-change-closed-immersion-ideal).
Proof: (1) The associated ideal has sections K on Spec A, by
lem-weil-pbc-spec-module-tilde-sections; lem-weil-pbc-module-pullback-ideal-quotient
computes its extension on affine opens as KB. Ideals equal on this basis are equal by gluing.
(2) The quotient immersion is closed by lem-weil-pbc-closed-immersion-affine-cover-criterion;
lem-weil-pbc-closed-immersion-base-change makes its pullback closed.
(3) By lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-cartesian-square-pasting,
the preimage of U is the affine fibre product. Use lem-weil-pbc-fibre-product-affine-spectra
and lem-weil-pbc-tensor-quotient-base-change to identify it with Spec(B/KB).
(4) Its kernel on U is KB by def-sbc-closed-immersion-ideal-sheaf, giving the ideal equality.
-/
theorem quotientBaseChange_closedImmersion_ideal {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (K : Ideal A) :
    IsClosedImmersion
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) ∧
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))).ker =
        (Scheme.IdealSheafData.ofIdealTop
          (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f ∧
      ∀ U : X.affineOpens,
        IsAffineOpen
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ⁻¹ᵁ U.1) ∧
        ((Scheme.IdealSheafData.ofIdealTop
          (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).ideal U =
          K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom ∧
        ∃ e : (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ⁻¹ᵁ
              U.1).toScheme ≅
            Spec (CommRingCat.of (Γ(X, U.1) ⧸
              K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom)),
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
              (K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom))) ≫
            U.2.isoSpec.inv =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ∣_ U.1 := by
  let j := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))
  have : IsClosedImmersion j := inferInstanceAs
    (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))))
  have hk : j.ker = (Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      quotient_spec_ker (R := CommRingCat.of A) K]
  refine ⟨inferInstance, hk, fun U ↦ ?_⟩
  have hs : ((Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).ideal U =
      K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom := by
    rw [Scheme.IdealSheafData.ideal_comap_appLE _ f
      ⟨⊤, isAffineOpen_top _⟩ U (by simp)]
    simp [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  refine ⟨U.2.preimage j, hs, ?_⟩
  have hku : j.ker.ideal U =
      K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom := by
    rw [hk, hs]
  rw [← hku]
  exact closedImmersion_affine_quotient j U

/-- Clause (2), Stacks Tag 01IN, the affine ideal calculation
(blueprint: lem-weil-pbc-quotient-base-change-closed-immersion-ideal).
Proof: (5) By the affine sections computation in step (1), the two sides have sections
(KB)(K'B) and (KK')B. Both are generated by the images of products kk', hence agree.
Glue this equality on the affine basis. Induction using this product formula proves the
power formula for every m ≥ 1. Products and powers are def-sbc-ideal-sheaf-powers.
-/
theorem quotientBaseChange_extendedIdeal_mul_pow {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    (∀ K K' : Ideal A,
      (Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso
          (CommRingCat.of A)).inv.hom)).comap f *
          (Scheme.IdealSheafData.ofIdealTop (K'.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f =
        (Scheme.IdealSheafData.ofIdealTop ((K * K').map (Scheme.ΓSpecIso
            (CommRingCat.of A)).inv.hom)).comap f) ∧
      ∀ (K : Ideal A) (m : ℕ), 1 ≤ m →
        (Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso
            (CommRingCat.of A)).inv.hom)).comap f ^ m =
          (Scheme.IdealSheafData.ofIdealTop ((K ^ m).map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f := by
  have sections (K : Ideal A) (U : X.affineOpens) :
      ((Scheme.IdealSheafData.ofIdealTop
        (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f).ideal U =
        K.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom := by
    rw [Scheme.IdealSheafData.ideal_comap_appLE _ f
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ U (by simp)]
    simp [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  constructor
  · intro K K'
    apply Scheme.IdealSheafData.ext
    funext U
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    rw [sections K U, sections K' U, sections (K * K') U, Ideal.map_mul]
  · intro K m hm
    apply Scheme.IdealSheafData.ext
    funext U
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    rw [sections K U, sections (K ^ m) U, Ideal.map_pow]

/-- Clause (3), Stacks Tag 01JU (1) over Spec(A/J), and Remark 088F
(blueprint: lem-weil-pbc-quotient-base-change-closed-immersion-ideal).
Proof: (6) The quotient map A/J → A/J' and def-pc-fibre-product give the unique transition
with the two projection identities. By lem-weil-pbc-cartesian-square-pasting its square
with Spec(A/J') → Spec(A/J) is cartesian.
(7) Apply steps (2)-(4) over A/J to J'/J. On affine opens its extension equals the extension
of J' along A → A/J, since the generating images agree. The quotient
(B/JB)/(J'B/JB) is B/J'B, compatibly with the quotient maps, yielding the affine description.
-/
theorem quotientBaseChange_nestedIdeals {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (J J' : Ideal A) (h : J ≤ J') :
    ∃ i : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))),
      (i ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ∧
        i ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ∧
      (∀ i' : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))),
        i' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) →
        i' ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) →
        i' = i) ∧
      IsClosedImmersion i ∧
      i.ker = (Scheme.IdealSheafData.ofIdealTop (J'.map (Scheme.ΓSpecIso
          (CommRingCat.of A)).inv.hom)).comap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ f) ∧
      ∀ U : X.affineOpens,
        ∃ (e : (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk J))) ⁻¹ᵁ U.1).toScheme ≅
            Spec (CommRingCat.of (Γ(X, U.1) ⧸
              J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom)))
          (e' : (pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk J'))) ⁻¹ᵁ U.1).toScheme ≅
            Spec (CommRingCat.of (Γ(X, U.1) ⧸
              J'.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom))),
          e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
              (J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom))) ≫
              U.2.isoSpec.inv =
            pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ∣_ U.1 ∧
          e'.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
              (J'.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom))) ≫
              U.2.isoSpec.inv =
            pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) ∣_ U.1 ∧
          e'.hom ≫ Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.factor (Ideal.map_mono h))) ≫ e.inv ≫
              (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ U.1).ι =
            (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk J'))) ⁻¹ᵁ U.1).ι ≫ i := by
  let cJ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let cJ' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))
  let c := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))
  have hc : c ≫ cJ = cJ' := by
    rw [← Spec.map_comp]
    congr 1
  let j := pullback.fst f cJ
  let j' := pullback.fst f cJ'
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion
    (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
  have : IsClosedImmersion j' := inferInstanceAs (IsClosedImmersion
    (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')))))
  have hw : j' ≫ f = (pullback.snd f cJ' ≫ c) ≫ cJ := by
    rw [Category.assoc, hc, pullback.condition]
  let i := pullback.lift j' (pullback.snd f cJ' ≫ c) hw
  have hi : i ≫ j = j' := pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd f cJ = pullback.snd f cJ' ≫ c :=
    pullback.lift_snd _ _ _
  have : IsClosedImmersion (i ≫ j) := hi ▸ inferInstance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i j
  have hk : i.ker = (Scheme.IdealSheafData.ofIdealTop
      (J'.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap (j ≫ f) := by
    rw [Scheme.IdealSheafData.comap_comp,
      ← (quotientBaseChange_closedImmersion_ideal f J').2.1]
    change i.ker = j'.ker.comap j
    rw [← hi, Scheme.Hom.ker_comp,
      Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
  refine ⟨i, ⟨hi, hi₂⟩, ?_, inferInstance, hk, ?_⟩
  · intro i' hi' hi₂'
    apply pullback.hom_ext
    · exact hi'.trans hi.symm
    · exact hi₂'.trans hi₂.symm
  · intro U
    obtain ⟨e, he⟩ := ((quotientBaseChange_closedImmersion_ideal f J).2.2 U).2.2
    obtain ⟨e', he'⟩ := ((quotientBaseChange_closedImmersion_ideal f J').2.2 U).2.2
    refine ⟨e, e', he, he', ?_⟩
    have heι := congrArg (fun g ↦ g ≫ U.1.ι) he
    rw [morphismRestrict_ι] at heι
    have heι' := congrArg (fun g ↦ g ≫ U.1.ι) he'
    rw [morphismRestrict_ι] at heι'
    have hq : Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.map_mono h))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            f.appLE ⊤ U.1 le_top).hom))) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (J'.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            f.appLE ⊤ U.1 le_top).hom))) := by
      rw [← Spec.map_comp]
      congr 1
    apply (cancel_mono j).1
    simp only [Category.assoc, hi]
    rw [← heι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc _ _ (U.2.isoSpec.inv ≫ U.1.ι), hq]
    simpa only [Category.assoc] using heι'

/-- Clause (4), Stacks Tags 01JU (1) and 01IN
(blueprint: lem-weil-pbc-quotient-base-change-closed-immersion-ideal).
Proof: (8) Step (1) gives sections LB for L O_X and KB for the immersion ideal.
By lem-weil-pbc-closed-immersion-pushforward-ideal-powers, extending L O_X has sections
LB · (B/KB). Applying step (1) to X_K over Spec A gives the same generators, namely the
images of L in B/KB. The preimages of affine opens form a basis because j_K is a closed
embedding. Gluing on that basis gives equality of the two extended ideals.
-/
theorem quotientBaseChange_extendedIdeal_comap {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (K L : Ideal A) :
    ((Scheme.IdealSheafData.ofIdealTop (L.map (Scheme.ΓSpecIso
        (CommRingCat.of A)).inv.hom)).comap f).comap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) =
        (Scheme.IdealSheafData.ofIdealTop (L.map (Scheme.ΓSpecIso
            (CommRingCat.of A)).inv.hom)).comap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ≫ f) ∧
      ∀ U : X.affineOpens,
        ∃ hW : IsAffineOpen (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk K))) ⁻¹ᵁ U.1),
        (((Scheme.IdealSheafData.ofIdealTop (L.map (Scheme.ΓSpecIso
            (CommRingCat.of A)).inv.hom)).comap f).comap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))))).ideal
            ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ⁻¹ᵁ U.1, hW⟩ =
          (L.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom).map
            ((pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))).app U.1).hom ∧
        ((Scheme.IdealSheafData.ofIdealTop (L.map (Scheme.ΓSpecIso
            (CommRingCat.of A)).inv.hom)).comap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ≫ f)).ideal
            ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) ⁻¹ᵁ U.1, hW⟩ =
          (L.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom).map
            ((pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk K)))).app U.1).hom := by
  let j := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))
  let I := Scheme.IdealSheafData.ofIdealTop
    (L.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  have hc : (I.comap f).comap j = I.comap (j ≫ f) :=
    (Scheme.IdealSheafData.comap_comp I j f).symm
  refine ⟨hc, fun U ↦ ?_⟩
  have : IsClosedImmersion j := inferInstanceAs
    (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))))
  have hW := U.2.preimage j
  refine ⟨hW, ?_⟩
  have hs : (I.comap f).ideal U =
      L.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 le_top).hom := by
    rw [Scheme.IdealSheafData.ideal_comap_appLE I f
      ⟨⊤, isAffineOpen_top _⟩ U (by simp)]
    simp [I, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  have hw : ((I.comap f).comap j).ideal ⟨j ⁻¹ᵁ U.1, hW⟩ =
      ((I.comap f).ideal U).map (j.app U.1).hom := by
    simpa [Scheme.Hom.app_eq_appLE] using
      Scheme.IdealSheafData.ideal_comap_appLE (I.comap f) j U
        ⟨j ⁻¹ᵁ U.1, hW⟩ le_rfl
  constructor
  · exact hw.trans (congrArg (Ideal.map (j.app U.1).hom) hs)
  · rw [← hc]
    exact hw.trans (congrArg (Ideal.map (j.app U.1).hom) hs)


end AlgebraicGeometry
