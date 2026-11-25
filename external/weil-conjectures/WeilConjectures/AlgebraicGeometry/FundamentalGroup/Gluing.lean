/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing finite étale schemes

Let `X = A ⊔_D B` be the pushout of two open immersions `D ⟶ A` and `D ⟶ B`, i.e. a scheme
covered by two opens `A` and `B` meeting in `D`. Finite étale schemes `P_A` over `A` and `P_B`
over `B` whose restrictions to `D` are isomorphic glue to a finite étale scheme over `X`
restricting to `P_A` and `P_B`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_inl_iso`): the glued scheme is the pushout
`P_A ⊔_{P_D} P_B`, whose charts are the base changes of `P_A` and `P_B` because the squares of
the morphism of spans are cartesian, and finiteness and étaleness are local on the target.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {D A B : Scheme.{u}} (dA : D ⟶ A) (dB : D ⟶ B) [IsOpenImmersion dA]
  [IsOpenImmersion dB]

/-- The isomorphism in `FÉt(Y)` attached to a cartesian square `P ⟶ Q.obj.left` over
`f : Y ⟶ X`. -/
noncomputable def isoPullbackOfIsPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (P : Y.FiniteEtale)
    (Q : X.FiniteEtale) (h : P.obj.left ⟶ Q.obj.left)
    (H : IsPullback h P.obj.hom Q.obj.hom f) : (pullback f).obj Q ≅ P :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk H.isoPullback.symm
    (by simp))

/-- **Gluing finite étale schemes** over the pushout `A ⊔_D B` of two open immersions: finite
étale schemes over `A` and over `B` with isomorphic restrictions to `D` glue to a finite étale
scheme over `A ⊔_D B` restricting to the given ones. For the span and its pushout

```
  D ──dB──▶ B
  │         │
 dA        inr
  ▼         ▼
  A ──inl─▶ A ⊔_D B
```

and finite étale `P_A ⟶ A`, `P_B ⟶ B` with `dA^* P_A ≅ dB^* P_B`, there is a finite étale
`P ⟶ A ⊔_D B` with `inl^* P ≅ P_A` and `inr^* P ≅ P_B`; it is the pushout
`P_A ⊔_{P_D} P_B`, and the squares

```
  P_A ──▶ P          P_B ──▶ P
   │      │           │      │
   ▼      ▼           ▼      ▼
   A ──▶ A ⊔_D B      B ──▶ A ⊔_D B
```

are cartesian. -/
theorem exists_pullback_inl_iso (PA : A.FiniteEtale) (PB : B.FiniteEtale)
    (e : (pullback dA).obj PA ≅ (pullback dB).obj PB) :
    ∃ P : (Limits.pushout dA dB).FiniteEtale,
      Nonempty ((pullback (Limits.pushout.inl dA dB)).obj P ≅ PA) ∧
        Nonempty ((pullback (Limits.pushout.inr dA dB)).obj P ≅ PB) := by
  have : IsFinite PA.obj.hom := PA.property
  have : Etale PA.obj.hom := PA.obj.prop
  have : IsFinite PB.obj.hom := PB.property
  have : Etale PB.obj.hom := PB.obj.prop
  let f' : Limits.pullback PA.obj.hom dA ⟶ PA.obj.left := Limits.pullback.fst PA.obj.hom dA
  let γ : Limits.pullback PA.obj.hom dA ⟶ D := Limits.pullback.snd PA.obj.hom dA
  let g' : Limits.pullback PA.obj.hom dA ⟶ PB.obj.left :=
    e.hom.hom.left ≫ Limits.pullback.fst PB.obj.hom dB
  have he : e.hom.hom.left ≫ Limits.pullback.snd PB.obj.hom dB = γ := hom_left_comp e.hom
  have hf : γ ≫ dA = f' ≫ PA.obj.hom := (Limits.pullback.condition).symm
  have hg : γ ≫ dB = g' ≫ PB.obj.hom := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, he]
  have hinv : e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ :=
    congrArg (fun φ ↦ φ.hom.left) e.inv_hom_id
  have HA : IsPullback γ f' dA PA.obj.hom := (IsPullback.of_hasPullback PA.obj.hom dA).flip
  have HB : IsPullback γ g' dB PB.obj.hom := by
    have h₀ := (IsPullback.of_hasPullback PB.obj.hom dB).flip
    let eL : Limits.pullback PA.obj.hom dA ≅ Limits.pullback PB.obj.hom dB :=
      (ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso e
    refine h₀.of_iso eL.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he]
      simp only [Functor.mapIso_inv, Functor.comp_map, ObjectProperty.ι_map,
        MorphismProperty.Comma.forget_map, Over.forget_map, ← Category.assoc, hinv, eL]
      exact
        (Category.id_comp (Limits.pullback.snd PB.obj.hom dB)).symm
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, g']
      simp only [Functor.mapIso_inv, Functor.comp_map, ObjectProperty.ι_map,
        MorphismProperty.Comma.forget_map, Over.forget_map, ← Category.assoc, hinv, eL]
      exact
        (Category.id_comp (Limits.pullback.fst PB.obj.hom dB)).symm
  let q := Limits.pushout.map f' g' dA dB PA.obj.hom PB.obj.hom γ hf.symm hg.symm
  have hinl := isPullback_pushout_map_inl_of_isPullback dA dB f' g' PA.obj.hom PB.obj.hom γ hf hg
    HB
  have hinr := isPullback_pushout_map_inr_of_isPullback dA dB f' g' PA.obj.hom PB.obj.hom γ hf hg
    HA
  have hP (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (hA : P PA.obj.hom)
      (hB : P PB.obj.hom) : P q := by
    refine IsZariskiLocalAtTarget.of_openCover (IsOpenImmersion.pushoutCover dA dB) fun i ↦ ?_
    cases i with
    | left =>
      refine (P.arrow_mk_iso_iff (Arrow.isoMk hinl.flip.isoPullback (Iso.refl _) ?_)).1 hA
      exact hinl.flip.isoPullback_hom_snd
    | right =>
      refine (P.arrow_mk_iso_iff (Arrow.isoMk hinr.flip.isoPullback (Iso.refl _) ?_)).1 hB
      exact hinr.flip.isoPullback_hom_snd
  let P : (Limits.pushout dA dB).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ q (hP @Etale inferInstance inferInstance),
      hP @IsFinite inferInstance inferInstance⟩
  exact ⟨P, ⟨isoPullbackOfIsPullback _ PA P _ hinl.flip⟩,
    ⟨isoPullbackOfIsPullback _ PB P _ hinr.flip⟩⟩

section PullbackIsos

variable {X Y W : Scheme.{u}}

/-- Base change of finite étale schemes along a composite is the composite of the base
changes. -/
noncomputable def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ W) (P : W.FiniteEtale) :
    (pullback (f ≫ g)).obj P ≅ (pullback f).obj ((pullback g).obj P) :=
  isoPullbackOfIsPullback (f ≫ g) ((pullback f).obj ((pullback g).obj P)) P
    (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
    ((IsPullback.of_hasPullback _ f).paste_horiz (IsPullback.of_hasPullback P.obj.hom g))

/-- Base change of finite étale schemes along the identity. -/
noncomputable def pullbackIdIso (P : X.FiniteEtale) : (pullback (𝟙 X)).obj P ≅ P :=
  isoPullbackOfIsPullback (𝟙 X) P P (𝟙 _) (IsPullback.id_horiz P.obj.hom)

end PullbackIsos

section Cover

variable {X : Scheme.{u}} (iA : A ⟶ X) (iB : B ⟶ X) [IsOpenImmersion iA]
  [IsOpenImmersion iB] (H : IsPullback dA dB iA iB)

omit [IsOpenImmersion iB] in
include H in
lemma preimage_opensRange_pushout_desc_inl :
    Limits.pushout.desc iA iB H.w ⁻¹ᵁ iA.opensRange =
      (Limits.pushout.inl dA dB).opensRange := by
  apply le_antisymm
  · intro x hx
    have hcov : x ∈ Set.range (Limits.pushout.inl dA dB) ∪
        Set.range (Limits.pushout.inr dA dB) := by
      rw [range_pushout_inl_union_range_pushout_inr]; trivial
    obtain (hmem | ⟨b, rfl⟩) := hcov
    · exact hmem
    · obtain ⟨a, ha⟩ := hx
      have hb : iB b = iA a := by
        rw [ha, ← Scheme.Hom.comp_apply, Limits.pushout.inr_desc]
      obtain ⟨d, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback H a b hb.symm
      refine ⟨dA d, ?_⟩
      rw [← Scheme.Hom.comp_apply, Limits.pushout.condition, Scheme.Hom.comp_apply]
  · rintro x ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.pushout.inl_desc]

omit [IsOpenImmersion iA] in
include H in
lemma preimage_opensRange_pushout_desc_inr :
    Limits.pushout.desc iA iB H.w ⁻¹ᵁ iB.opensRange =
      (Limits.pushout.inr dA dB).opensRange := by
  apply le_antisymm
  · intro x hx
    have hcov : x ∈ Set.range (Limits.pushout.inl dA dB) ∪
        Set.range (Limits.pushout.inr dA dB) := by
      rw [range_pushout_inl_union_range_pushout_inr]; trivial
    obtain (⟨a, rfl⟩ | hmem) := hcov
    · obtain ⟨b, hb⟩ := hx
      have ha : iA a = iB b := by
        rw [hb, ← Scheme.Hom.comp_apply, Limits.pushout.inl_desc]
      obtain ⟨d, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback H a b ha
      refine ⟨dB d, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Limits.pushout.condition, Scheme.Hom.comp_apply]
    · exact hmem
  · rintro x ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.pushout.inr_desc]

include H in
/-- A scheme covered by two open immersions `A ⟶ X` and `B ⟶ X` meeting in `D` is the pushout
`A ⊔_D B`: if the square

```
  D ──dB──▶ B
  │         │
 dA        iB
  ▼         ▼
  A ──iA──▶ X
```

is cartesian and the images of `iA` and `iB` cover `X`, then the induced map
`pushout.desc iA iB : A ⊔_D B ⟶ X` is an isomorphism. -/
lemma isIso_pushout_desc (hcov : ∀ x, x ∈ Set.range iA ∨ x ∈ Set.range iB) :
    IsIso (Limits.pushout.desc iA iB H.w) := by
  rw [← MorphismProperty.isomorphisms.iff]
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool (fun b ↦ cond b A B)
    (fun b ↦ match b with | true => iA | false => iB) (fun x ↦ by
      rcases hcov x with ⟨a, ha⟩ | ⟨b, hb⟩
      exacts [⟨true, a, ha⟩, ⟨false, b, hb⟩])
    (fun b ↦ by cases b <;> infer_instance)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun b ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  match b with
  | true =>
    have h := (IsOpenImmersion.isPullback (𝟙 A) (Limits.pushout.inl dA dB) iA _
      (by simp) (preimage_opensRange_pushout_desc_inl dA dB iA iB H)).flip
    change IsIso (Limits.pullback.snd (Limits.pushout.desc iA iB H.w) iA)
    have e : Limits.pullback.snd (Limits.pushout.desc iA iB H.w) iA = h.isoPullback.inv := by
      rw [← Category.id_comp (Limits.pullback.snd _ iA), ← h.isoPullback.inv_hom_id,
        Category.assoc, IsPullback.isoPullback_hom_snd, Category.comp_id]
    rw [e]
    infer_instance
  | false =>
    have h := (IsOpenImmersion.isPullback (𝟙 B) (Limits.pushout.inr dA dB) iB _
      (by simp) (preimage_opensRange_pushout_desc_inr dA dB iA iB H)).flip
    change IsIso (Limits.pullback.snd (Limits.pushout.desc iA iB H.w) iB)
    have e : Limits.pullback.snd (Limits.pushout.desc iA iB H.w) iB = h.isoPullback.inv := by
      rw [← Category.id_comp (Limits.pullback.snd _ iB), ← h.isoPullback.inv_hom_id,
        Category.assoc, IsPullback.isoPullback_hom_snd, Category.comp_id]
    rw [e]
    infer_instance

include H in
/-- **Gluing finite étale schemes** over a scheme `X` covered by two open immersions `A ⟶ X`,
`B ⟶ X` meeting in `D`: finite étale schemes over `A` and over `B` with isomorphic restrictions
to `D` glue to a finite étale scheme over `X` restricting to the one over `A`. Here the square

```
  D ──dB──▶ B
  │         │
 dA        iB
  ▼         ▼
  A ──iA──▶ X
```

is cartesian, the images of `iA` and `iB` cover `X`, and `X ≅ A ⊔_D B` by
`AlgebraicGeometry.Scheme.FiniteEtale.isIso_pushout_desc`. -/
theorem exists_pullback_iso_of_isPullback (hcov : ∀ x, x ∈ Set.range iA ∨ x ∈ Set.range iB)
    (PA : A.FiniteEtale) (PB : B.FiniteEtale) (e : (pullback dA).obj PA ≅ (pullback dB).obj PB) :
    ∃ P : X.FiniteEtale, Nonempty ((pullback iA).obj P ≅ PA) := by
  have := isIso_pushout_desc dA dB iA iB H hcov
  obtain ⟨P', ⟨eA⟩, -⟩ := exists_pullback_inl_iso dA dB PA PB e
  have h : iA ≫ inv (Limits.pushout.desc iA iB H.w) = Limits.pushout.inl dA dB := by
    rw [IsIso.comp_inv_eq, Limits.pushout.inl_desc]
  exact ⟨(pullback (inv (Limits.pushout.desc iA iB H.w))).obj P',
    ⟨(pullbackCompIso _ _ _).symm ≪≫ eqToIso (by rw [h]) ≪≫ eA⟩⟩

end Cover

end AlgebraicGeometry.Scheme.FiniteEtale
