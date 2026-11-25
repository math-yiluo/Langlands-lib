/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality

/-!
# Strict henselizations at compatible geometric points

Let `g : T ⟶ S` be a morphism of schemes, `s : Spec Ω ⟶ S` and `t : Spec Ω' ⟶ T` geometric
points and `ι : Spec Ω' ⟶ Spec Ω` a morphism with `ι ≫ s = t ≫ g`. This generalises the
situation of `AlgebraicGeometry.Scheme.strictHenselizationMap`, where `s = t ≫ g` and `ι` is
the identity: the two points may have different fields.

We construct the local homomorphism `φ : 𝒪^{sh}_{S,s} ⟶ 𝒪^{sh}_{T,t}` of strict henselizations
(`AlgebraicGeometry.Scheme.strictHenselizationHom`). For an affine pointed étale neighbourhood
`(V, v)` of `s`, the composite `T_(t) ⟶ S_(s) ⟶ V` is the unique morphism over `S` through which
`ι ≫ v` factors. The map `Spec φ` is compatible with the structure morphisms to `S` and `T`, and
`φ` is compatible with the evaluations at the geometric points through `ι`; hence `φ` is local and
the induced map of residue fields commutes with the embeddings of the residue fields into `Ω`
and `Ω'`.

## Main definitions

- `AlgebraicGeometry.Scheme.strictHenselizationHom`: the map `𝒪^{sh}_{S,s} ⟶ 𝒪^{sh}_{T,t}`.

## Main statements

- `AlgebraicGeometry.Scheme.spec_map_strictHenselizationHom_comp_strictLocalizationToBase`:
  compatibility with the structure morphisms.
- `AlgebraicGeometry.Scheme.spec_map_strictHenselizationEval_comp_spec_map_strictHenselizationHom`:
  compatibility with the geometric points.
- `AlgebraicGeometry.Scheme.residueFieldMap_strictHenselizationHom_comp`: the residue square.

## References

- Stacks Project, Lemma 59.33.1, <https://stacks.math.columbia.edu/tag/04HX>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} (g : T ⟶ S) {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω]
  [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ T)
  (ι : Spec (.of Ω') ⟶ Spec (.of Ω)) (h : ι ≫ s = t ≫ g)

include h in
lemma strictLocalizationLiftOf_aux (x : AffinePointedEtaleNeighborhood s) :
    ∃! φ : strictLocalization t ⟶ x.obj.1.left,
      φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g ∧
        Spec.map (strictHenselizationEval t) ≫ φ = ι ≫ x.obj.2.left := by
  have : Etale x.obj.1.hom := x.obj.1.prop
  refine existsUnique_lift_of_etale (strictHenselizationEval t)
    (maximalIdeal_strictHenselization (s := t)).symm _ _ _ ?_
  rw [Category.assoc]
  refine (congrArg (ι ≫ ·) (CategoryTheory.Over.w x.obj.2)).trans ?_
  rw [← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
  exact h

/-- For an affine pointed étale neighbourhood `(V, v)` of `s`, the unique morphism
`T_(t) ⟶ V` over `S` (via `T_(t) ⟶ T ⟶ S`) through which `ι ≫ v` factors as
`Spec Ω' ⟶ T_(t) ⟶ V`. -/
noncomputable def strictLocalizationLiftOf (x : AffinePointedEtaleNeighborhood s) :
    strictLocalization t ⟶ x.obj.1.left :=
  (strictLocalizationLiftOf_aux g s t ι h x).exists.choose

@[reassoc]
lemma strictLocalizationLiftOf_comp_hom (x : AffinePointedEtaleNeighborhood s) :
    strictLocalizationLiftOf g s t ι h x ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g :=
  (strictLocalizationLiftOf_aux g s t ι h x).exists.choose_spec.1

@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationLiftOf
    (x : AffinePointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationEval t) ≫ strictLocalizationLiftOf g s t ι h x =
      ι ≫ x.obj.2.left :=
  (strictLocalizationLiftOf_aux g s t ι h x).exists.choose_spec.2

/-- Uniqueness of `strictLocalizationLiftOf`. -/
lemma eq_strictLocalizationLiftOf (x : AffinePointedEtaleNeighborhood s)
    (φ : strictLocalization t ⟶ x.obj.1.left)
    (h₁ : φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g)
    (h₂ : Spec.map (strictHenselizationEval t) ≫ φ = ι ≫ x.obj.2.left) :
    φ = strictLocalizationLiftOf g s t ι h x :=
  (strictLocalizationLiftOf_aux g s t ι h x).unique ⟨h₁, h₂⟩
    ⟨strictLocalizationLiftOf_comp_hom g s t ι h x,
      spec_map_strictHenselizationEval_comp_strictLocalizationLiftOf g s t ι h x⟩

/-- The local homomorphism `𝒪^{sh}_{S,s} ⟶ 𝒪^{sh}_{T,t}` of strict henselizations induced by
`g: T ⟶ S` and the morphism `ι: Spec Ω' ⟶ Spec Ω` of the fields of the geometric points with
`ι ≫ s = t ≫ g`. -/
noncomputable def strictHenselizationHom :
    strictHenselization s ⟶ strictHenselization t :=
  colimit.desc (strictHenselizationDiagram s)
    { pt := strictHenselization t
      ι :=
        { app x := Scheme.Γ.map (strictLocalizationLiftOf g s t ι h x.unop).op ≫
            (Scheme.ΓSpecIso (strictHenselization t)).hom
          naturality x y f := by
            have h' : strictLocalizationLiftOf g s t ι h y.unop ≫ f.unop.hom.1.left =
                strictLocalizationLiftOf g s t ι h x.unop := by
              refine eq_strictLocalizationLiftOf g s t ι h _ _ ?_ ?_
              · rw [Category.assoc, ← strictLocalizationLiftOf_comp_hom g s t ι h y.unop]
                congr 1
                exact f.unop.hom.1.w.trans (Category.comp_id _)
              · rw [spec_map_strictHenselizationEval_comp_strictLocalizationLiftOf_assoc]
                exact congrArg (ι ≫ ·) (congrArg CommaMorphism.left f.unop.hom.2)
            change Scheme.Γ.map f.unop.hom.1.left.op ≫ Scheme.Γ.map _ ≫ _ =
              (Scheme.Γ.map _ ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← h', op_comp, Scheme.Γ.map_comp, Category.assoc] } }

set_option backward.isDefEq.respectTransparency false in
/-- The composite `T_(t) ⟶ S_(s) ⟶ V` is `strictLocalizationLiftOf g s t ι h x`. -/
@[reassoc]
lemma spec_map_strictHenselizationHom_comp_strictLocalizationCone_π_app
    (x : AffinePointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationHom g s t ι h) ≫ (strictLocalizationCone s).π.app x =
      strictLocalizationLiftOf g s t ι h x := by
  have hy : Spec.map (Scheme.Γ.map (strictLocalizationLiftOf g s t ι h x).op ≫
      (Scheme.ΓSpecIso (strictHenselization t)).hom) =
      strictLocalizationLiftOf g s t ι h x ≫ x.obj.1.left.toSpecΓ := by
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Γ_map_op, Scheme.toSpecΓ_naturality]
  rw [strictLocalizationCone_π_app, ← Spec.map_comp_assoc, strictHenselizationHom,
    colimit.ι_desc]
  change Spec.map (Scheme.Γ.map (strictLocalizationLiftOf g s t ι h x).op ≫
      (Scheme.ΓSpecIso (strictHenselization t)).hom) ≫ inv x.obj.1.left.toSpecΓ = _
  rw [hy, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- `Spec` of `strictHenselizationHom` is compatible with the structure morphisms:
`j_S ∘ Spec φ = g ∘ j_T`. -/
@[reassoc]
lemma spec_map_strictHenselizationHom_comp_strictLocalizationToBase :
    Spec.map (strictHenselizationHom g s t ι h) ≫ strictLocalizationToBase s =
      strictLocalizationToBase t ≫ g := by
  obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood s)
  rw [← strictLocalizationCone_π_app_hom s x,
    spec_map_strictHenselizationHom_comp_strictLocalizationCone_π_app_assoc,
    strictLocalizationLiftOf_comp_hom]

/-- `strictHenselizationHom` is compatible with the geometric points: the closed geometric point
`Spec Ω' ⟶ T_(t)` followed by `Spec φ` is `ι` followed by the closed geometric point
`Spec Ω ⟶ S_(s)`. -/
@[reassoc]
lemma spec_map_strictHenselizationEval_comp_spec_map_strictHenselizationHom :
    Spec.map (strictHenselizationEval t) ≫ Spec.map (strictHenselizationHom g s t ι h) =
      ι ≫ Spec.map (strictHenselizationEval s) := by
  refine (isLimitStrictLocalizationCone s).hom_ext fun x ↦ ?_
  rw [Category.assoc, spec_map_strictHenselizationHom_comp_strictLocalizationCone_π_app,
    spec_map_strictHenselizationEval_comp_strictLocalizationLiftOf, Category.assoc,
    spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app]

/-- `strictHenselizationHom` is compatible with the evaluations at the geometric points, as ring
maps: `ev_t ∘ φ = ι^♯ ∘ ev_s`. -/
lemma strictHenselizationHom_comp_strictHenselizationEval :
    strictHenselizationHom g s t ι h ≫ strictHenselizationEval t =
      strictHenselizationEval s ≫ Spec.preimage ι := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage,
    spec_map_strictHenselizationEval_comp_spec_map_strictHenselizationHom]

lemma strictHenselizationEval_strictHenselizationHom (a : ↑(strictHenselization s)) :
    strictHenselizationEval t (strictHenselizationHom g s t ι h a) =
      Spec.preimage ι (strictHenselizationEval s a) := by
  rw [← CommRingCat.comp_apply, strictHenselizationHom_comp_strictHenselizationEval,
    CommRingCat.comp_apply]

/-- `strictHenselizationHom` is a local homomorphism. -/
instance isLocalHom_strictHenselizationHom :
    IsLocalHom (strictHenselizationHom g s t ι h).hom := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [isUnit_iff_strictHenselizationEval_ne_zero] at ha ⊢
  change strictHenselizationEval t (strictHenselizationHom g s t ι h a) ≠ 0 at ha
  rw [strictHenselizationEval_strictHenselizationHom] at ha
  exact fun h0 ↦ ha (by rw [h0, map_zero])

/-- **The residue square**: the residue field map of `strictHenselizationHom` commutes with the
embeddings of the residue fields of the strict henselizations into `Ω` and `Ω'`. -/
lemma residueFieldMap_strictHenselizationHom_comp :
    (strictHenselizationResidueFieldEmb t).comp
        (ResidueField.map (strictHenselizationHom g s t ι h).hom) =
      (Spec.preimage ι).hom.comp (strictHenselizationResidueFieldEmb s) := by
  refine RingHom.ext fun a ↦ ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.comp_apply, ResidueField.map_residue,
    strictHenselizationResidueFieldEmb_residue]
  exact strictHenselizationEval_strictHenselizationHom g s t ι h a

end AlgebraicGeometry.Scheme
