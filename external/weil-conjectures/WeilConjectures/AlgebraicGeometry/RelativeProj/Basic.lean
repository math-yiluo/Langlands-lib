/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedAlgebraData
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Relative `Proj` of a quasi-coherent graded algebra

Let `A: X.GradedAlgebraData` be a quasi-coherent graded `𝒪_X`-algebra. We construct its
relative `Proj` by relative gluing (`Scheme.Cover.RelativeGluingData`) of the schemes
`Proj (A(V))` over the locally directed cover of `X` by all of its affine opens, exactly as for
the blow-up in `WeilConjectures.Blowup.Gluing`. Since the index category is a thin preorder, no
cocycle conditions appear: the overlap isomorphisms and their cocycle identities of the
usual gluing construction are replaced by the functoriality of `Proj.map` and by the fact that
the transition maps are base changes
(`AlgebraicGeometry.Proj.isPullback_map_of_isGradedBaseChangeAlong`).

## Main definitions

- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProj` — the relative `Proj` of `A`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjHom` — its structure morphism to `X`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjι` — the chart `Proj (A(V)) ⟶ relProj A`
  over an affine open `V`.

## Main results

- `AlgebraicGeometry.Scheme.GradedAlgebraData.isPullback_relProjι` — over every affine open `V`
  the relative `Proj` restricts to `Proj (A(V))`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.isPullback_relProjFunctor_map` and
  `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjFunctor_map_relProjι` — compatibility with
  iterated restriction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {X : Scheme.{u}} (A : X.GradedAlgebraData)

/-- The diagram `V ↦ Proj (A(V))` over the affine opens of `X`. -/
noncomputable def relProjFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := Proj (A.grading U)
  map {U V} f := Proj.map (A.res (leOfHom f)) (A.irrelevant_le_map_res (leOfHom f))
  map_id U :=
    (Proj.map_congr (A.res_id' U) _ (by simp)).trans Proj.map_id
  map_comp {U V W} f g :=
    (Proj.map_congr (A.res_comp (leOfHom f) (leOfHom g)).symm _
      (HomogeneousIdeal.irrelevant_le_map_comp (A.irrelevant_le_map_res (leOfHom g))
        (A.irrelevant_le_map_res (leOfHom f)))).trans
      (Proj.map_comp _ _ _ _)

@[simp]
lemma relProjFunctor_obj (U : X.affineOpens) :
    A.relProjFunctor.obj U = Proj (A.grading U) :=
  rfl

lemma relProjFunctor_map {U V : X.affineOpens} (f : U ⟶ V) :
    A.relProjFunctor.map f =
      Proj.map (A.res (leOfHom f)) (A.irrelevant_le_map_res (leOfHom f)) :=
  rfl

/-- The structure morphism `Proj (A(U)) ⟶ U` over an affine open `U`. -/
noncomputable def toOpen (U : X.affineOpens) : Proj (A.grading U) ⟶ U.1 :=
  Proj.toSpecOfAlgebra (A.grading U) ≫ U.2.isoSpec.inv

/-- The restriction squares of the local `Proj`s are pullbacks: for affine opens `U ≤ V`,
`Proj (A(U)) = U ×_V Proj (A(V))`. -/
lemma isPullback_relProjFunctor_map {U V : X.affineOpens} (h : U ≤ V) :
    IsPullback (A.relProjFunctor.map (homOfLE h)) (A.toOpen U) (A.toOpen V) (X.homOfLE h) := by
  have key := Proj.isPullback_map_of_isGradedBaseChangeAlong _ _ (A.isGradedBaseChangeAlong h)
  have w : Spec.map (CommRingCat.ofHom (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom) ≫
      V.2.isoSpec.inv = U.2.isoSpec.inv ≫ X.homOfLE h := by
    rw [CommRingCat.ofHom_hom]
    exact specMap_res_isoSpec_inv h
  exact key.paste_vert (IsPullback.of_vert_isIso ⟨w⟩)

/-- The structure maps of the local `Proj`s, as a natural transformation to the diagram of
affine opens of `X`. -/
noncomputable def relProjNatTrans :
    A.relProjFunctor ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := A.toOpen U
  naturality _ _ f := (A.isPullback_relProjFunctor_map (leOfHom f)).w

lemma relProjNatTrans_app (U : X.affineOpens) : A.relProjNatTrans.app U = A.toOpen U :=
  rfl

lemma relProjNatTrans_equifibered : A.relProjNatTrans.Equifibered := fun _ _ f ↦
  A.isPullback_relProjFunctor_map (leOfHom f)

/-- The relative gluing datum of the relative `Proj`. -/
noncomputable def relProjGluingData : X.directedAffineCover.RelativeGluingData where
  functor := A.relProjFunctor
  natTrans := A.relProjNatTrans
  equifibered := A.relProjNatTrans_equifibered

instance : (A.relProjFunctor ⋙ Scheme.forget).IsLocallyDirected :=
  inferInstanceAs ((A.relProjGluingData.functor ⋙ Scheme.forget).IsLocallyDirected)

instance : HasColimit A.relProjFunctor :=
  inferInstanceAs (HasColimit A.relProjGluingData.functor)

instance {U V : X.affineOpens} (f : U ⟶ V) : IsOpenImmersion (A.relProjFunctor.map f) :=
  inferInstanceAs (IsOpenImmersion (A.relProjGluingData.functor.map f))

/-- The **relative `Proj`** `Proj_X(𝒜)` of a quasi-coherent graded `𝒪_X`-algebra, obtained by
gluing the schemes `Proj (Γ(V, 𝒜))` over all affine opens `V` of `X`. -/
noncomputable def relProj : Scheme.{u} :=
  A.relProjGluingData.glued

/-- The structure morphism `Proj_X(𝒜) ⟶ X`, glued from the structure morphisms of the
`Proj (Γ(V, 𝒜))`. -/
noncomputable def relProjHom : A.relProj ⟶ X :=
  A.relProjGluingData.toBase

/-- The chart embedding `Proj (Γ(V, 𝒜)) ⟶ Proj_X(𝒜)` over an affine open `V`. -/
noncomputable def relProjι (U : X.affineOpens) : Proj (A.grading U) ⟶ A.relProj :=
  colimit.ι A.relProjFunctor U

instance (U : X.affineOpens) : IsOpenImmersion (A.relProjι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι A.relProjFunctor U))

/-- The chart embeddings are compatible with the structure morphisms. -/
@[reassoc (attr := simp)]
lemma relProjι_relProjHom (U : X.affineOpens) :
    A.relProjι U ≫ A.relProjHom = A.toOpen U ≫ U.1.ι :=
  A.relProjGluingData.ι_toBase U

/-- The preimage of an affine open under the structure morphism is the corresponding chart. -/
lemma relProjHom_preimage (U : X.affineOpens) :
    A.relProjHom ⁻¹ᵁ U.1 = (A.relProjι U).opensRange := by
  have h := A.relProjGluingData.toBase_preimage_eq_opensRange_ι U
  rwa [show (X.directedAffineCover.f U).opensRange = U.1 from
    Scheme.Opens.opensRange_ι U.1] at h

/-- **Affine restriction of the relative `Proj`**: over every affine open `V ⊆ X`, the relative
`Proj` restricts to `Proj (Γ(V, 𝒜))`, i.e. `Proj (Γ(V, 𝒜)) = V ×_X Proj_X(𝒜)` via the chart
embedding and the structure morphisms. -/
theorem isPullback_relProjι (U : X.affineOpens) :
    IsPullback (A.toOpen U) (A.relProjι U) U.1.ι A.relProjHom :=
  A.relProjGluingData.isPullback_natTrans_ι_toBase U

/-- The chart embeddings are compatible with further restriction: for affine opens `U ≤ V`, the
chart of `U` is the restriction morphism `Proj (A(U)) ⟶ Proj (A(V))` followed by the chart of
`V`. -/
@[reassoc (attr := simp)]
lemma relProjFunctor_map_relProjι {U V : X.affineOpens} (f : U ⟶ V) :
    A.relProjFunctor.map f ≫ A.relProjι V = A.relProjι U :=
  colimit.w A.relProjFunctor f

/-- The restriction morphism `Proj (A(U)) ⟶ Proj (A(V))` is `Proj` of the restriction map. -/
lemma relProjFunctor_map_homOfLE {U V : X.affineOpens} (h : U ≤ V) :
    A.relProjFunctor.map (homOfLE h) = Proj.map (A.res h) (A.irrelevant_le_map_res h) :=
  rfl

/-- The local structure morphism `Proj (A(U)) ⟶ U` is `Proj.toSpecOfAlgebra` followed by
`Spec Γ(X, U) ≅ U`. -/
lemma toOpen_eq (U : X.affineOpens) :
    A.toOpen U = Proj.toSpecOfAlgebra (A.grading U) ≫ U.2.isoSpec.inv :=
  rfl

/-- The restriction isomorphism `Proj (Γ(V, 𝒜)) ≅ V ×_X Proj_X(𝒜)` over an affine open `V`. -/
noncomputable def relProjRestrictIso (U : X.affineOpens) :
    Proj (A.grading U) ≅ pullback U.1.ι A.relProjHom :=
  (A.isPullback_relProjι U).isoPullback

@[reassoc (attr := simp)]
lemma relProjRestrictIso_hom_fst (U : X.affineOpens) :
    (A.relProjRestrictIso U).hom ≫ pullback.fst _ _ = A.toOpen U :=
  (A.isPullback_relProjι U).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma relProjRestrictIso_hom_snd (U : X.affineOpens) :
    (A.relProjRestrictIso U).hom ≫ pullback.snd _ _ = A.relProjι U :=
  (A.isPullback_relProjι U).isoPullback_hom_snd

/-- The restriction isomorphisms commute with further restriction: for affine opens `U ≤ V`, the
restriction morphism `Proj (A(U)) ⟶ Proj (A(V))` corresponds to the inclusion
`U ×_X Proj_X(𝒜) ⟶ V ×_X Proj_X(𝒜)`. -/
@[reassoc]
lemma relProjRestrictIso_hom_naturality {U V : X.affineOpens} (h : U ≤ V) :
    (A.relProjRestrictIso U).hom ≫
        pullback.map U.1.ι A.relProjHom V.1.ι A.relProjHom (X.homOfLE h) (𝟙 _) (𝟙 _)
          (by simp) (by simp) =
      A.relProjFunctor.map (homOfLE h) ≫ (A.relProjRestrictIso V).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, relProjRestrictIso_hom_fst_assoc,
      relProjRestrictIso_hom_fst]
    exact (A.isPullback_relProjFunctor_map h).w.symm
  · simp

end AlgebraicGeometry.Scheme.GradedAlgebraData
