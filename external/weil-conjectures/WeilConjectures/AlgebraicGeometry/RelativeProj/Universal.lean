/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Uniqueness and cover independence of the relative `Proj`

Let `A: X.GradedAlgebraData`. We show that the relative `Proj` is characterised by its affine
charts: if `P` is a scheme over `X` together with open immersions `Proj (A(V)) ⟶ P` for a
family of affine opens `V` that is closed under refinement around every point and covers `X`,
such that each chart is the preimage of `V` and the charts are compatible with restriction, then
`P` is the colimit of the corresponding diagram
(`AlgebraicGeometry.Scheme.GradedAlgebraData.isColimitOfIsPullback`).

Consequences:

- `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjIsoOfIsPullback` and
  `AlgebraicGeometry.Scheme.GradedAlgebraData.existsUnique_relProjIso`: any scheme over `X` with
  compatible chart identifications over all affine opens is isomorphic over `X` to the relative
  `Proj`, via a unique isomorphism compatible with the charts.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.isColimitRestrict`: the relative `Proj` is also
  glued from the charts of any covering family of affine opens which is closed under refinement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {X : Scheme.{u}} (A : X.GradedAlgebraData)

section General

variable {I : Type u} [Preorder I] {π : I → X.affineOpens} (hπ : Monotone π)
  {P : Scheme.{u}} (p : P ⟶ X) (j : ∀ i, Proj (A.grading (π i)) ⟶ P)
  (hj : ∀ i, IsPullback (A.toOpen (π i)) (j i) (π i).1.ι p)
  (hjc : ∀ {i i' : I} (h : i ≤ i'), A.relProjFunctor.map (homOfLE (hπ h)) ≫ j i' = j i)
  (hcov : ∀ x : X, ∃ i, x ∈ (π i).1)
  (hdir : ∀ (i i' : I) (x : X), x ∈ (π i).1 → x ∈ (π i').1 →
    ∃ k, k ≤ i ∧ k ≤ i' ∧ x ∈ (π k).1)

include hj in
omit [Preorder I] in
lemma isOpenImmersion_of_isPullback (i : I) : IsOpenImmersion (j i) :=
  (hj i).flip.isOpenImmersion_fst

omit [Preorder I] in
include hj in
lemma opensRange_of_isPullback (i : I) :
    have := A.isOpenImmersion_of_isPullback p j hj i
    (j i).opensRange = p ⁻¹ᵁ (π i).1 := by
  have := (hj i).flip.opensRange_fst
  rwa [Scheme.Opens.opensRange_ι] at this

include hj in
omit [Preorder I] in
lemma mem_of_isPullback (i : I) (y : Proj (A.grading (π i))) : p (j i y) ∈ (π i).1 := by
  rw [← Scheme.Hom.comp_apply, ← (hj i).w, Scheme.Hom.comp_apply]
  exact (Scheme.Opens.opensRange_ι (π i).1).le ⟨_, rfl⟩

/-- The open cover of `P` by the charts `j i`. -/
@[simps I₀ X f]
noncomputable def chartCover : P.OpenCover where
  I₀ := I
  X i := Proj (A.grading (π i))
  f := j
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ A.isOpenImmersion_of_isPullback p j hj i⟩
    obtain ⟨i, hi⟩ := hcov (p x)
    refine ⟨i, ?_⟩
    have := A.isOpenImmersion_of_isPullback p j hj i
    have hx : x ∈ (j i).opensRange := by
      rw [A.opensRange_of_isPullback p j hj i]
      exact hi
    exact hx

instance : Preorder (A.chartCover p j hj hcov).I₀ :=
  inferInstanceAs (Preorder I)

include hj hjc hdir in
lemma exists_lift_eq (i i' : I) (x : ↥(pullback (j i) (j i'))) :
    ∃ (k : I) (hki : k ≤ i) (hki' : k ≤ i') (w : Proj (A.grading (π k))),
      pullback.lift (f := j i) (g := j i') (A.relProjFunctor.map (homOfLE (hπ hki)))
        (A.relProjFunctor.map (homOfLE (hπ hki'))) (by rw [hjc hki, hjc hki']) w = x := by
  have := A.isOpenImmersion_of_isPullback p j hj
  set y := (pullback.fst (j i) (j i') ≫ j i) x with hy
  have hyi : p y ∈ (π i).1 := A.mem_of_isPullback p j hj i _
  have hyi' : p y ∈ (π i').1 := by
    rw [hy, pullback.condition]
    exact A.mem_of_isPullback p j hj i' _
  obtain ⟨k, hki, hki', hk⟩ := hdir i i' (p y) hyi hyi'
  have hyk : y ∈ (j k).opensRange := by
    rw [A.opensRange_of_isPullback p j hj k]
    exact hk
  obtain ⟨w, hw⟩ := hyk
  refine ⟨k, hki, hki', w, ?_⟩
  apply (pullback.fst (j i) (j i') ≫ j i).isOpenEmbedding.injective
  have e : pullback.lift (f := j i) (g := j i') (A.relProjFunctor.map (homOfLE (hπ hki)))
      (A.relProjFunctor.map (homOfLE (hπ hki'))) (by rw [hjc hki, hjc hki']) ≫
      (pullback.fst (j i) (j i') ≫ j i) = j k := by
    rw [pullback.lift_fst_assoc, hjc hki]
  have := congrArg (fun f ↦ f w) e
  simp only [Scheme.Hom.comp_apply] at this ⊢
  rw [this]
  exact hw.trans (by simp only [hy, Scheme.Hom.comp_apply])

include hdir in
/-- The chart cover is locally directed. -/
@[reducible] noncomputable def chartCoverLocallyDirected :
    (A.chartCover p j hj hcov).LocallyDirected where
  trans {i i'} h := A.relProjFunctor.map (homOfLE (hπ (leOfHom h)))
  trans_id i := by
    rw [show homOfLE (hπ (leOfHom (𝟙 i))) = 𝟙 (π i) from Subsingleton.elim _ _]
    exact A.relProjFunctor.map_id _
  trans_comp {i i' i''} h h' := by
    rw [← Functor.map_comp]
    exact congrArg A.relProjFunctor.map (Subsingleton.elim _ _)
  w h := hjc (leOfHom h)
  directed {i i'} x := by
    obtain ⟨k, hki, hki', w, hw⟩ := A.exists_lift_eq hπ p j hj hjc hdir i i' x
    exact ⟨k, homOfLE hki, homOfLE hki', w, hw⟩
  property_trans h := inferInstance

/-- **Characterisation of the relative `Proj` by its charts**: if a scheme `P` over `X` comes with
open embeddings of the `Proj (A(V))`, for a family of affine opens `V` covering `X` and closed
under refinement around every point, such that each chart is the preimage of `V` and the charts
are compatible with restriction, then `P` is the colimit of the charts. -/
noncomputable def isColimitOfIsPullback :
    IsColimit (Cocone.mk P
      { app i := j i
        naturality _ _ h := (hjc (leOfHom h)).trans (Category.comp_id _).symm } :
      Cocone (hπ.functor ⋙ A.relProjFunctor)) :=
  letI := A.chartCoverLocallyDirected hπ p j hj hjc hcov hdir
  OpenCover.isColimitCoconeOfLocallyDirected (A.chartCover p j hj hcov)

end General

section Unique

variable {X : Scheme.{u}}

lemma exists_affineOpens_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨⟨U, hU⟩, hx⟩

lemma exists_affineOpens_le (U V : X.affineOpens) (x : X) (hU : x ∈ U.1) (hV : x ∈ V.1) :
    ∃ W : X.affineOpens, W ≤ U ∧ W ≤ V ∧ x ∈ W.1 := by
  obtain ⟨W, hW, hx, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ U.1 ⊓ V.1 from ⟨hU, hV⟩)
  exact ⟨⟨W, hW⟩, hle.trans inf_le_left, hle.trans inf_le_right, hx⟩

variable (A : X.GradedAlgebraData) {P : Scheme.{u}} (p : P ⟶ X)
  (j : ∀ U : X.affineOpens, Proj (A.grading U) ⟶ P)
  (hj : ∀ U, IsPullback (A.toOpen U) (j U) U.1.ι p)
  (hjc : ∀ {U V : X.affineOpens} (h : U ≤ V), A.relProjFunctor.map (homOfLE h) ≫ j V = j U)

/-- A scheme `P` over `X` with compatible chart identifications `Proj (A(V)) ⟶ P` over all affine
opens `V` (each exhibiting `Proj (A(V))` as the preimage of `V`) is the colimit of the charts. -/
noncomputable def isColimitOfCharts :
    IsColimit (Cocone.mk P
      { app U := j U
        naturality _ _ h := (hjc (leOfHom h)).trans (Category.comp_id _).symm } :
      Cocone A.relProjFunctor) :=
  A.isColimitOfIsPullback (π := id) monotone_id p j hj (fun h ↦ hjc h)
    exists_affineOpens_mem exists_affineOpens_le

/-- The isomorphism between the relative `Proj` and any scheme over `X` with compatible chart
identifications over all affine opens. -/
noncomputable def relProjIsoOfIsPullback : A.relProj ≅ P :=
  (colimit.isColimit A.relProjFunctor).coconePointUniqueUpToIso (A.isColimitOfCharts p j hj hjc)

@[reassoc (attr := simp)]
lemma relProjι_relProjIsoOfIsPullback_hom (U : X.affineOpens) :
    A.relProjι U ≫ (A.relProjIsoOfIsPullback p j hj hjc).hom = j U :=
  (colimit.isColimit A.relProjFunctor).comp_coconePointUniqueUpToIso_hom _ U

/-- The isomorphism `relProjIsoOfIsPullback` lives over `X`. -/
@[reassoc (attr := simp)]
lemma relProjIsoOfIsPullback_hom_comp :
    (A.relProjIsoOfIsPullback p j hj hjc).hom ≫ p = A.relProjHom := by
  refine colimit.hom_ext fun U ↦ ?_
  change A.relProjι U ≫ _ = A.relProjι U ≫ _
  rw [relProjι_relProjIsoOfIsPullback_hom_assoc, relProjι_relProjHom, (hj U).w]

include hj hjc in
/-- **Uniqueness of the relative `Proj`**: any scheme `P` over `X` with chart identifications
`Proj (Γ(V, 𝒜)) ⟶ P` over all affine opens `V`, exhibiting `Proj (Γ(V, 𝒜))` as `V ×_X P` and
compatible with restriction, is isomorphic to `Proj_X(𝒜)` via a unique isomorphism compatible with
the chart identifications; this isomorphism lies over `X` (`relProjIsoOfIsPullback_hom_comp`). -/
theorem existsUnique_relProjIso :
    ∃! e : A.relProj ≅ P, ∀ U, A.relProjι U ≫ e.hom = j U := by
  refine ⟨A.relProjIsoOfIsPullback p j hj hjc,
    A.relProjι_relProjIsoOfIsPullback_hom p j hj hjc, fun e he ↦ ?_⟩
  ext1
  refine colimit.hom_ext fun U ↦ ?_
  change A.relProjι U ≫ _ = A.relProjι U ≫ _
  rw [he, relProjι_relProjIsoOfIsPullback_hom]

/-- **Independence of the affine cover**: the relative `Proj` is also the colimit of the charts
`Proj (A(V)) ⟶ Proj_X(𝒜)` over any family of affine opens `V` that covers `X` and is closed under
refinement around every point. -/
noncomputable def isColimitRestrict {I : Type u} [Preorder I] {π : I → X.affineOpens}
    (hπ : Monotone π) (hcov : ∀ x : X, ∃ i, x ∈ (π i).1)
    (hdir : ∀ (i i' : I) (x : X), x ∈ (π i).1 → x ∈ (π i').1 →
      ∃ k, k ≤ i ∧ k ≤ i' ∧ x ∈ (π k).1) :
    IsColimit (Cocone.mk A.relProj
      { app i := A.relProjι (π i)
        naturality {i i'} h := by
          simp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id]
          exact A.relProjFunctor_map_relProjι _ } :
      Cocone (hπ.functor ⋙ A.relProjFunctor)) :=
  A.isColimitOfIsPullback hπ A.relProjHom (fun i ↦ A.relProjι (π i))
    (fun i ↦ A.isPullback_relProjι (π i)) (fun _ ↦ A.relProjFunctor_map_relProjι _) hcov hdir

end Unique

end AlgebraicGeometry.Scheme.GradedAlgebraData
