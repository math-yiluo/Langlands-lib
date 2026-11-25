/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal

/-!
# Base change of the relative `Proj`

Let `g: X' ⟶ X` be a morphism of schemes, `A` a quasi-coherent graded algebra on `X` and `A'`
one on `X'`. A `PullbackData g A A'` identifies `A'` with the coefficientwise pullback `g^* A`:
for affine opens `U' ⊆ X'` and `U ⊆ X` with `g(U') ⊆ U` it provides graded maps
`A(U) → A'(U')`, compatible with restrictions on both sides, which exhibit each `A'(U')ₙ` as the
base change `Γ(X', U') ⊗_{Γ(X, U)} A(U)ₙ`.

Given such data we construct the comparison morphism `Proj_{X'}(A') ⟶ Proj_X(A)` and show that
it exhibits `Proj_{X'}(A')` as the fibre product `X' ×_X Proj_X(A)`. Flatness of `g`
is not needed.

## Main results

- `AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData` — identification of `A'` with `g^* A`.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.relProjComparison` — the comparison
  morphism.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.isPullback` and
  `AlgebraicGeometry.Scheme.GradedAlgebraData.PullbackData.relProjIsoPullback` — the base change
  isomorphism `Proj_{X'}(g^* 𝒜) ≅ X' ×_X Proj_X(𝒜)` over `X'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (A : X.GradedAlgebraData) (A' : X'.GradedAlgebraData)

/-- An identification of the quasi-coherent graded algebra `A'` on `X'` with the coefficientwise
pullback `g^* A` of `A` along `g : X' ⟶ X`: for affine opens `U' ⊆ X'`, `U ⊆ X` with
`U' ⊆ g⁻¹ U`, a graded homomorphism `A(U) → A'(U')` which is a coefficientwise base change along
`g.appLE U U' : Γ(X, U) → Γ(X', U')`, i.e. `A'(U')ₙ = Γ(X', U') ⊗_{Γ(X, U)} A(U)ₙ`, compatibly
with the restriction maps of `A` and `A'`. -/
structure PullbackData where
  /-- The comparison maps. -/
  map {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    A.grading U →+*ᵍ A'.grading U'
  isGradedBaseChangeAlong {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    (map h).IsGradedBaseChangeAlong (g.appLE U.1 U'.1 h).hom
  res_map {U' V' : X'.affineOpens} {U : X.affineOpens} (h' : U' ≤ V') (h : V'.1 ≤ g ⁻¹ᵁ U.1)
    (x : A.obj U) : A'.res h' (map h x) = map ((show U'.1 ≤ V'.1 from h').trans h) x
  map_res {U' : X'.affineOpens} {U V : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) (hUV : U ≤ V)
    (x : A.obj V) : map h (A.res hUV x) = map (h.trans (g.preimage_mono hUV)) x

namespace PullbackData

variable {g A A'} (D : PullbackData g A A')

lemma irrelevant_le_map {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    HomogeneousIdeal.irrelevant (A'.grading U') ≤
      (HomogeneousIdeal.irrelevant (A.grading U)).map (D.map h) :=
  (D.isGradedBaseChangeAlong h).irrelevant_le

/-- The local comparison morphism `Proj (A'(U')) ⟶ Proj (A(U)) ⟶ Proj_X(A)`. -/
noncomputable def localComparison {U' : X'.affineOpens} {U : X.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) : Proj (A'.grading U') ⟶ A.relProj :=
  Proj.map (D.map h) (D.irrelevant_le_map h) ≫ A.relProjι U

/-- The index set of pairs `(U', U)` of affine opens with `U' ⊆ g⁻¹ U`. -/
def Pairs (g : X' ⟶ X) : Type u :=
  {q : X'.affineOpens × X.affineOpens // q.1.1 ≤ g ⁻¹ᵁ q.2.1}

instance : Preorder (Pairs g) := inferInstanceAs (Preorder {q : X'.affineOpens × X.affineOpens //
  q.1.1 ≤ g ⁻¹ᵁ q.2.1})

lemma Pairs.le_iff {q q' : Pairs g} : q ≤ q' ↔ q.1.1 ≤ q'.1.1 ∧ q.1.2 ≤ q'.1.2 :=
  Iff.rfl

lemma Pairs.monotone_fst : Monotone (fun q : Pairs g ↦ q.1.1) := fun _ _ h ↦ h.1

lemma Pairs.exists_mem (x : X') : ∃ q : Pairs g, x ∈ q.1.1.1 := by
  obtain ⟨U, hU⟩ := exists_affineOpens_mem (g x)
  obtain ⟨U', hU'⟩ := exists_affineOpens_mem x
  obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show x ∈ U'.1 ⊓ g ⁻¹ᵁ U.1 from ⟨hU', hU⟩)
  exact ⟨⟨(⟨W, hW⟩, U), hle.trans inf_le_right⟩, hxW⟩

lemma Pairs.exists_le (q q' : Pairs g) (x : X') (hq : x ∈ q.1.1.1) (hq' : x ∈ q'.1.1.1) :
    ∃ k : Pairs g, k ≤ q ∧ k ≤ q' ∧ x ∈ k.1.1.1 := by
  obtain ⟨W, hWq, hWq', hgW⟩ := exists_affineOpens_le q.1.2 q'.1.2 (g x) (q.2 hq) (q'.2 hq')
  obtain ⟨W', hW', hxW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show x ∈ q.1.1.1 ⊓ q'.1.1.1 ⊓ g ⁻¹ᵁ W.1 from ⟨⟨hq, hq'⟩, hgW⟩)
  refine ⟨⟨(⟨W', hW'⟩, W), hle.trans inf_le_right⟩, ⟨?_, hWq⟩, ⟨?_, hWq'⟩, hxW'⟩
  · exact hle.trans (inf_le_left.trans inf_le_left)
  · exact hle.trans (inf_le_left.trans inf_le_right)

lemma localComparison_naturality {U' V' : X'.affineOpens} {U V : X.affineOpens}
    (h' : U' ≤ V') (hUV : U ≤ V) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (hV : V'.1 ≤ g ⁻¹ᵁ V.1) :
    A'.relProjFunctor.map (homOfLE h') ≫ D.localComparison hV = D.localComparison hU := by
  have e : (A'.res h').comp (D.map hV) = (D.map hU).comp (A.res hUV) := by
    refine GradedRingHom.ext fun x ↦ ?_
    simp only [GradedRingHom.comp_apply, D.res_map, D.map_res]
  rw [localComparison, localComparison, relProjFunctor_map_homOfLE, ← Category.assoc,
    ← Proj.map_comp, Proj.map_congr e _
      (HomogeneousIdeal.irrelevant_le_map_comp (A.irrelevant_le_map_res hUV)
        (D.irrelevant_le_map hU)),
    Proj.map_comp _ _ (A.irrelevant_le_map_res hUV) (D.irrelevant_le_map hU), Category.assoc]
  exact congrArg _ (A.relProjFunctor_map_relProjι (homOfLE hUV))

/-- The comparison morphism `Proj_{X'}(A') ⟶ Proj_X(A)`, glued from the morphisms
`Proj (A'(U')) ⟶ Proj (A(U))` over all pairs of affine opens with `U' ⊆ g⁻¹ U`. -/
noncomputable def relProjComparison : A'.relProj ⟶ A.relProj :=
  (A'.isColimitRestrict (Pairs.monotone_fst (g := g)) Pairs.exists_mem Pairs.exists_le).desc
    { pt := A.relProj
      ι :=
        { app q := D.localComparison q.2
          naturality {q q'} f :=
            (D.localComparison_naturality (leOfHom f).1 (leOfHom f).2 q.2 q'.2).trans
              (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma relProjι_relProjComparison {U' : X'.affineOpens} {U : X.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    A'.relProjι U' ≫ D.relProjComparison = D.localComparison h :=
  (A'.isColimitRestrict (Pairs.monotone_fst (g := g)) Pairs.exists_mem Pairs.exists_le).fac _
    (⟨(U', U), h⟩ : Pairs g)

/-- The restriction of `g` to affine opens, compared with `Spec` of `appLE`. -/
lemma specMap_appLE_isoSpec_inv {U' : X'.affineOpens} {U : X.affineOpens}
    (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    Spec.map (g.appLE U.1 U'.1 h) ≫ U.2.isoSpec.inv = U'.2.isoSpec.inv ≫ g.resLE U.1 U'.1 h := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.Hom.resLE_comp_ι, IsAffineOpen.isoSpec_inv_ι_assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec]

/-- The local base change square: `Proj (A'(U')) = U' ×_X Proj_X(A)`. -/
lemma isPullback_local {U' : X'.affineOpens} {U : X.affineOpens} (h : U'.1 ≤ g ⁻¹ᵁ U.1) :
    IsPullback (D.localComparison h) (A'.toOpen U') A.relProjHom (U'.1.ι ≫ g) := by
  have T1 := Proj.isPullback_map_of_isGradedBaseChangeAlong _ _ (D.isGradedBaseChangeAlong h)
  have T2 : IsPullback (Spec.map (CommRingCat.ofHom (g.appLE U.1 U'.1 h).hom))
      U'.2.isoSpec.inv U.2.isoSpec.inv (g.resLE U.1 U'.1 h) :=
    IsPullback.of_vert_isIso ⟨by rw [CommRingCat.ofHom_hom]; exact specMap_appLE_isoSpec_inv h⟩
  have L := T1.paste_vert T2
  have R := (A.isPullback_relProjι U).flip
  have := L.paste_horiz R
  rwa [Scheme.Hom.resLE_comp_ι] at this

/-- **Base change of the relative `Proj`**: if `A'` is identified with the coefficientwise
pullback `g^* A`, then the comparison morphism exhibits `Proj_{X'}(A')` as the fibre product
`X' ×_X Proj_X(A)`. No flatness of `g` is needed: this is the base change of the relative `Proj`
along an arbitrary morphism. -/
theorem isPullback :
    IsPullback D.relProjComparison A'.relProjHom A.relProjHom g := by
  refine IsPullback.flip <| Scheme.isPullback_of_openCover _ _ _ _
    (X'.openCoverOfIsOpenCover (fun q : Pairs g ↦ q.1.1.1) ?_) fun q ↦ ?_
  · refine TopologicalSpace.Opens.ext <| Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨q, hq⟩ := Pairs.exists_mem (g := g) x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hq⟩
  have S1 := (A'.isPullback_relProjι q.1.1).flip
  refine (D.isPullback_local q.2).flip.of_iso S1.isoPullback (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact S1.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = S1.isoPullback.hom ≫ pullback.fst _ _ ≫ _
    rw [S1.isoPullback_hom_fst_assoc, relProjι_relProjComparison]
  · simp
  · simp

/-- The base change isomorphism `Proj_{X'}(g^* 𝒜) ≅ X' ×_X Proj_X(𝒜)` for an arbitrary morphism
`g: X' ⟶ X`. -/
noncomputable def relProjIsoPullback : A'.relProj ≅ pullback A.relProjHom g :=
  D.isPullback.isoPullback

@[reassoc (attr := simp)]
lemma relProjIsoPullback_hom_snd : D.relProjIsoPullback.hom ≫ pullback.snd _ _ = A'.relProjHom :=
  D.isPullback.isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma relProjIsoPullback_hom_fst :
    D.relProjIsoPullback.hom ≫ pullback.fst _ _ = D.relProjComparison :=
  D.isPullback.isoPullback_hom_fst

end PullbackData

end AlgebraicGeometry.Scheme.GradedAlgebraData
