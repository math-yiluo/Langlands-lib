/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.Graph
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Gluing the projections of the graph into the modification

Let `S` be a scheme, let `f : X ⟶ S` be a separated morphism and let `U : ι → X.Opens` be a
finite nonempty family of opens with proper closed models `Mᵢ` of `Uᵢ ⟶ S`. Let `Z` be the
graph `AlgebraicGeometry.ChowGraph M` of the family, with its proper projections
`pᵢ : Z ⟶ Mᵢ.Z` and its scheme-theoretically dense open `U∞ ⊆ Z`, the isomorphic image of
`⋂ i, Uᵢ`. Step 5 of the proof of Chow's lemma glues the `pᵢ` over the opens
`Vᵢ := pᵢ⁻¹(Uᵢ) ⊆ Z` into a morphism `π : X' ⟶ X`, where `X' := ⋃ i, Vᵢ`: the restrictions
`Vᵢ ⟶ Uᵢ ⊆ X` all agree on `U∞`, where they are the inclusion of `U∞` in `X`, and this
suffices because `X` is separated over `S` and `U∞` is scheme-theoretically dense.

This file constructs `π` (`AlgebraicGeometry.ChowGraph.modificationMap`) and identifies its
fibres over the members of the family: `π⁻¹(Uᵢ) = Vᵢ`, so that `π⁻¹(Uᵢ) ⟶ Uᵢ` is proper. Both
statements together say that `π` becomes proper over each `Uᵢ`, which is what makes `π` itself
proper once the `Uᵢ` cover `X`.

## Main definitions

- `AlgebraicGeometry.ChowGraph.projPreimage` — the open `Vᵢ = pᵢ⁻¹(Uᵢ)` of the graph.
- `AlgebraicGeometry.ChowGraph.projRestrict` — the proper morphism `pᵢ|_{Vᵢ} : Vᵢ ⟶ Uᵢ`.
- `AlgebraicGeometry.ChowGraph.modificationMap` — the modification `π : X' ⟶ X`, where the
  source `X'` is the open `⨆ i, Vᵢ` of the graph.

## Main statements

- `AlgebraicGeometry.ChowGraph.homOfLE_modificationMap` — `π` restricts to `pᵢ|_{Vᵢ}` on `Vᵢ`;
  `AlgebraicGeometry.ChowGraph.toGraph_modificationMap` — `π` restricts to the inclusion on
  `U∞`; `AlgebraicGeometry.ChowGraph.modificationMap_over` — `π` is a morphism over `S`.
- `AlgebraicGeometry.ChowGraph.preimage_modificationMap` — `π⁻¹(Uᵢ) = Vᵢ`.
- `AlgebraicGeometry.ChowGraph.isProper_morphismRestrict_modificationMap` — `π⁻¹(Uᵢ) ⟶ Uᵢ` is
  proper.

## Implementation notes

* `Vᵢ` is the preimage under `pᵢ` of the *image* `Mᵢ.ι.opensRange` of `Uᵢ` in `Mᵢ.Z`, since
  `pᵢ` lands in `Mᵢ.Z` and not in `X`; accordingly `pᵢ|_{Vᵢ}` is the restriction of `pᵢ` to
  that open of the target, followed by the inverse of the isomorphism of `Uᵢ` with its image.
  This makes properness of `pᵢ|_{Vᵢ}` a matter of typeclass inference, properness being local
  at the target.
* `Vᵢ` and `U∞` are opens of the graph `Z`, and so is `X'`, which is spelled out as
  `⨆ i, projPreimage M i` rather than given a name of its own: the gluing API is stated for
  a family of opens and their supremum, and the statements here are meant to be usable
  without unfolding. The source of `π` is the scheme `(⨆ i, projPreimage M i).toScheme`.
* Consequently the equality `π⁻¹(Uᵢ) = Vᵢ` is an equality of opens of `X'`: on the right hand
  side it is `Vᵢ` pulled back along the inclusion `X' ⟶ Z`.
* The hypothesis `IsSeparated f` is not needed for the graph, but it is needed here: it is
  what makes the restrictions of the `pᵢ` agree on `U∞`.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200), step 5 of the proof.

## Blueprint

`AlgebraicGeometry.ChowGraph.modificationMap` and the lemmas around it implement
`lem:chow-glue`, `AlgebraicGeometry.ChowGraph.preimage_modificationMap` and
`AlgebraicGeometry.ChowGraph.isProper_morphismRestrict_modificationMap` implement
`lem:chow-preimage`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace ChowGraph

variable {ι : Type*} [Finite ι] {X S : Scheme.{u}} {f : X ⟶ S} {U : ι → X.Opens}
  (M : ∀ i, ProperClosedModel ((U i).ι ≫ f)) [QuasiCompact (tuple M)]

/-- The open `Vᵢ = pᵢ⁻¹(Uᵢ)` of the graph: the preimage under the `i`-th projection of the
image of `Uᵢ` in the closed model `Mᵢ.Z`. -/
noncomputable def projPreimage (i : ι) : (ChowGraph M).Opens := proj M i ⁻¹ᵁ (M i).ι.opensRange

/-- The restriction `pᵢ|_{Vᵢ} : Vᵢ ⟶ Uᵢ` of the `i`-th projection of the graph, obtained by
restricting `pᵢ` to the image of `Uᵢ` in `Mᵢ.Z` and identifying `Uᵢ` with that image. -/
noncomputable def projRestrict (i : ι) : (projPreimage M i).toScheme ⟶ (U i).toScheme :=
  (proj M i ∣_ (M i).ι.opensRange) ≫ (M i).ι.isoOpensRange.inv

/-- **The restriction `pᵢ|_{Vᵢ} : Vᵢ ⟶ Uᵢ` is proper**, being the base change of the proper
morphism `pᵢ` along the open immersion of `Uᵢ` in `Mᵢ.Z`. -/
instance isProper_projRestrict (i : ι) : IsProper (projRestrict M i) := by
  unfold projRestrict; infer_instance

@[reassoc (attr := simp)]
lemma projRestrict_ι (i : ι) :
    projRestrict M i ≫ (M i).ι = (projPreimage M i).ι ≫ proj M i := by
  rw [projRestrict, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- The morphism `Vᵢ ⟶ Uᵢ ⟶ X` is a morphism over `S`. -/
lemma projRestrict_ι_over (i : ι) :
    (projRestrict M i ≫ (U i).ι) ≫ f = (projPreimage M i).ι ≫ over M := by
  rw [Category.assoc, ← (M i).w, projRestrict_ι_assoc, proj_over]

/-- The isomorphism of `Vᵢ` with the corresponding open subscheme of `X'`. -/
noncomputable def projPreimageIsoOfLE (i : ι) :
    (projPreimage M i).toScheme ≅
      ((⨆ i, projPreimage M i).ι ⁻¹ᵁ projPreimage M i).toScheme :=
  ((ChowGraph M).homOfLE (le_iSup (projPreimage M) i)).isoOpensRange ≪≫
    (⨆ i, projPreimage M i).toScheme.isoOfEq (Scheme.opensRange_homOfLE _)

@[reassoc (attr := simp)]
lemma projPreimageIsoOfLE_hom_ι (i : ι) :
    (projPreimageIsoOfLE M i).hom ≫
        ((⨆ i, projPreimage M i).ι ⁻¹ᵁ projPreimage M i).ι =
      (ChowGraph M).homOfLE (le_iSup (projPreimage M) i) := by
  rw [projPreimageIsoOfLE, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

section Nonempty

variable [Nonempty ι]

/-- The open subscheme of the graph cut out by `U∞` is quasi-compact. -/
instance quasiCompact_opensRange_toGraph : QuasiCompact (toGraph M).opensRange.ι :=
  (toGraph M).isoOpensRange_inv_comp ▸ inferInstance

/-- `U∞` is contained in `Vᵢ`. -/
lemma opensRange_toGraph_le_projPreimage (i : ι) :
    (toGraph M).opensRange ≤ projPreimage M i :=
  opensRange_toGraph_le_preimage M i

/-- **On `U∞` the restriction `pᵢ|_{Vᵢ}` is the inclusion `U∞ ⟶ Uᵢ`.** -/
lemma homOfLE_projRestrict (i : ι) :
    (ChowGraph M).homOfLE (opensRange_toGraph_le_projPreimage M i) ≫ projRestrict M i =
      (toGraph M).isoOpensRange.inv ≫ X.homOfLE (iInf_le U i) := by
  rw [← cancel_mono (M i).ι, Category.assoc, projRestrict_ι, Scheme.homOfLE_ι_assoc,
    Category.assoc, ← toGraph_proj, Scheme.Hom.isoOpensRange_inv_comp_assoc]

/-- **On `U∞` the morphism `Vᵢ ⟶ Uᵢ ⟶ X` is the inclusion of `U∞` in `X`**, independently
of `i`. This is the compatibility that makes the gluing possible. -/
lemma homOfLE_projRestrict_ι (i : ι) :
    (ChowGraph M).homOfLE (opensRange_toGraph_le_projPreimage M i) ≫
        projRestrict M i ≫ (U i).ι =
      (toGraph M).isoOpensRange.inv ≫ (⨅ i, U i).ι := by
  rw [← Category.assoc, homOfLE_projRestrict, Category.assoc, X.homOfLE_ι]

/-- `U∞` is contained in `X'`. -/
lemma opensRange_toGraph_le_iSup : (toGraph M).opensRange ≤ ⨆ i, projPreimage M i :=
  (opensRange_toGraph_le_projPreimage M (Classical.arbitrary ι)).trans (le_iSup _ _)

variable [IsSeparated f]

/-- **The modification `π : X' ⟶ X`** obtained by gluing the restrictions
`pᵢ|_{Vᵢ} : Vᵢ ⟶ Uᵢ ⊆ X` of the projections of the graph over the open
`X' = ⋃ i, Vᵢ` of the graph.

The morphisms being glued agree on the scheme-theoretically dense open `U∞`, where they are
all the inclusion of `U∞` in `X`, and `X` is separated over `S`; this is enough by rigidity
of morphisms into a separated scheme.
(blueprint: `lem:chow-glue`) -/
@[stacks 0200 "step 5 of the proof"]
noncomputable def modificationMap : (⨆ i, projPreimage M i).toScheme ⟶ X :=
  Scheme.Opens.glueMorphismsOfDominant (projPreimage M) (toGraph M).opensRange
    (opensRange_toGraph_le_projPreimage M) f (over M) (fun i ↦ projRestrict M i ≫ (U i).ι)
    (projRestrict_ι_over M) fun i j ↦ by
      rw [homOfLE_projRestrict_ι, homOfLE_projRestrict_ι]

/-- **On `Vᵢ` the modification is the restriction `pᵢ|_{Vᵢ} : Vᵢ ⟶ Uᵢ ⊆ X`.** -/
@[reassoc (attr := simp)]
lemma homOfLE_modificationMap (i : ι) :
    (ChowGraph M).homOfLE (le_iSup (projPreimage M) i) ≫ modificationMap M =
      projRestrict M i ≫ (U i).ι :=
  Scheme.Opens.homOfLE_glueMorphismsOfDominant (projPreimage M) (toGraph M).opensRange
    (opensRange_toGraph_le_projPreimage M) f (over M) _ _ _ i

/-- **The modification is a morphism over `S`.** -/
@[reassoc (attr := simp)]
lemma modificationMap_over :
    modificationMap M ≫ f = (⨆ i, projPreimage M i).ι ≫ over M :=
  Scheme.Opens.glueMorphismsOfDominant_comp (projPreimage M) (toGraph M).opensRange
    (opensRange_toGraph_le_projPreimage M) f (over M) _ _ _

/-- **On `U∞` the modification is the inclusion of `U∞ = ⋂ i, Uᵢ` in `X`.** -/
lemma toGraph_modificationMap :
    (toGraph M).isoOpensRange.hom ≫ (ChowGraph M).homOfLE (opensRange_toGraph_le_iSup M) ≫
      modificationMap M = (⨅ i, U i).ι := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have key : (ChowGraph M).homOfLE (opensRange_toGraph_le_iSup M) =
      (ChowGraph M).homOfLE (opensRange_toGraph_le_projPreimage M i) ≫
        (ChowGraph M).homOfLE (le_iSup (projPreimage M) i) :=
    ((ChowGraph M).homOfLE_homOfLE _ _).symm
  rw [key, Category.assoc, homOfLE_modificationMap, homOfLE_projRestrict_ι,
    Iso.hom_inv_id_assoc]

/-- **The modification is separated**, being separated over `S` since the graph is proper
over `S`. -/
instance isSeparated_modificationMap : IsSeparated (modificationMap M) :=
  have : IsSeparated (modificationMap M ≫ f) := by rw [modificationMap_over]; infer_instance
  .of_comp (f := modificationMap M) (g := f)

/-- `Vᵢ` is contained in `π⁻¹(Uᵢ)`, since on `Vᵢ` the modification is `pᵢ|_{Vᵢ}`, which takes
values in `Uᵢ`. -/
lemma le_preimage_modificationMap (i : ι) :
    (⨆ i, projPreimage M i).ι ⁻¹ᵁ projPreimage M i ≤ modificationMap M ⁻¹ᵁ U i := by
  rw [← Scheme.opensRange_homOfLE (le_iSup (projPreimage M) i)]
  rintro x ⟨y, rfl⟩
  have h : (modificationMap M).base
      (((ChowGraph M).homOfLE (le_iSup (projPreimage M) i)).base y) ∈ U i := by
    rw [← Scheme.Hom.comp_apply, homOfLE_modificationMap, Scheme.Hom.comp_apply]
    exact ((projRestrict M i).base y).2
  exact h

/-- Under the identification of `Vᵢ` with an open subscheme of `X'`, the inclusion of `Vᵢ`
in `π⁻¹(Uᵢ)` followed by `π|_{Uᵢ}` is the proper morphism `pᵢ|_{Vᵢ}`. -/
lemma projPreimageIsoOfLE_hom_homOfLE_morphismRestrict (i : ι) :
    (projPreimageIsoOfLE M i).hom ≫
      (⨆ i, projPreimage M i).toScheme.homOfLE (le_preimage_modificationMap M i) ≫
        (modificationMap M ∣_ U i) = projRestrict M i := by
  rw [← cancel_mono (U i).ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc, projPreimageIsoOfLE_hom_ι_assoc, homOfLE_modificationMap]

/-- The inclusion of `Vᵢ` in `π⁻¹(Uᵢ)` is proper over `Uᵢ`, being `pᵢ|_{Vᵢ}` up to the
identification of `Vᵢ` with an open subscheme of `X'`. -/
instance isProper_homOfLE_morphismRestrict (i : ι) :
    IsProper ((⨆ i, projPreimage M i).toScheme.homOfLE (le_preimage_modificationMap M i) ≫
      (modificationMap M ∣_ U i)) := by
  refine (MorphismProperty.cancel_left_of_respectsIso @IsProper
    (projPreimageIsoOfLE M i).hom _).mp ?_
  rw [projPreimageIsoOfLE_hom_homOfLE_morphismRestrict]
  infer_instance

/-- **The fibre of the modification over `Uᵢ` is `Vᵢ`.**

The inclusion `Vᵢ ⊆ π⁻¹(Uᵢ)` is proper over `Uᵢ`, hence universally closed since `π⁻¹(Uᵢ)`
is separated over `Uᵢ`; and `Vᵢ` contains `U∞`, which is dense in `X'`. So `Vᵢ` is a closed
dense open subscheme of `π⁻¹(Uᵢ)`, hence all of it.
(blueprint: `lem:chow-preimage`) -/
@[stacks 0200 "step 5 of the proof"]
theorem preimage_modificationMap (i : ι) :
    modificationMap M ⁻¹ᵁ U i = (⨆ i, projPreimage M i).ι ⁻¹ᵁ projPreimage M i := by
  have h1 : Dense ((toGraph M).opensRange : Set (ChowGraph M)) := by
    rw [Scheme.Hom.coe_opensRange]
    exact (toGraph M).denseRange
  have h2 : Dense ((⨆ i, projPreimage M i).ι.base ⁻¹'
      (projPreimage M i : Set (ChowGraph M))) := by
    rw [dense_iff_closure_eq, ← (⨆ i, projPreimage M i).ι.isOpenEmbedding.isOpenMap
      |>.preimage_closure_eq_closure_preimage (⨆ i, projPreimage M i).ι.continuous,
      (h1.mono (opensRange_toGraph_le_projPreimage M i)).closure_eq, Set.preimage_univ]
  exact (Scheme.Opens.eq_of_isProper_of_dense (le_preimage_modificationMap M i)
    (modificationMap M ∣_ U i) fun x _ ↦ h2 x).symm

/-- **The modification is proper over each member of the family.** -/
instance isProper_morphismRestrict_modificationMap (i : ι) :
    IsProper (modificationMap M ∣_ U i) := by
  have hiso : IsIso ((⨆ i, projPreimage M i).toScheme.homOfLE
      (le_preimage_modificationMap M i)) :=
    inferInstanceAs (IsIso ((⨆ i, projPreimage M i).toScheme.isoOfEq
      (preimage_modificationMap M i).symm).hom)
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper
    ((⨆ i, projPreimage M i).toScheme.homOfLE (le_preimage_modificationMap M i)) _).mp
    inferInstance

end Nonempty

end ChowGraph

end AlgebraicGeometry
