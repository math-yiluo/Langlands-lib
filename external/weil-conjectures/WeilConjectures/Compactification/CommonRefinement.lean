/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# A common refinement of two compactifications

Any two compactifications `c` and `d` of a quasi-compact morphism `f : X ⟶ Y` are refined
by a third one: the closure of the graph of `X` in `c.Z ×_Y d.Z`.

Concretely, the two open immersions `c.i` and `d.i` induce `γ : X ⟶ c.Z ×_Y d.Z`, and the
common refinement is the scheme-theoretic image of `γ`, with structure morphism the
projection to `c.Z` followed by `c.g` and with `X` embedded by `γ.toImage`. That this last
morphism is an open immersion is the graph-extension package of
`WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks`: the projection
`SIm(γ) ⟶ c.Z` is proper and restricts to an isomorphism over the open `X ⊆ c.Z`.

## Main definitions

- `AlgebraicGeometry.Compactification.inf`: the common refinement of two compactifications
  `c` and `d`, the closure of the graph of `X` in `c.Z ×_Y d.Z` (blueprint:
  `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`);
- `AlgebraicGeometry.Compactification.infFst` and `AlgebraicGeometry.Compactification.infSnd`:
  the two projections, exhibiting `inf c d` as a refinement of `c` and of `d`.

## Main results

- `AlgebraicGeometry.Compactification.isPullback_infFst` and
  `AlgebraicGeometry.Compactification.isPullback_infSnd`: over the copy of `X` in `c.Z`
  (resp. `d.Z`) the common refinement is `X` itself, i.e. the squares formed by the two
  refinements and the open immersions of `X` are cartesian.
- `AlgebraicGeometry.Compactification.exists_common_refinement`: two compactifications of a
  quasi-compact morphism admit a common refinement (blueprint:
  `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`). This is what makes the `κ`-system
  `κ_{c,d} = ρ_{e → d} ρ_{e → c}⁻¹` of the proper base change chapter well-posed.
- `AlgebraicGeometry.Compactification.exists_common_refinement_isSchemeTheoreticallyDominant`:
  the refinement `inf c d` is moreover scheme-theoretically dense, since its ambient
  scheme is by construction the scheme-theoretic image of `X`.

Finite presentation of the structure morphism of the common refinement, the remaining part
of `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`, is not treated here.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The graph `X ⟶ c.Z ×_Y d.Z` of the two open immersions of a pair of compactifications
`c`, `d` of `f`. -/
noncomputable def graph (c d : Compactification f) : X ⟶ pullback c.g d.g :=
  pullback.lift c.i d.i (by rw [← c.comm, ← d.comm])

@[reassoc (attr := simp)]
lemma graph_fst (c d : Compactification f) : graph c d ≫ pullback.fst c.g d.g = c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_snd (c d : Compactification f) : graph c d ≫ pullback.snd c.g d.g = d.i :=
  pullback.lift_snd _ _ _

variable [QuasiCompact f]

instance (c d : Compactification f) : QuasiCompact (graph c d) :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  quasiCompact_of_partialSection c.g d.g c.i _ (graph_fst c d)

/-- The projection of the scheme-theoretic image of `graph c d` to `c.Z` restricts to an
isomorphism over the open `X ⊆ c.Z`. -/
lemma isIso_restrict_imageι_graph_fst (c d : Compactification f) :
    IsIso (((graph c d).imageι ≫ pullback.fst c.g d.g) ∣_ c.i.opensRange) :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  isIso_restrict_imageι_comp_fst c.g d.g c.i _ (graph_fst c d)

/-- **The common refinement of two compactifications**: for compactifications `c` and `d` of
a quasi-compact morphism `f : X ⟶ Y`, the closure of the graph of `X` in `c.Z ×_Y d.Z`, i.e.
the scheme-theoretic image of `graph c d`, is a compactification of `f`. It refines both `c`
and `d` (`Compactification.infFst`, `Compactification.infSnd`).
(Blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`.) -/
noncomputable def inf (c d : Compactification f) : Compactification f where
  Z := (graph c d).image
  g := ((graph c d).imageι ≫ pullback.fst c.g d.g) ≫ c.g
  i := (graph c d).toImage
  comm := by rw [← Category.assoc, Scheme.Hom.toImage_imageι_assoc, graph_fst, ← c.comm]
  isProper :=
    have : IsProper ((graph c d).imageι ≫ pullback.fst c.g d.g) :=
      isProper_imageι_comp_fst c.g d.g _
    inferInstance
  isOpenImmersion :=
    isOpenImmersion_of_comp_of_isIso_restrict _ _ c.i
      (by rw [Scheme.Hom.toImage_imageι_assoc, graph_fst])
      (isIso_restrict_imageι_graph_fst c d)

lemma inf_Z (c d : Compactification f) : (inf c d).Z = (graph c d).image := rfl

lemma inf_i (c d : Compactification f) : (inf c d).i = (graph c d).toImage := rfl

/-- The first projection exhibits the common refinement `inf c d` as a refinement of `c`. -/
noncomputable def infFst (c d : Compactification f) : (inf c d).Refinement c where
  hom := (graph c d).imageι ≫ pullback.fst c.g d.g
  i_hom := by
    change (graph c d).toImage ≫ _ = _
    rw [Scheme.Hom.toImage_imageι_assoc, graph_fst]
  hom_g := rfl

/-- The second projection exhibits the common refinement `inf c d` as a refinement of `d`. -/
noncomputable def infSnd (c d : Compactification f) : (inf c d).Refinement d where
  hom := (graph c d).imageι ≫ pullback.snd c.g d.g
  i_hom := by
    change (graph c d).toImage ≫ _ = _
    rw [Scheme.Hom.toImage_imageι_assoc, graph_snd]
  hom_g := by
    change _ = ((graph c d).imageι ≫ pullback.fst c.g d.g) ≫ c.g
    rw [Category.assoc, ← pullback.condition, Category.assoc]

lemma infFst_hom (c d : Compactification f) :
    (infFst c d).hom = (graph c d).imageι ≫ pullback.fst c.g d.g := rfl

lemma infSnd_hom (c d : Compactification f) :
    (infSnd c d).hom = (graph c d).imageι ≫ pullback.snd c.g d.g := rfl

/-- **`X` is the whole fibre of the common refinement over `X ⊆ c.Z`**: the square formed by
the open immersions of `X` and the refinement `infFst c d` is cartesian. -/
theorem isPullback_infFst (c d : Compactification f) :
    IsPullback (inf c d).i (𝟙 X) (infFst c d).hom c.i :=
  have : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  isPullback_toImage_partialSection c.g d.g c.i _ (graph_fst c d)

/-- **`X` is the whole fibre of the common refinement over `X ⊆ d.Z`**: the square formed by
the open immersions of `X` and the refinement `infSnd c d` is cartesian. Over `X ⊆ d.Z` the
closure of the graph is the graph itself, `c.Z ⟶ Y` being separated. -/
theorem isPullback_infSnd (c d : Compactification f) :
    IsPullback (inf c d).i (𝟙 X) (infSnd c d).hom d.i := by
  refine (IsOpenImmersion.isPullback (𝟙 X) (inf c d).i d.i (infSnd c d).hom
    (by rw [(infSnd c d).i_hom, Category.id_comp]) ?_).flip
  ext1
  exact preimage_range_snd_eq_range_toImage c.g d.g (graph c d) d.i (graph_snd c d)

/-- `X` is scheme-theoretically dense in the common refinement `inf c d`, whose ambient
scheme is by construction the scheme-theoretic image of `X`. -/
theorem isSchemeTheoreticallyDominant_inf_i (c d : Compactification f) :
    IsSchemeTheoreticallyDominant (inf c d).i := by
  change IsSchemeTheoreticallyDominant (graph c d).toImage
  infer_instance

/-- **Two compactifications admit a common refinement, densely**: the closure of the graph
of `X` in `c.Z ×_Y d.Z` is a compactification of `f` refining both `c` and `d`, in which `X`
is moreover scheme-theoretically dense. -/
theorem exists_common_refinement_isSchemeTheoreticallyDominant (c d : Compactification f) :
    ∃ e : Compactification f, IsSchemeTheoreticallyDominant e.i ∧
      Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) :=
  ⟨inf c d, isSchemeTheoreticallyDominant_inf_i c d, ⟨infFst c d⟩, ⟨infSnd c d⟩⟩

/-- **Two compactifications admit a common refinement**: for compactifications `c` and `d`
of a quasi-compact morphism `f`, there is a compactification `e` of `f` refining both.
(Blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`.) -/
theorem exists_common_refinement (c d : Compactification f) :
    ∃ e : Compactification f, Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) :=
  ⟨inf c d, ⟨infFst c d⟩, ⟨infSnd c d⟩⟩

end AlgebraicGeometry.Compactification
