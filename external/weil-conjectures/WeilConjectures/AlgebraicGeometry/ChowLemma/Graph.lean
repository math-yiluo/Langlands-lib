/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The graph of a finite affine open cover

Let `S` be a scheme, let `f : X ⟶ S` be a morphism and let `X = ⋃ i, Uᵢ` be a finite open
cover indexed by a nonempty type. Assume given, for every `i`, a proper closed model
`Mᵢ : ProperClosedModel ((U i).ι ≫ f)`, i.e. a closed subscheme `Mᵢ.Z ⊆ ℙ(Mᵢ.n; S)` containing
`Uᵢ` as a scheme-theoretically dense open subscheme. Step 4 of the proof of Chow's lemma
considers the tuple morphism
`U∞ := ⋂ i, Uᵢ ⟶ ∏_S ℙ(Mᵢ.n; S)` and its scheme-theoretic image `Z`, the *graph* of the cover.
This file constructs `Z` (`AlgebraicGeometry.ChowGraph`) and the data attached to it: `Z` is
proper over `S`, contains `U∞` as a scheme-theoretically dense open subscheme, and admits, for
each `i`, a proper morphism `pᵢ : Z ⟶ Mᵢ.Z` restricting on `U∞` to the open immersion
`U∞ ⟶ Uᵢ ⟶ Mᵢ.Z`. Gluing the `pᵢ` over the opens `pᵢ⁻¹(Uᵢ)` is the subject of a later file.

The `m`-fold fibre product `∏_S ℙ(nᵢ; S)` is taken to be the categorical finite product in the
category `Over S`; `AlgebraicGeometry.isProper_pi_hom` is what makes it proper over `S`, so no
Segre embedding is needed here. The composition of the closed immersion
`Z ⟶ ∏_S ℙ(Mᵢ.n; S)` with the Segre embedding of
`AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi`, giving a closed immersion of `Z`
into a single projective space `ℙ(N; S)` over `S`, is the separate statement
`AlgebraicGeometry.ChowGraph.exists_isClosedImmersion_over` below.

## Main definitions

- `AlgebraicGeometry.ChowGraph` — the graph `Z` of the cover, the scheme-theoretic image of the
  tuple morphism `U∞ ⟶ ∏_S ℙ(Mᵢ.n; S)`.
- `AlgebraicGeometry.ChowGraph.emb` — the closed immersion `Z ⟶ ∏_S ℙ(Mᵢ.n; S)`.
- `AlgebraicGeometry.ChowGraph.toGraph` — the open immersion `U∞ ⟶ Z`.
- `AlgebraicGeometry.ChowGraph.over` — the structure morphism `Z ⟶ S`.
- `AlgebraicGeometry.ChowGraph.proj` — the projection `pᵢ : Z ⟶ Mᵢ.Z`.

## Main statements

- `AlgebraicGeometry.isImmersion_left_pi_lift` — a tuple of morphisms of `S`-schemes one of
  whose components is an immersion is itself an immersion.
- `AlgebraicGeometry.ChowGraph.isProper_over` — `Z` is proper over `S`.
- `AlgebraicGeometry.ChowGraph.exists_isClosedImmersion_over` — `Z` admits a closed immersion
  into a single projective space `ℙ(N; S)` over `S`.
- `AlgebraicGeometry.ChowGraph.isOpenImmersion_toGraph` and
  `AlgebraicGeometry.ChowGraph.isSchemeTheoreticallyDominant_toGraph` — `U∞` is a
  scheme-theoretically dense open subscheme of `Z`.
- `AlgebraicGeometry.ChowGraph.isProper_proj` — the projection `pᵢ : Z ⟶ Mᵢ.Z` is proper.
- `AlgebraicGeometry.ChowGraph.toGraph_proj` — `pᵢ` restricts on `U∞` to `U∞ ⟶ Uᵢ ⟶ Mᵢ.Z`;
  `AlgebraicGeometry.ChowGraph.opensRange_toGraph_le_preimage` is the consequence that `U∞`
  is contained in the open `pᵢ⁻¹(Uᵢ)` of `Z`.

## Implementation notes

* Following `AlgebraicGeometry.ChowModification`, and unlike `AlgebraicGeometry.ChowReduction`
  and `AlgebraicGeometry.ProperClosedModel`, the outcome is not packaged as a structure: the
  graph is a definition and its properties are separate statements, so that a consumer obtains
  them by typeclass inference rather than by destructing an existential.
* The hypotheses are minimal rather than the ones of the blueprint: the members of the cover
  need not be affine and need not cover `X`, only the tuple morphism needs to be quasi-compact
  (which holds for instance if `X` is a Noetherian space), and `U∞` need not be dense in `X`.
* `Nonempty ι` is genuinely needed: for an empty cover the product is `S` itself and the tuple
  morphism is the structure morphism of `U∞`, which is not an immersion.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200), step 4 of the proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace ChowGraph

variable {ι : Type*} [Finite ι] {X S : Scheme.{u}} {f : X ⟶ S} {U : ι → X.Opens}
  (M : ∀ i, ProperClosedModel ((U i).ι ≫ f))

/-- The `m`-fold fibre product `∏_S ℙ(Mᵢ.n; S)` of the ambient projective spaces of the closed
models, as an object of `Over S`. -/
noncomputable def ambient : Over S := ∏ᶜ fun i ↦ Over.mk (ℙ((M i).n; S) ↘ S)

/-- **The product of the ambient projective spaces is proper over `S`**, being a finite product
of proper `S`-schemes. This is what replaces the Segre embedding. -/
instance isProper_ambient_hom : IsProper (ambient M).hom :=
  haveI (i : ι) : IsProper (Over.mk (ℙ((M i).n; S) ↘ S)).hom :=
    inferInstanceAs (IsProper (ℙ((M i).n; S) ↘ S))
  isProper_pi_hom _

/-- The `i`-th projection `∏_S ℙ(Mⱼ.n; S) ⟶ ℙ(Mᵢ.n; S)`. -/
noncomputable def ambientπ (i : ι) : (ambient M).left ⟶ ℙ((M i).n; S) :=
  (Pi.π (fun i ↦ Over.mk (ℙ((M i).n; S) ↘ S)) i).left

@[reassoc (attr := simp)]
lemma ambientπ_over (i : ι) : ambientπ M i ≫ ℙ((M i).n; S) ↘ S = (ambient M).hom :=
  Over.w (Pi.π (fun i ↦ Over.mk (ℙ((M i).n; S) ↘ S)) i)

/-- The `i`-th component `U∞ ⟶ ℙ(Mᵢ.n; S)` of the tuple morphism: the intersection of the
members of the cover sits inside `Uᵢ`, which sits inside the closed model `Mᵢ.Z`, which is a
closed subscheme of `ℙ(Mᵢ.n; S)`. -/
noncomputable def toProjectiveSpace (i : ι) : ↑(⨅ i, U i) ⟶ ℙ((M i).n; S) :=
  X.homOfLE (iInf_le U i) ≫ (M i).ι ≫ (M i).emb

instance isImmersion_toProjectiveSpace (i : ι) : IsImmersion (toProjectiveSpace M i) := by
  unfold toProjectiveSpace; infer_instance

omit [Finite ι] in
@[reassoc (attr := simp)]
lemma toProjectiveSpace_over (i : ι) :
    toProjectiveSpace M i ≫ ℙ((M i).n; S) ↘ S = (⨅ i, U i).ι ≫ f := by
  rw [toProjectiveSpace, Category.assoc, Category.assoc, (M i).w, ← Category.assoc,
    X.homOfLE_ι]

/-- The tuple morphism `U∞ ⟶ ∏_S ℙ(Mᵢ.n; S)` whose `i`-th component is
`AlgebraicGeometry.ChowGraph.toProjectiveSpace`. -/
noncomputable def tuple : ↑(⨅ i, U i) ⟶ (ambient M).left :=
  (Pi.lift (f := fun i ↦ Over.mk (ℙ((M i).n; S) ↘ S))
    (fun i ↦ Over.homMk (U := Over.mk ((⨅ i, U i).ι ≫ f)) (toProjectiveSpace M i)
      (toProjectiveSpace_over M i))).left

@[reassoc (attr := simp)]
lemma tuple_ambientπ (i : ι) : tuple M ≫ ambientπ M i = toProjectiveSpace M i := by
  rw [tuple, ambientπ, ← Over.comp_left, Pi.lift_comp_π]
  rfl

@[reassoc (attr := simp)]
lemma tuple_over : tuple M ≫ (ambient M).hom = (⨅ i, U i).ι ≫ f :=
  Over.w _

/-- **The tuple morphism is an immersion**, since already one of its components is. -/
instance isImmersion_tuple [Nonempty ι] : IsImmersion (tuple M) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine isImmersion_left_pi_lift _ _ _ i ?_
  simp only [Over.homMk_left]
  infer_instance

end ChowGraph

/-- **The graph of a finite open cover**: the scheme-theoretic image `Z` of the tuple
morphism `U∞ = ⋂ i, Uᵢ ⟶ ∏_S ℙ(Mᵢ.n; S)` assembled from the closed models `Mᵢ` of the members
of the cover.

It is a closed subscheme of `∏_S ℙ(Mᵢ.n; S)` (`AlgebraicGeometry.ChowGraph.emb`), hence proper
over `S` (`AlgebraicGeometry.ChowGraph.isProper_over`), it contains `U∞` as a
scheme-theoretically dense open subscheme (`AlgebraicGeometry.ChowGraph.toGraph`) and it maps
properly to each closed model (`AlgebraicGeometry.ChowGraph.proj`). -/
@[stacks 0200 "step 4 of the proof"]
noncomputable def ChowGraph {ι : Type*} [Finite ι] {X S : Scheme.{u}} {f : X ⟶ S}
    {U : ι → X.Opens} (M : ∀ i, ProperClosedModel ((U i).ι ≫ f)) : Scheme.{u} :=
  (ChowGraph.tuple M).image

namespace ChowGraph

variable {ι : Type*} [Finite ι] {X S : Scheme.{u}} {f : X ⟶ S} {U : ι → X.Opens}
  (M : ∀ i, ProperClosedModel ((U i).ι ≫ f))

/-- The closed immersion of the graph into the product `∏_S ℙ(Mᵢ.n; S)`. -/
noncomputable def emb : ChowGraph M ⟶ (ambient M).left := (tuple M).imageι

instance isClosedImmersion_emb : IsClosedImmersion (emb M) := by
  unfold emb; infer_instance

/-- The morphism from the intersection of the members of the cover to the graph. It is an open
immersion onto a scheme-theoretically dense open subscheme; see
`AlgebraicGeometry.ChowGraph.isOpenImmersion_toGraph` and
`AlgebraicGeometry.ChowGraph.isSchemeTheoreticallyDominant_toGraph`. -/
noncomputable def toGraph : ↑(⨅ i, U i) ⟶ ChowGraph M := (tuple M).toImage

@[reassoc (attr := simp)]
lemma toGraph_emb : toGraph M ≫ emb M = tuple M := (tuple M).toImage_imageι

/-- The structure morphism of the graph. -/
noncomputable def over : ChowGraph M ⟶ S := emb M ≫ (ambient M).hom

/-- **The graph is proper over `S`**: it is a closed subscheme of the product
`∏_S ℙ(Mᵢ.n; S)`, which is proper over `S`. -/
instance isProper_over : IsProper (over M) := by
  unfold over; infer_instance

@[reassoc (attr := simp)]
lemma toGraph_over : toGraph M ≫ over M = (⨅ i, U i).ι ≫ f := by
  rw [over, toGraph_emb_assoc, tuple_over]

instance noetherianSpace_iInf [NoetherianSpace X] : NoetherianSpace ↑(⨅ i, U i) :=
  inferInstanceAs (NoetherianSpace ((⨅ i, U i : X.Opens) : Set X))

/-- The tuple morphism is quasi-compact if `X` is a Noetherian space, its source then being a
Noetherian space. -/
instance quasiCompact_tuple [NoetherianSpace X] : QuasiCompact (tuple M) := inferInstance

section QuasiCompact

variable [QuasiCompact (tuple M)]

/-- The factorisation of the tuple morphism through the graph is quasi-compact. -/
instance quasiCompact_toGraph : QuasiCompact (toGraph M) :=
  have : QuasiCompact (toGraph M ≫ emb M) := by rw [toGraph_emb]; infer_instance
  .of_comp _ (emb M)

/-- **`U∞` is scheme-theoretically dense in the graph**, being the source of the factorisation
of the tuple morphism through its scheme-theoretic image. -/
instance isSchemeTheoreticallyDominant_toGraph :
    IsSchemeTheoreticallyDominant (toGraph M) := by
  unfold toGraph; infer_instance

/-- `U∞` is dense in the graph. -/
instance isDominant_toGraph : IsDominant (toGraph M) := by
  unfold toGraph; infer_instance

/-- **`U∞` is an open subscheme of the graph**: the tuple morphism is a quasi-compact
immersion, so it factors as an open immersion onto its scheme-theoretic image followed by a
closed immersion. -/
instance isOpenImmersion_toGraph [Nonempty ι] : IsOpenImmersion (toGraph M) := by
  unfold toGraph; infer_instance

/-- The open subscheme of the graph cut out by `U∞` is scheme-theoretically dense. -/
instance isSchemeTheoreticallyDominant_opensRange_toGraph [Nonempty ι] :
    IsSchemeTheoreticallyDominant (toGraph M).opensRange.ι :=
  (toGraph M).isoOpensRange_inv_comp ▸ inferInstance

/-- **The projection of the graph onto the `i`-th closed model.** It is the unique morphism
`pᵢ : Z ⟶ Mᵢ.Z` compatible with the `i`-th projection `∏_S ℙ(Mⱼ.n; S) ⟶ ℙ(Mᵢ.n; S)`; it exists
by the universal property of the closed immersion `Mᵢ.Z ⟶ ℙ(Mᵢ.n; S)`, because the composition
of the tuple morphism with the `i`-th projection factors through `Mᵢ.Z` by construction and
`U∞` is scheme-theoretically dense in `Z`. -/
@[stacks 01R9 "combined with 0200, step 4 of the proof"]
noncomputable def proj (i : ι) : ChowGraph M ⟶ (M i).Z :=
  IsClosedImmersion.lift (M i).emb (emb M ≫ ambientπ M i) <| by
    have key : (emb M ≫ ambientπ M i).ker = (tuple M ≫ ambientπ M i).ker := by
      conv_rhs => rw [← toGraph_emb M, Category.assoc]
      exact (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (toGraph M)
        (emb M ≫ ambientπ M i)).symm
    rw [key, tuple_ambientπ, toProjectiveSpace, ← Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

@[reassoc (attr := simp)]
lemma proj_emb (i : ι) : proj M i ≫ (M i).emb = emb M ≫ ambientπ M i :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma proj_over (i : ι) : proj M i ≫ (M i).emb ≫ ℙ((M i).n; S) ↘ S = over M := by
  rw [← Category.assoc, proj_emb, Category.assoc, ambientπ_over, over]

/-- **The projection onto the `i`-th closed model is proper**: it becomes proper after
composing with the structure morphism `Mᵢ.Z ⟶ S`, which is separated. -/
@[stacks 01W6 "(2), combined with 0200, step 4 of the proof"]
instance isProper_proj (i : ι) : IsProper (proj M i) := by
  have : IsProper (proj M i ≫ (M i).emb ≫ ℙ((M i).n; S) ↘ S) := by
    rw [proj_over]; infer_instance
  exact IsProper.of_comp (f := proj M i) (g := (M i).emb ≫ ℙ((M i).n; S) ↘ S)

/-- **On `U∞` the projection onto the `i`-th closed model is the open immersion
`U∞ ⟶ Uᵢ ⟶ Mᵢ.Z`.** -/
@[reassoc (attr := simp)]
lemma toGraph_proj (i : ι) :
    toGraph M ≫ proj M i = X.homOfLE (iInf_le U i) ≫ (M i).ι := by
  rw [← cancel_mono (M i).emb, Category.assoc, proj_emb, toGraph_emb_assoc, tuple_ambientπ,
    toProjectiveSpace, Category.assoc]

/-- **`U∞` is contained in `pᵢ⁻¹(Uᵢ)`**, as an open subscheme of the graph. -/
lemma opensRange_toGraph_le_preimage [Nonempty ι] (i : ι) :
    (toGraph M).opensRange ≤ proj M i ⁻¹ᵁ (M i).ι.opensRange := by
  rintro x ⟨y, rfl⟩
  exact ⟨X.homOfLE (iInf_le U i) y, by
    rw [← Scheme.Hom.comp_apply, ← toGraph_proj, Scheme.Hom.comp_apply]⟩

end QuasiCompact

/-- **The graph is a closed subscheme of a single projective space over `S`.** Composing the
closed immersion `Z ⟶ ∏_S ℙ(Mᵢ.n; S)` of `AlgebraicGeometry.ChowGraph.emb` with the `m`-fold
Segre embedding `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi` yields a closed
immersion of `Z` into a projective space `ℙ(N; S)` with `N` finite, compatible with the
structure morphisms over `S`.

The index type `ι` of the cover lives in an arbitrary universe, while the Segre embedding is
stated for an index type in the universe of the schemes; the two are matched up by reindexing
the product along an equivalence `ι ≃ ULift.{u} (Fin k)`. -/
@[stacks 0200 "step 7 of the proof"]
theorem exists_isClosedImmersion_over :
    ∃ (N : Type u) (_ : Finite N) (g : ChowGraph M ⟶ ℙ(N; S)),
      IsClosedImmersion g ∧ g ≫ ℙ(N; S) ↘ S = over M := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let e' : ι ≃ ULift.{u} (Fin k) := e.trans Equiv.ulift.symm
  obtain ⟨N, hN, g, hg⟩ :=
    ProjectiveSpace.exists_isClosedImmersion_pi (fun j ↦ (M (e'.symm j)).n) S
  let ee : ambient M ≅ ∏ᶜ fun j ↦ Over.mk (ℙ((M (e'.symm j)).n; S) ↘ S) :=
    Pi.whiskerEquiv (f := fun i ↦ Over.mk (ℙ((M i).n; S) ↘ S))
      (g := fun j ↦ Over.mk (ℙ((M (e'.symm j)).n; S) ↘ S)) e'
      fun i ↦ eqToIso (by rw [Equiv.symm_apply_apply])
  have : IsIso ee.hom.left := inferInstanceAs (IsIso ((Over.forget S).map ee.hom))
  refine ⟨N, hN, emb M ≫ (ee.hom ≫ g).left, ?_, ?_⟩
  · rw [Over.comp_left]
    infer_instance
  · have h := Over.w (ee.hom ≫ g)
    simp only [Over.mk_hom] at h
    rw [Category.assoc, h, over]

end ChowGraph

end AlgebraicGeometry
