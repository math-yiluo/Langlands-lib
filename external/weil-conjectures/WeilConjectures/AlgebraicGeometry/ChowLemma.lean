/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.ChowLemma.Glue
public import WeilConjectures.AlgebraicGeometry.ChowLemma.Reduction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Chow's lemma

Chow's lemma says that a separated morphism of finite type `f : X ⟶ S` over a Noetherian
scheme `S` is, up to a proper surjective modification of `X`, quasi-projective. For such an `f`
we introduce the modification itself: a scheme `AlgebraicGeometry.ChowModification f`, a finite
index type `AlgebraicGeometry.ChowModification.index f` and two morphisms out of the
modification, namely a proper surjective
`AlgebraicGeometry.ChowModification.modificationMap f : ChowModification f ⟶ X` which is an
isomorphism over a dense open subset of `X`, and an immersion
`AlgebraicGeometry.ChowModification.toProjectiveSpace f : ChowModification f ⟶ ℙ(index f; S)`
over `S`.

## Main definitions

- `AlgebraicGeometry.ChowModification` — the Chow modification `X'` of `f : X ⟶ S`.
- `AlgebraicGeometry.ChowModification.index` — the index type of the homogeneous coordinates
  of the projective space the Chow modification embeds into.
- `AlgebraicGeometry.ChowModification.modificationMap` — the modification `X' ⟶ X`.
- `AlgebraicGeometry.ChowModification.toProjectiveSpace` — the immersion `X' ⟶ ℙ(index f; S)`.

## Main statements

- `AlgebraicGeometry.ChowModification.isProper_modificationMap` and
  `AlgebraicGeometry.ChowModification.surjective_modificationMap` — the modification is proper
  and surjective.
- `AlgebraicGeometry.ChowModification.isImmersion_toProjectiveSpace` and
  `AlgebraicGeometry.ChowModification.toProjectiveSpace_over` — the morphism to projective
  space is an immersion over `S`.
- `AlgebraicGeometry.ChowModification.exists_dense_isIso_restrict` — the modification is an
  isomorphism over a dense open subset of `X`.
- `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace` — if `f` is proper,
  the immersion into projective space is a closed immersion, so `X` is dominated by a
  projective `S`-scheme.
- `AlgebraicGeometry.ChowModification.nonempty_data` — the assembly of the above out of the
  reduction, the graph and the gluing; all of the declarations listed here are read off it.
- `AlgebraicGeometry.exists_chowModification_of_finite_irreducibleComponents` — Chow's lemma
  over a quasi-compact quasi-separated base, for `X` with finitely many irreducible components
  (Stacks 0203); `nonempty_data` is its Noetherian special case.

## Implementation notes

* The construction depends on a great many choices — a reduction of `f`, a proper closed model
  of each member of its affine cover, and a closed immersion of the resulting graph into a
  single projective space — and `ChowModification f`, `index f`, `modificationMap f` and
  `toProjectiveSpace f` are four separate declarations that must all be read off the *same*
  choice. The choice is therefore made once, in
  `AlgebraicGeometry.ChowModification.data f : ChowModification.Data f`, and every declaration
  of this file is a field of it.
* Rather than packaging the modification as a structure and asserting that it is nonempty,
  the modification is a definition and its properties are separate statements. A consumer
  therefore obtains properness of the modification and the immersion property by typeclass
  inference, without destructing an existential.
* `index f` is the index type of the *homogeneous* coordinates of `ℙ(index f; S)`, so the
  space Stacks writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`. Matching
  `AlgebraicGeometry.ProjectiveSpace` and Mathlib's affine space `𝔸(n; S)`, it is a finite
  type in `Type u` rather than a natural number.
* Mathlib has no bundled `IsFiniteType` for morphisms of schemes, so Stacks' "of finite type"
  is spelled out as the two hypotheses `LocallyOfFiniteType f` and `QuasiCompact f`.
* `IsImmersion` is Stacks' immersion (locally closed), not `IsClosedImmersion`.

## TODO

* Deduce the classical form of Chow's lemma for an irreducible `X`, where the modification can
  be taken to be irreducible as well.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200)

## Blueprint

The declarations of this file implement `thm:chow-lemma` of the proper-base-change blueprint.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

/-- **Chow's lemma over a quasi-compact quasi-separated base** (the non-Noetherian variant,
blueprint `rem-chow-lemma-non-noetherian`): let `S` be quasi-compact and quasi-separated and let
`f : X ⟶ S` be separated and of finite type, with `X` having finitely many irreducible
components. Then there are a proper surjective morphism `π : X' ⟶ X` which is an isomorphism
over a dense open subset of `X`, and an immersion `e : X' ⟶ ℙ(N; S)` over `S` with `N` finite.

The proof is that of `AlgebraicGeometry.ChowModification.nonempty_data`: Noetherianity of `S`
is only used there through the finiteness of the set of irreducible components of `X` and the
quasi-compactness of the various immersions out of quasi-compact schemes, which here follows
from quasi-separatedness instead. -/
@[stacks 0203]
theorem exists_chowModification_of_finite_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hX : (irreducibleComponents X).Finite) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (N : Type u) (_ : Finite N) (e : X' ⟶ ℙ(N; S)),
      IsProper π ∧ Surjective π ∧ IsImmersion e ∧ e ≫ ℙ(N; S) ↘ S = π ≫ f ∧
      ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  -- Steps 1 and 2: a reduction of `f` with a nonempty finite affine open cover.
  obtain ⟨R, hn⟩ := (nonempty_chowReduction_of_finite_irreducibleComponents f hX).some
    |>.exists_n_ne_zero
  have : Nonempty (Fin R.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have : CompactSpace R.Y := QuasiCompact.compactSpace_of_compactSpace (R.c ≫ f)
  have : QuasiSeparatedSpace R.Y := quasiSeparatedSpace_of_quasiSeparated (R.c ≫ f)
  -- Step 3: a proper closed model of each member of the cover.
  have M : ∀ i, ProperClosedModel ((R.U i).ι ≫ R.c ≫ f) := fun i ↦
    have : IsAffine (R.U i) := R.isAffineOpen_U i
    (nonempty_properClosedModel_of_quasiSeparatedSpace _).some
  -- The tuple morphism is quasi-compact: its source `⋂ i, R.U i` is quasi-compact, being a
  -- finite intersection of affine opens of a quasi-separated scheme, and its target is
  -- quasi-compact and quasi-separated, being proper over `S`.
  have hc : IsCompact ((⨅ i, R.U i : R.Y.Opens) : Set R.Y) := by
    have h := QuasiSeparatedSpace.isCompact_sInter (α := R.Y)
      (s := Set.range fun i ↦ (R.U i : Set R.Y)) (Set.finite_range _)
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (R.U i).isOpen)
      (by rintro _ ⟨i, rfl⟩; exact (R.isAffineOpen_U i).isCompact)
    rwa [Set.sInter_range, ← TopologicalSpace.Opens.coe_iInf] at h
  have : CompactSpace (⨅ i, R.U i : R.Y.Opens) := isCompact_iff_compactSpace.mp hc
  have : QuasiCompact (⨅ i, R.U i).ι := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have : QuasiCompact (ChowGraph.tuple M) := by
    have : CompactSpace (ChowGraph.ambient M).left :=
      QuasiCompact.compactSpace_of_compactSpace (ChowGraph.ambient M).hom
    have : QuasiSeparatedSpace (ChowGraph.ambient M).left :=
      quasiSeparatedSpace_of_quasiSeparated (ChowGraph.ambient M).hom
    exact (quasiCompact_iff_compactSpace _).mpr inferInstance
  -- Step 7: the graph is a closed subscheme of a single projective space over `S`.
  obtain ⟨N, hNfin, g, hg, hgS⟩ := ChowGraph.exists_isClosedImmersion_over M
  -- Step 5: the modification is proper, being proper over each member of the cover.
  have hproper : IsProper (ChowGraph.modificationMap M) :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
      (f := ChowGraph.modificationMap M) R.U R.iSup_U fun i ↦
        ChowGraph.isProper_morphismRestrict_modificationMap M i
  -- Step 5: the modification is dominant, since `U∞` maps onto the dense `⋂ i, R.U i`, hence
  -- surjective, being universally closed.
  have hdom : IsDominant (ChowGraph.modificationMap M) := by
    have h : IsDominant ((⨅ i, R.U i).ι) := inferInstance
    rw [← ChowGraph.toGraph_modificationMap M] at h
    have h' : IsDominant ((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M) ≫
        ChowGraph.modificationMap M) :=
      IsDominant.of_comp (ChowGraph.toGraph M).isoOpensRange.hom _
    exact IsDominant.of_comp
      ((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M)) _
  have hsurj : Surjective (ChowGraph.modificationMap M) := inferInstance
  -- Step 6: on `U∞` the modification is the inclusion of `⋂ i, R.U i` in `R.Y`.
  have hju : (ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M) ≫
      ChowGraph.modificationMap M =
        (ChowGraph.toGraph M).isoOpensRange.inv ≫ (⨅ i, R.U i).ι :=
    (Iso.eq_inv_comp _).mpr (ChowGraph.toGraph_modificationMap M)
  have hle : ((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M)).opensRange ≤
      ChowGraph.modificationMap M ⁻¹ᵁ ⨅ i, R.U i := by
    rintro x ⟨y, rfl⟩
    have h : (ChowGraph.modificationMap M).base
        (((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M)).base y) ∈
          ⨅ i, R.U i := by
      rw [← Scheme.Hom.comp_apply, hju, Scheme.Hom.comp_apply]
      exact ((ChowGraph.toGraph M).isoOpensRange.inv.base y).2
    exact h
  -- so `U∞ ⟶ π⁻¹(⋂ i, R.U i) ⟶ ⋂ i, R.U i` is an isomorphism, in particular proper.
  have hcomp : ((ChowGraph.toGraph M).isoOpensRange ≪≫
      ((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M)).isoOpensRange).hom ≫
        ((⨆ i, ChowGraph.projPreimage M i).toScheme.homOfLE hle ≫
          (ChowGraph.modificationMap M ∣_ ⨅ i, R.U i)) = 𝟙 _ := by
    rw [← cancel_mono (⨅ i, R.U i).ι]
    simp only [Iso.trans_hom, Category.assoc, Category.id_comp]
    rw [morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc,
      ChowGraph.toGraph_modificationMap]
  have hb : IsIso ((⨆ i, ChowGraph.projPreimage M i).toScheme.homOfLE hle ≫
      (ChowGraph.modificationMap M ∣_ ⨅ i, R.U i)) := by
    rw [(Iso.hom_comp_eq_id _).mp hcomp]
    infer_instance
  -- `U∞` is dense in `X'` and proper over `⋂ i, R.U i`, hence all of `π⁻¹(⋂ i, R.U i)`.
  have hVW : ((ChowGraph M).homOfLE (ChowGraph.opensRange_toGraph_le_iSup M)).opensRange =
      ChowGraph.modificationMap M ⁻¹ᵁ ⨅ i, R.U i := by
    have h1 : Dense ((ChowGraph.toGraph M).opensRange : Set (ChowGraph M)) := by
      rw [Scheme.Hom.coe_opensRange]
      exact (ChowGraph.toGraph M).denseRange
    have h2 : Dense ((⨆ i, ChowGraph.projPreimage M i).ι.base ⁻¹'
        ((ChowGraph.toGraph M).opensRange : Set (ChowGraph M))) := by
      rw [dense_iff_closure_eq, ← (⨆ i, ChowGraph.projPreimage M i).ι.isOpenEmbedding.isOpenMap
        |>.preimage_closure_eq_closure_preimage (⨆ i, ChowGraph.projPreimage M i).ι.continuous,
        h1.closure_eq, Set.preimage_univ]
    have h3 : Dense ((((ChowGraph M).homOfLE
        (ChowGraph.opensRange_toGraph_le_iSup M)).opensRange :
          Set (⨆ i, ChowGraph.projPreimage M i).toScheme)) := by
      rw [Scheme.opensRange_homOfLE]
      exact h2
    exact Scheme.Opens.eq_of_isProper_of_dense hle
      (ChowGraph.modificationMap M ∣_ ⨅ i, R.U i) fun x _ ↦ h3 x
  have hisoLE : IsIso ((⨆ i, ChowGraph.projPreimage M i).toScheme.homOfLE hle) :=
    inferInstanceAs (IsIso ((⨆ i, ChowGraph.projPreimage M i).toScheme.isoOfEq hVW).hom)
  have hq : IsIso (ChowGraph.modificationMap M ∣_ ⨅ i, R.U i) :=
    IsIso.of_isIso_comp_left ((⨆ i, ChowGraph.projPreimage M i).toScheme.homOfLE hle) _
  refine ⟨(⨆ i, ChowGraph.projPreimage M i).toScheme, ChowGraph.modificationMap M ≫ R.c, N,
    hNfin, (⨆ i, ChowGraph.projPreimage M i).ι ≫ g, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hgS, ChowGraph.modificationMap_over]
  · refine ⟨R.V, R.dense_V, ?_⟩
    have hcV : IsIso (ChowGraph.modificationMap M ∣_ R.c ⁻¹ᵁ R.V) := by
      rw [R.preimage_V]
      exact hq
    rw [morphismRestrict_comp]
    infer_instance

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

namespace ChowModification

/-- All the data the Chow modification of `f : X ⟶ S` is made of, in one structure: the
modification `X'` together with the proper surjective `π : X' ⟶ X`, which is an isomorphism
over a dense open subset of `X`, and the immersion of `X'` into a projective space `ℙ(N; S)`
over `S`.

Bundling the data like this is what makes the choices underlying `ChowModification f`,
`ChowModification.index f`, `ChowModification.modificationMap f` and
`ChowModification.toProjectiveSpace f` the *same* choices: all four are fields of
`ChowModification.data f`. -/
structure Data {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] where
  /-- the modification `X'` -/
  X' : Scheme.{u}
  /-- the proper surjective morphism `X' ⟶ X` -/
  π : X' ⟶ X
  [isProper_π : IsProper π]
  [surjective_π : Surjective π]
  /-- the index type of the homogeneous coordinates of the ambient projective space -/
  N : Type u
  [finite_N : Finite N]
  /-- the immersion of `X'` into the projective space `ℙ(N; S)` -/
  e : X' ⟶ ℙ(N; S)
  [isImmersion_e : IsImmersion e]
  /-- the immersion is a morphism over `S` -/
  w : e ≫ ℙ(N; S) ↘ S = π ≫ f
  /-- the modification is an isomorphism over a dense open subset of `X` -/
  exists_dense_isIso : ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)

/-- **Chow's lemma**: a separated morphism of finite type over a Noetherian scheme admits a
Chow modification.

Steps 1 and 2 of Stacks' proof produce a reduction `R` of `f` (`AlgebraicGeometry.ChowReduction`)
with a nonempty finite affine open cover `R.U`, step 3 a proper closed model `M i` of each
member of the cover, step 4 the graph `ChowGraph M` of the family, and step 5 the modification
`ChowGraph.modificationMap M` obtained by gluing the projections of the graph. It remains to
check that the latter is proper (it is proper over each `R.U i`, which cover), surjective (it
is universally closed and dominant, the dense open `U∞` mapping isomorphically onto
`⋂ i, R.U i`) and an isomorphism over `⋂ i, R.U i` (the open `U∞` of `X'` is dense in the
preimage of `⋂ i, R.U i` and proper over it, hence all of it); step 7 is the closed immersion
of the graph into a single projective space over `S`. These steps are carried out in
`AlgebraicGeometry.exists_chowModification_of_finite_irreducibleComponents`, which applies since
`X` is Noetherian.
(blueprint: `thm:chow-lemma`, `lem-weil-pbc-chow-noetherian`) -/
@[stacks 0200]
theorem nonempty_data : Nonempty (Data f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨X', π, N, hN, e, hπ, hπs, he, w, hU⟩ :=
    exists_chowModification_of_finite_irreducibleComponents f
      (finite_irreducibleComponents_of_isNoetherian (X := X))
  exact ⟨{ X' := X', π := π, N := N, e := e, w := w, exists_dense_isIso := hU }⟩

/-- The choice of all the data underlying the Chow modification of `f`. -/
def data : Data f := (nonempty_data f).some

end ChowModification

/-- The **Chow modification** `X'` of a separated morphism of finite type `f : X ⟶ S` over a
Noetherian scheme `S`: a scheme with a proper surjective morphism to `X` which is an
isomorphism over a dense open subset of `X`, and an immersion into a projective space over
`S`, i.e. a scheme making

```
                     toProjectiveSpace
  ChowModification f -----------------> ℙ(index f; S)
          |                                   |
          | modificationMap                   | ↘
          ↓                                   ↓
          X ------------- f ----------------> S
```

commute. -/
@[stacks 0200]
def ChowModification {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Scheme.{u} :=
  (ChowModification.data f).X'

namespace ChowModification

/-- The index type of the homogeneous coordinates of the projective space that the Chow
modification of `f` is immersed into. -/
def index {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Type u :=
  (data f).N

/-- The projective space the Chow modification is immersed into is finite dimensional. -/
instance finite_index : Finite (index f) := (data f).finite_N

/-- The modification `X' ⟶ X` of a Chow modification, which is proper and surjective and an
isomorphism over a dense open subset of `X`. -/
def modificationMap : ChowModification f ⟶ X := (data f).π

/-- The immersion `X' ⟶ ℙ(index f; S)` of a Chow modification into a projective space
over `S`. -/
def toProjectiveSpace : ChowModification f ⟶ ℙ(index f; S) := (data f).e

/-- The modification of a Chow modification is proper. -/
instance isProper_modificationMap : IsProper (modificationMap f) := (data f).isProper_π

/-- The modification of a Chow modification is surjective. -/
instance surjective_modificationMap : Surjective (modificationMap f) := (data f).surjective_π

/-- The morphism from a Chow modification to projective space is an immersion, that is, a
locally closed immersion. -/
instance isImmersion_toProjectiveSpace : IsImmersion (toProjectiveSpace f) :=
  (data f).isImmersion_e

/-- The immersion of a Chow modification into projective space is a morphism over `S`:

```
                     toProjectiveSpace
  ChowModification f -----------------> ℙ(index f; S)
          |                                   |
          | modificationMap                   | ↘
          ↓                                   ↓
          X ------------- f ----------------> S
```

commutes. -/
@[reassoc]
theorem toProjectiveSpace_over :
    toProjectiveSpace f ≫ ℙ(index f; S) ↘ S = modificationMap f ≫ f :=
  (data f).w

/-- **Chow's lemma**: the modification of a Chow modification is an isomorphism over a dense
open subset of `X`.
(blueprint: `thm:chow-lemma`) -/
@[stacks 0200]
theorem exists_dense_isIso_restrict :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (modificationMap f ∣_ U) :=
  (data f).exists_dense_isIso

/-- **Chow's lemma for proper morphisms**: if `f : X ⟶ S` is proper, the immersion of its Chow
modification into projective space is a *closed* immersion. Together with
`AlgebraicGeometry.ChowModification.isProper_modificationMap` and
`AlgebraicGeometry.ChowModification.surjective_modificationMap` this says that a proper scheme
over a Noetherian base is dominated by a projective one.

Indeed, `toProjectiveSpace f` composed with the structure morphism of `ℙ(index f; S)` is the
proper morphism `modificationMap f ≫ f`, and the structure morphism is separated, so
`toProjectiveSpace f` is itself proper, hence universally closed.
(blueprint: `cor:chow-lemma-proper`) -/
@[stacks 0202]
instance isClosedImmersion_toProjectiveSpace {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [IsProper f] : IsClosedImmersion (toProjectiveSpace f) := by
  have : IsProper (toProjectiveSpace f ≫ ℙ(index f; S) ↘ S) := by
    rw [toProjectiveSpace_over]
    infer_instance
  have : IsProper (toProjectiveSpace f) := .of_comp _ (ℙ(index f; S) ↘ S)
  exact .of_universallyClosed _

end ChowModification

end

end AlgebraicGeometry
