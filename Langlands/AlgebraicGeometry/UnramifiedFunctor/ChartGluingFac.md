# Factorization through a monomorphic chart

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingFac`, first of the five
modules proving `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartGluingStatement`
(Murre's Lemma 3 = SGA 3, XI, Proposition 3.5). All declarations live in the namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing`. These are internal auxiliary
results for that proof. The module formalizes the formal (non-noetherian) parts of the proof of
SGA 3, XI, Proposition 3.1, (ii) ⇒ (i) (printed pp. 94–96 of the Gille–Polo recomposition,
registered as `sga3-exposes-xi-xii-xiv-gille-polo-2008`).

Throughout, `S : Scheme.{u}`, `F : (Over S)ᵒᵖ ⥤ Type v`, `U : Over S` and `ξ : F.obj (op U)`
(a morphism `U → F` by Yoneda). The conditions `ZariskiSheaf` (F1a) and `FaithfullyFlatSheaf`
(F1b) are those of the published module `MurreCriterionStatement`; `IsMonoElement` is the one of
`MurreLocalToGlobalSteps`.

## The factorization predicate

* `Fac ξ η a`, for `η : F.obj (op T)` and `a : T' ⟶ T` in `Over S`: there is an `S`-morphism
  `h : T' ⟶ U` with `F.map h.op ξ = F.map a.op η`, i.e. the restriction `η|_{T'}` factors
  through `ξ : U → F`.
* `fac_comp`: `Fac ξ η a → Fac ξ η (b ≫ a)` (compose the witness with `b`).
* `fac_map_iff`: `Fac ξ (F.map c.op η₀) b ↔ Fac ξ η₀ (b ≫ c)` (functoriality of `F`).
* `eq_of_fac`: two witnesses of the same factorization are equal when `ξ` is a monomorphism.

## Descent along faithfully flat morphisms

`fac_of_flat`: if `ξ` is a monomorphism, `F` satisfies (F1b), `φ : T₁ ⟶ T₀` is flat, surjective
and quasi-compact, and `Fac ξ η (φ ≫ a)`, then `Fac ξ η a`. Proof: let `h : T₁ ⟶ U` be the
witness. For two maps `g₁, g₂ : Z ⟶ T₁` with `g₁ ≫ φ = g₂ ≫ φ`, the two composites
`g₁ ≫ h`, `g₂ ≫ h` have the same image under `ξ` (both equal the restriction of `η`), so they
agree because `ξ` is a monomorphism. Since a flat surjective quasi-compact morphism is an
effective epimorphism of schemes (Mathlib's fpqc results, `EffectiveEpi`), `h` descends to
`h₀ : T₀ ⟶ U` with `φ ≫ h₀ = h`; it is an `S`-morphism because `φ` is an epimorphism. Finally
`F.map h₀.op ξ = F.map a.op η` because both sides have the same pullback along `φ` and `F` is
separated for the singleton covering `{φ}` by (F1b).

This is the descent step used twice in SGA 3, XI 3.1: in (ii) ⇒ (i) for `S′ → S₀` with `S₀` the
spectrum of a residue field, and in (iii) ⇒ (ii) for the completion `Spec Â → Spec A`.

## Points with values in fields

* `resPt T t : Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T`, the point `Spec κ(t) → T`.
* `exists_eq_comp_resPt`: every `g : Spec K ⟶ T` over `S` (with `K` a field) factors through
  `resPt T t` at its image point `t`, via `Spec` of a field extension `κ(t) → K` (Mathlib's
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`).
* Instances: `Spec.map φ` is flat and quasi-compact for a map of fields `φ`, and it is
  surjective (`surjective_specMap_of_field`), since `Spec L` has one point.
* `fac_fieldPt_iff`: for a monomorphism `ξ` and (F1b), `Fac ξ η g ↔ Fac ξ η (resPt T t)` at the
  image point `t` of `g : Spec K ⟶ T`. The direction `⇐` is `fac_comp`; the direction `⇒` is
  `fac_of_flat` along `Spec K → Spec κ(t)`. This is the last paragraph of the proof of SGA 3,
  XI 3.1 (ii) ⇒ (i).
* `W ξ η : Set T.left`, the set of points `t` with `Fac ξ η (resPt T t)`; `mem_W_iff` unfolds it.
  This is the set `U` of SGA 3, XI 3.1 (ii) ⇒ (i), relative to `T`.
* `range_subset_W_of_fac`: if `Fac ξ η a` then `a` maps `T'` into `W ξ η` (restrict to residue
  fields of `T'` and apply `fac_fieldPt_iff`).
* `mem_W_map_iff`: `t' ∈ W ξ (F.map c.op η) ↔ c.left t' ∈ W ξ η` (by `fac_map_iff` and
  `fac_fieldPt_iff`).

## Zariski gluing

* `ιOver T V : Over.mk (V.ι ≫ T.hom) ⟶ T`, an open subscheme `V ⊆ T.left` as an object of
  `Over S`.
* `fac_of_openCover`: if `ξ` is a monomorphism, `F` satisfies (F1a), and `η` factors through
  `ξ` after restriction to every member of an open cover `𝒰` of `T'`, then `Fac ξ η a`. The
  witnesses `hᵢ` agree on the overlaps (again because `ξ` is a monomorphism), so they glue to
  `g : T'.left ⟶ U.left` (`Scheme.Cover.glueMorphisms`), an `S`-morphism by `hom_ext` on the
  cover; the required equality holds on every member of the cover, hence on `T'` by (F1a)
  separatedness.
* `fac_of_forall_opens`: the same with an open neighbourhood of every point.
* `LocFac ξ η t`: `η` factors through `ξ` on some open neighbourhood `V` of `t`.
  `LocFac.pullback` transports it along any `a : T' ⟶ T` (using preimages of opens).
* `opensRangeToSource`, `ιOver_opensRange`: for an `S`-morphism `c : X ⟶ T` with `c.left` an
  open immersion, the inclusion of the open image `c.left.opensRange` factors through `c`.
  `LocFac.of_isOpenImmersion`: `Fac ξ η c` gives `LocFac ξ η t` for every `t` in the image.

## The open locus (SGA 3, XI 3.1, formal part)

Section `Locus` assumes, besides a monomorphism `ξ`, (F1a) and (F1b), the hypothesis `hloc`:
every point of every `W ξ η` has an open neighbourhood on which `η` factors through `ξ`.
(This hypothesis is proved over a locally noetherian base in `ChartGluingLocus`.)

* `fac_iff_range_subset`: `Fac ξ η a ↔ Set.range a.left ⊆ W ξ η`. `⇒` is
  `range_subset_W_of_fac`; for `⇐`, `hloc` and `LocFac.pullback` give local factorizations of
  `η|_{T'}` near every point of `T'`, which glue by `fac_of_forall_opens`.
* `isOpen_W`: `W ξ η` is open, since every point has a neighbourhood `V` with `Fac ξ η (ιOver T V)`
  and then `V ⊆ W ξ η`.

These are the statements "`U` is open" and "an `S`-morphism `S′ → F` factors through `U`
exactly when it does so pointwise at residue fields" of SGA 3, XI 3.1 (ii) ⇒ (i), for the
fibre product `T ×_F U` instead of `F` itself.
