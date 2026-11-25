# Proof of potential geometric reducedness of the reduced generic fibre over a DVR

Lean module: `Langlands.AlgebraicGeometry.DvrPotentialGenericReductionProof`.

## Result

`theorem Langlands.AlgebraicGeometry.dvrPotentialGenericReduction :
DvrPotentialGenericReductionStatement.{u}` proves the Library statement
`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement` in every universe `u`,
with no extra hypotheses. Let `R` be a DVR and `X` a flat, quasi-compact, locally finite-type
scheme over `Spec R`. Then there are a DVR `R'` (same universe) and a flat surjective
`b : Spec R' ⟶ Spec R` such that the canonical reduction of
`(X ×_{Spec R} Spec R') ×_{Spec R'} Spec (FractionRing R')` is geometrically reduced over
`FractionRing R'`. The witness is `b = Spec.map (algebraMap R R')`. Flatness of `X` is not
used.

The module also contains one auxiliary theorem,
`Langlands.AlgebraicGeometry.PotentialGeometricReduction.exists_good_field`.

## Mathematical route

The route is the first sentence of the proof of Lemma A.5 in Brian Conrad's appendix to
Prasad–Yu, *On quasi-reductive group schemes* (author preprint, p. 29): after a finite
extension `K'/K` of the fraction field, `(X'_red) ⊗_{K'} K̄` is reduced. That step is proved
in the helper module `Langlands.AlgebraicGeometry.PotentialGeometricReduction` (affine case),
and globalized here. The DVR step does not use henselization. It uses a DVR `R'` inside the
finite extension that dominates `R`, as the target's Markdown allows. This module records only
the Lean proof.

## Ingredients

From `Langlands.AlgebraicGeometry.PotentialGeometricReduction` (namespace of the same name):

- `Good f`: some surjective closed immersion `i : Z ⟶ Y` with `Z` reduced has
  `GeometricallyReduced (i ≫ f)`.
- `good_iff f : Good f ↔ GeometricallyReduced (redι Y ≫ f)`, where `redι Y`
  (`Langlands.GroupScheme.ReducedSubgroup.redι`) is the inclusion of the closed subscheme of
  `vanishingIdeal ⊤`. For `X : Over S`, `(DvrPotentialGenericReduction.reducedOver X).hom` is
  by definition `redι X.left ≫ X.hom`.
- `Good.iso_comp`, `Good.pullback_snd` (base change along `Spec` of a field),
  `good_pullback_snd_comp_iff` (base change along `g' ≫ g` versus iterated base change),
  `Good.of_comp` (descent along a flat, surjective, geometrically reduced morphism onto a
  locally noetherian scheme).
- `exists_good_affine K A`: for a finite-type algebra `A` over a field `K` there is a
  finite extension `L` with the base change of `Spec A ⟶ Spec K` to `Spec L` good.

From the helper modules `QuasiCompactAffineEtaleCover` and `DvrDominatingFiniteExtension`:

- `QuasiCompactAffineEtaleCover.exists_spec_cover Y`: for a quasi-compact scheme `Y` there are
  a ring `R` and `p : Spec R ⟶ Y` that is surjective, flat, geometrically reduced, locally of
  finite type, étale and smooth.
- `DvrDominatingFiniteExtension.exists_dvr_of_finite_extension R L`: for a DVR `R` and a finite
  extension `L` of `FractionRing R` there are a DVR `R'` with an `R`-algebra structure and
  `σ : L →+* FractionRing R'`. They satisfy: `Spec.map (algebraMap R R')` is flat and
  surjective, and `σ ∘ (R → FractionRing R → L) = (R' → FractionRing R') ∘ (R → R')`.

## Proof of `exists_good_field`

Statement: let `K` be a field and `f : Y ⟶ Spec K` quasi-compact and locally of finite type.
Then there is a finite extension `L / K` (a field `L : Type u` with `Algebra K L` and
`FiniteDimensional K L`) such that `Good (pullback.snd f (Spec.map (algebraMap K L)))`.

1. `Y` is quasi-compact, so `exists_spec_cover` gives `p : Spec R ⟶ Y`, surjective, flat,
   geometrically reduced and locally of finite type.
2. `p ≫ f : Spec R ⟶ Spec K` is `Spec.map φ` for a ring map `φ : K → R`
   (`Spec.map_surjective`). Make `R` a `K`-algebra by `φ`. It is of finite type, since
   `Spec.map φ` is locally of finite type (`HasRingHomProperty.Spec_iff`).
3. `exists_good_affine K R` gives `L`. Rewriting with `φ = algebraMap K R` and
   `Spec.map φ = p ≫ f` gives `Good (pullback.snd (p ≫ f) σ)` for
   `σ = Spec.map (algebraMap K L)`.
4. `pullbackRightPullbackFstIso f σ p` identifies `pullback (p ≫ f) σ` with
   `pullback p (pullback.fst f σ)` and its second projection with
   `pullback.snd p (pullback.fst f σ) ≫ pullback.snd f σ`. By `Good.iso_comp` that
   composite is good.
5. `pullback.snd p (pullback.fst f σ)` is a base change of `p`, so it is flat, surjective and
   geometrically reduced. Its target `pullback f σ` is locally of finite type over the field
   `L`, hence locally noetherian. `Good.of_comp` gives `Good (pullback.snd f σ)`.

## Proof of `dvrPotentialGenericReduction`

Let `R`, `X` be given and put `K = FractionRing R`, `a = Spec.map (algebraMap R K)`.

1. `pullback.snd X.hom a : X_K ⟶ Spec K` is quasi-compact and locally of finite type (base
   change), so `exists_good_field` gives a finite extension `L / K` with
   `Good (pullback.snd (pullback.snd X.hom a) (Spec.map (algebraMap K L)))`.
2. `exists_dvr_of_finite_extension R L` gives `R'`, `σ`, flatness and surjectivity of
   `b = Spec.map (algebraMap R R')`, and the compatibility `hσ`. These, with `R'`, its
   instances and `b`, are the witnesses of the statement.
3. It remains to show `Good` for the base change of `X ×_R R'` along
   `Spec (FractionRing R') ⟶ Spec R'`. By `good_pullback_snd_comp_iff`, this is `Good`
   for the base change of `X` along the composite `Spec (FractionRing R') ⟶ Spec R`. By
   `hσ`, that composite equals
   `Spec.map σ ≫ Spec.map (algebraMap K L) ≫ a`. Applying `good_pullback_snd_comp_iff`
   twice more, it is enough to know `Good` for the base change of
   `pullback.snd (pullback.snd X.hom a) (Spec.map (algebraMap K L))` along
   `Spec.map σ : Spec (FractionRing R') ⟶ Spec L`. This is step 1 combined with
   `Good.pullback_snd`, since `FractionRing R'` is a field.
4. `good_iff` turns this into geometric reducedness of `redι _ ≫ pullback.snd _ _`. That is
   definitionally the morphism `(reducedOver ((Over.pullback (Spec.algebraMap R'
   (FractionRing R'))).obj ((Over.pullback b).obj X))).hom` of the statement.

The module sets `backward.isDefEq.respectTransparency false`, as its imports do. The proof
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
