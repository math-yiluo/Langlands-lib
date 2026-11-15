# Reduction of Murre's Lemma 2 to closed subschemes of étale schemes (proof)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosedProof`
proves

```
theorem EtaleLocus.murreEtaleLocusOpen_of_closed : ClosedReductionStatement.{u, v}
```

(namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor`), that is,
`ClosedEtaleLocusOpenStatement → MurreEtaleLocusOpenStatement`: Murre's
Lemma 2 for closed subschemes `Spec (R'/𝔍)` of étale `Spec R`-schemes
`Spec R'` implies Murre's Lemma 2. The statements are explained in
`MurreEtaleLocusClosed.md`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

Besides the statement module it imports the published module
`MurreChartsLocal` (namespace `Charts`) and Mathlib's
`Mathlib.RingTheory.Unramified.LocalStructure`. Auxiliary results are in the
namespace `ClosedReduction`.

## Open subschemes (section `Open`)

For a presheaf `F` on `Over S`, an open immersion `ι : V ⟶ U` in `Over S`
(that is, `ι.left` is an open immersion), `ξ ∈ F(U)` and a point `y` of `V`:

- `infinitesimallyEtaleAt_of_isOpenImmersion`: if the restriction
  `F.map ι.op ξ` is infinitesimally étale at `y`, then `ξ` is infinitesimally
  étale at `ι.left y`. Proof: by `Charts.infinitesimallyEtaleAt_of_factor`
  applied to `ι`, it suffices that every morphism from the spectrum of a
  local artinian ring `L` to `U` whose image is the point `ι.left y` factors
  uniquely through `ι.left` (by `IsOpenImmersion.lift`, since its image lies
  in the range of `ι.left`; uniqueness because `ι.left` is a monomorphism),
  and that the restriction is infinitesimally étale at every point of `V`
  over `ι.left y`; the only such point is `y`, as `ι.left` is injective on
  points.
- `infinitesimallyEtaleAt_map_iff`: the two conditions are equivalent; the
  converse direction is the published `Charts.infinitesimallyEtaleAt_restrict`.

## Local structure (section `Chart`)

`exists_closed_chart` is EGA IV, Corollary 18.4.7, in the form needed: if
`U : Over (Spec R)` is locally of finite type and formally unramified, then
every point `y` of `U` lies in the image of an open immersion
`ι : algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍) ⟶ U`
in `Over (Spec R)`, for some étale `R`-algebra `R'` (in universe `u`) and
ideal `𝔍` of `R'`.

Proof. Choose an affine open `f : Spec C ⟶ U.left` containing `y`
(`Scheme.exists_affine_mem_range_and_range_subset`), and let `y₀` be the
point of `Spec C` over `y`. The composite `f ≫ U.hom` is `Spec.map φ` for a
ring map `φ : R ⟶ C` (`Spec.preimage`), which makes `C` an `R`-algebra.
`Spec.map φ` is locally of finite type and formally unramified, being the
composite of an open immersion with `U.hom` (formal unramifiedness of the open
immersion `f` holds because its diagonal is an isomorphism); hence `C` is a
finite type, formally unramified `R`-algebra (`HasRingHomProperty.Spec_iff`),
and so unramified at `y₀`. Mathlib's local structure theorem for unramified
algebras, `Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, gives
`s ∈ C` with `s ∉ y₀`, a standard étale pair `P` over `R` and a surjective
`R`-algebra map `ψ : P.Ring → C[1/s]`. Put `R' := P.Ring` (étale over `R`)
and `𝔍 := ker ψ`, so that `R'/𝔍 ≅ C[1/s]` as `R`-algebras
(`Ideal.quotientKerAlgEquivOfSurjective`). Through this isomorphism `R'/𝔍` is
a localization of `C` away from `s`, so `Spec (R'/𝔍) → Spec C` is an open
immersion (`IsOpenImmersion.of_isLocalization`) whose image contains `y₀`
(`PrimeSpectrum.localization_away_comap_range`). Its composite with `f` is
the required `ι`; it is a morphism over `Spec R` because the isomorphism
`R'/𝔍 ≅ C[1/s]` is `R`-linear.

## The reduction (`EtaleLocus.murreEtaleLocusOpen_of_closed`)

Assume `ClosedEtaleLocusOpenStatement`, and take `R`, `F` and the hypotheses
of `MurreEtaleLocusOpenStatement`, together with `U` (locally of finite type,
quasi-compact, separated, formally unramified over `Spec R`) and
`ξ ∈ F(U)`. Only local finiteness and formal unramifiedness of `U` are used.
Openness of `W := {y | InfinitesimallyEtaleAt F ξ y}` is checked at each
point `y ∈ W` (`isOpen_iff_forall_mem_open`). Take `ι` from
`exists_closed_chart` with `y = ι.left y'`. The hypothesis, applied to the
same `R`, `F` and hypotheses on them and to the restriction
`F.map ι.op ξ`, says that the étale locus `W'` of the restriction in
`Spec (R'/𝔍)` is open. Its image `ι.left '' W'` is open because `ι.left` is
an open embedding, it contains `y` and is contained in `W` by
`infinitesimallyEtaleAt_map_iff`.

## Relation to the literature

This is the first step of Murre's proof of Lemma 2 (Bourbaki exp. 294,
printed p.250, PDF p.9), in which `Y` is replaced by a neighbourhood of a
point that factors as a closed immersion into an étale `S`-scheme. Murre gives
no reference for the factorization; it is EGA IV, Corollary 18.4.7 (printed
p.121, PDF p.120 of `grothendieck-dieudonne-ega-iv4-1967`), here taken from
Mathlib's local structure theorem for unramified algebras. Murre's subsequent
base change of `F` to the étale scheme is not part of this proof (see
`MurreEtaleLocusClosed.md`).
