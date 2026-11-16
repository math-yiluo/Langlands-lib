# Step 1 of Murre's induction: the criterion over a local artinian base

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreArtinianBase`. It proves

```
theorem Langlands.AlgebraicGeometry.UnramifiedFunctor.murreArtinianBase :
    MurreArtinianBaseStatement.{u, v}
```

for arbitrary universes `u` and `v`. This is the statement
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreArtinianBaseStatement` of the Library module
`MurreLocalStepParts`. Let `R : CommRingCat.{u}` be a local artinian ring and let
`F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfy `MurreConditions F`. Then `UnramifiedRepresentable F`
holds: `F` is represented by some `q : Y ⟶ Spec R` that is separated, locally of finite type
and formally unramified.

This is Step 1 of Case I of Murre's proof (J. P. Murre, *Representation of unramified
functors. Applications*, Séminaire Bourbaki exp. 294, printed p. 247, PDF p. 6; registered as
`murre-1965-bourbaki-294-unramified-functors`). Of the ten conditions only these are used:
`SmallValues`, (F1a) `ZariskiSheaf`, (F1b) `FaithfullyFlatSheaf`, (F2) `FilteredColimits`, (F3)
`AdicLimits`, (F4′) `ArtinianLifting` and strong (F5) `NilpotentInjective`.

## Route, compared with Murre

Murre pro-represents `F` at its points by (F4), using complete local rings `A_i`. He glues
`X = ∐ Spec A_i → F` by (F1) and concludes with his Lemma 1 (the Library statement
`MurreArtinianDetectionStatement`, which is not used here).

The Lean proof avoids Lemma 1 and pro-representability. It builds, directly from (F4′) and
strong (F5), a family of affine charts `Spec B ⟶ F`. The family is indexed by `ChartIdx F`.
Each indexed `B` is an artinian ring, of finite type and formally unramified over `R`
(`ChartData.Good`). Locality of `B` is not part of the index condition. The charts constructed
in `ArtinianBaseChart` are quotients `E/J` of a local ring `E` with `J ≤ ker πE`. They are
therefore local, but Lean does not record this, and the family also contains every other chart
satisfying `ChartData.Good`. The charts are glued with the Library theorem
`ChartGluing.murreChartGluing` (module `ChartGluingRepr`), which is Murre's Lemma 3 in the form
of SGA 3, XI, Proposition 3.5. The resulting scheme `Y` has the discrete topology
(`discreteTopology_of_cover`), and this is used to prove separatedness. Lean proves nothing
further about the shape of `Y`.

## Supporting modules

The proof uses nine internal supporting modules. They are listed in import order, each with
its own Markdown.

* `ArtinianBaseTools`: restriction maps, separation by field points (F1a + F5), descent along
  faithfully flat maps (F1b), products (F1a), the predicate `IsOver` (an element lying over a
  field point), and (F4′) in terms of `IsOver`.
* `ArtinianBaseChain`: chains of length-one extensions with the same residue field, and closure
  of liftability under intersections of ideals.
* `ArtinianBaseFlat`: finite free local extensions with prescribed residue field.
* `ArtinianBaseDescent`: the descent problem for finite extensions `C ⊆ A` of local artinian
  rings. An element of `F(Spec A)` over a field point `η` of `C` forces `η` to lift to
  `F(Spec C)` (normal closure, flat base change, (F1b)).
* `ArtinianBaseGeneral`: the same for arbitrary local artinian `A ⊇ C`, via (F2), the Krull
  intersection theorem and the Nullstellensatz.
* `ArtinianBaseField`: purely inseparable and Galois descent of field points, minimal fields of
  definition, and the monomorphism property of minimal points on field-valued points.
* `ArtinianBaseChart`: the chart `E_L/J` of a minimal field point. `E_L` is a formally étale
  lift of `L`, and `J` is the least ideal to which the point lifts. The chart is proved
  infinitesimally étale and injective on field points at the ring level.
* `ArtinianBaseSpec`: translation of these ring-level properties into the Library's
  `IsMonoElement` and `InfinitesimallyEtaleAt`.
* `ArtinianBaseProof`: the `u`-small index type `ChartIdx F` of charts, and the theorem that
  every point of `F` with values in any field factors through a chart.

## This module

* `discreteTopology_of_cover`: a scheme covered by open immersions from discrete schemes is
  discrete. Each point is the image of an open point.
* `valuativeUniqueness_of_discrete`: for any `q : Y ⟶ S` with `Y` discrete, lifts in valuative
  squares are unique (`ValuativeCriterion.Uniqueness q`).
  - A lift `Spec V ⟶ Y` is constant: every point of `Spec V` specializes to the closed point,
    and `Y` is T1.
  - Two lifts agree on the image of `Spec K`, hence have the same value `y`. Both factor
    through an affine open `Spec B ∋ y` (`IsOpenImmersion.lift`).
  - There they are `Spec` of ring maps `B → V` that agree after composing with the injection
    `V → K`, so they are equal.
* `murreArtinianBase`:
  1. Apply `ChartGluing.murreChartGluing` over `S = Spec R` (locally noetherian, since `R` is
     artinian). The family is indexed by `ChartIdx F`, with `Uᵢ = Spec (PRing i)` and
     `ξᵢ = i.elem`.
     - `Uᵢ ⟶ Spec R` is locally of finite type (`Charts.locallyOfFiniteType_ovR`).
     - Each `ξᵢ` is a monomorphism and infinitesimally étale, by the definition of the index.
     - For the factorization of field points `Spec K ⟶ Spec R`, `K` is made an `R`-algebra
       through `Spec.preimage`. The object `Over.mk f` is identified with `ovR R K`, and
       `exists_fac_field` applies.
  2. The theorem returns `Y`, `q`, a representation `e` of `F` by `Over.mk q`, and that `q`
     is locally of finite type. The chart morphisms `Uᵢ ⟶ Y` are open immersions covering `Y`.
  3. `Y` is discrete by `discreteTopology_of_cover`, since each `Uᵢ` is the spectrum of an
     artinian ring. Hence `q` is quasi-separated (`Y` is T2). It is separated by
     `IsSeparated.of_valuativeCriterion` and `valuativeUniqueness_of_discrete`.
  4. `q` is formally unramified by `IsZariskiLocalAtSource.of_openCover` on the chart cover.
     On `Uᵢ` the composite with `q` is `Uᵢ ⟶ Spec R`, which is formally unramified since
     `PRing i` is (`Charts.formallyUnramified_ovR`).

No hypothesis is added to the statement. The proof uses no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.
