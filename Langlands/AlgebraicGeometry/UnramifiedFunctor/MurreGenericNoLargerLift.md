# Murre's Lemma 2, first half of case (b) (statement)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericNoLargerLift`
defines one `Prop`-valued statement in the namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. It proves nothing.

The conditions `MurreConditions` are those of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps` (the ten
conditions of Murre's criterion, among them (F2) `FilteredColimits` and (F8)
`GenericNonLifting`). The helper `InfinitesimallyEtaleAt` (infinitesimal
étaleness of an element at a point, SGA 3, XI, Remark 1.8) is that of the
published module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps`.
The module imports the published `MurreEtaleLocusOpen`, which provides both.
`algebraOver g A` and `NoLargerLift` come from the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`, a
dependency of those modules:

- for `g : Spec R' ⟶ Spec R` and an `R'`-algebra `A`, `algebraOver g A` is
  `Spec A`, viewed as an object of `Over (Spec R)` through
  `Spec A → Spec R' → Spec R`;
- for an `R'`-algebra `B` and `ξ' ∈ F(algebraOver g (R' ⧸ 𝔍))`,
  `NoLargerLift B ξ'` says that the restriction of `ξ'` to `Spec (B/𝔍B)`
  extends to no closed subscheme `Spec (B/J)` of `Spec B` with `J < 𝔍B`. This
  is the property "cannot be lifted to a subscheme strictly larger" used in
  condition (F8).

## `GenericNoLargerLiftStatement`

`GenericNoLargerLiftStatement.{u, v}`: let `R : CommRingCat.{u}` be a
noetherian ring and `F : (Over (Spec R))ᵒᵖ ⥤ Type v` a presheaf with
`MurreConditions F`. Let `R'` be an étale `R`-algebra (`[Algebra R R']`,
`[Algebra.Etale R R']`, `R'` in universe `u`), `𝔍` an ideal of `R'`, and

```
ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍)))
```

an element of `F` over the closed subscheme `Spec (R'/𝔍)` of the étale
`Spec R`-scheme `Spec R'`. Let `y : PrimeSpectrum (R' ⧸ 𝔍)` be a point such
that

- `InfinitesimallyEtaleAt F ξ y`, and
- `y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) ≤ nilradical R`: the image of `y`
  in `Spec R` is contained in the nilradical. Since that image is prime,
  this means that `nilradical R` is prime, so `Spec R` is irreducible, and
  that `y` lies over its generic point.

Then there is an open set `V` of `Spec (R'/𝔍)` with `y ∈ V` such that for
every `w ∈ V`, with `Q := w.asIdeal.comap (Ideal.Quotient.mk 𝔍)` the prime
of `R'` under `w` and `R'_Q := Localization.AtPrime Q` the local ring of
`Spec R'` at the image of `w`:

- the ideal `𝔍 R'_Q` (`𝔍.map (algebraMap R' (Localization.AtPrime Q))`) is
  nilpotent, and
- `NoLargerLift (Localization.AtPrime Q) ξ`: the restriction of `ξ` to
  `Spec (R'_Q/𝔍R'_Q)` extends to no `Spec (R'_Q/J)` with `J < 𝔍 R'_Q`.

The proof is in the modules `MurreGenericLiftMaps`, `MurreGenericLiftDescent`,
`MurreGenericLiftAlgebra` and `MurreGenericNoLargerLiftProof`, as
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus.genericNoLargerLift`.

## Correspondence with Murre's proof

Murre's proof of Lemma 2 first reduces to the case where `Y → S` is a closed
immersion; he replaces `S` by an étale `S`-scheme `S'` and `F` by
`F' = F ×_S S'` (printed p.250). Then, by EGA 0_III 9.2.6, he shows that for
each point `y`, the set `{y}⁻ ∩ U` is empty or contains a nonempty open
subset of `{y}⁻`, where `U` is the étale locus. He distinguishes two cases
(printed p.251, PDF p.10). In case (b), the image `s` of `y` is the generic
point of an irreducible component of `S`. He shows:

1. Restricted to `Spec 𝒪_{S,y}`, `ξ` cannot be lifted to a subscheme of
   `Spec 𝒪_{S,y}` strictly larger than `Spec 𝒪_{Y,y}`. This uses that `ξ` is
   étale at `y`.
2. By (F8) there is a neighbourhood `W` of `y` such that, for all open
   `W₁ ⊆ W`, `ξ|(Y ∩ W₁)` cannot be lifted to a subscheme of `W₁` strictly
   larger.
3. Using (F2), for every `z` of `Y ∩ W`, the restriction of `ξ` to `Y_z`
   cannot be lifted to a subscheme of `Spec 𝒪_{S,z}` strictly larger than
   `Spec 𝒪_{Y,z}`.

On printed p.252 (PDF p.11) he deduces from this that `ξ` is étale at `z`.
`GenericNoLargerLiftStatement` is steps 1–3, with the following
differences:

- The étale scheme `S'` is `Spec R'` and `Y` is `Spec (R'/𝔍)`. The functor is
  not base changed: `F` stays a presheaf on `Over (Spec R)`, and
  `Spec (R'/𝔍)` and the local rings `R'_Q` are objects over `Spec R` through
  `Spec R'`.
- Murre's hypothesis that `s` is a generic point of a component of `S'` is
  replaced by the hypothesis that `y` lies over the generic point of `Spec R`.
  The proof deduces that the prime of `R'` under `y` is a minimal prime of
  `R'`.
- Murre's further reduction "which we can assume to be `S` itself" (`S`
  irreducible), and his remark that `Y` is then defined by a nilpotent ideal,
  are not hypotheses here. They appear in the conclusion as the nilpotency of
  `𝔍 R'_Q`. That conclusion is needed for the second half of case (b), the
  deduction that `ξ` is étale at `w`. The second half is not part of this
  statement.

## Sources and provenance

Provenance is derived: this is an intermediate statement of this project,
splitting Murre's case (b) at the point described above. Murre does not state
it separately. The remainder of Lemma 2 is the implication
`ClosedOfGenericStatement` of module `EtaleLocusClosedOfGeneric`, whose
hypothesis is this statement; it is proved as
`EtaleLocus.closedEtaleLocusOpen_of_generic` in `EtaleLocusAssembly`.

- J. P. Murre, *Representation of unramified functors. Applications
  (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki
  exp. 294 (1964–65), registered as
  `murre-1965-bourbaki-294-unramified-functors` (SHA-256
  `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`. Lemma 2: printed p.250 (PDF p.9).
  Case (b) of its proof: printed pp.251–252 (PDF pp.10–11). Condition (F2):
  printed p.244 (PDF p.3); condition (F8): printed p.246 (PDF p.5).
