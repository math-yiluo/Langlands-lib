# Two steps of Murre's proof of Proposition 2

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps`
states two steps of Murre's proof of his Proposition 2, which the Library
states as
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalStatement`.
It defines two helper predicates, two `Prop`-valued statements and their
conjunction, and proves nothing.

Throughout, `S : Scheme.{u}` and `F : (Over S)ᵒᵖ ⥤ Type v`. The conditions
`SmallValues`, `ZariskiSheaf` (F1a), `FaithfullyFlatSheaf` (F1b),
`FilteredColimits` (F2), `AdicLimits` (F3) and the helpers `algebraOver`,
`algebraOverBase` are those of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`.
`MurreConditions`, `UnramifiedRepresentable` and `baseChange` are those of the
published module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`.
Their Markdown records their correspondence with Murre's text.

An element `ξ ∈ F(U)`, for `U : Over S`, is the same as a morphism `U → F` of
presheaves on `Over S` (Yoneda). The two helpers state properties of this
morphism in terms of `ξ`.

## Helpers

- `IsMonoElement F ξ`, for `U : Over S` and `ξ : F.obj (op U)`: for every
  `T : Over S` and all `h₁ h₂ : T ⟶ U` with
  `F.map h₁.op ξ = F.map h₂.op ξ`, we have `h₁ = h₂`. This says that
  `ξ : U → F` is a monomorphism of presheaves: for every `S`-scheme `T`, the
  map `Hom_S(T, U) → F(T)`, `h ↦ ξ ∘ h`, is injective.
- `InfinitesimallyEtaleAt F ξ y`, for `ξ : F.obj (op U)` and a point
  `y : U.left`: for every local artinian ring `A : Type u`, every morphism
  `f : Spec A ⟶ S`, every nilpotent ideal `J` of `A`, every `S`-morphism
  `u₀ : Spec (A/J) ⟶ U` (from `algebraOver f (A ⧸ J)`, that is,
  `Spec (A/J) ⟶ Spec A ⟶ S`) whose underlying map sends every point (there is
  only one) to `y`, and every `v : F.obj (op (Over.mk f))` with
  `F.map u₀.op ξ = F.map (algebraOverBase f (A ⧸ J)).op v`, there is exactly
  one `S`-morphism `u : Over.mk f ⟶ U` with
  `algebraOverBase f (A ⧸ J) ≫ u = u₀` and `F.map u.op ξ = v`.

  This is SGA 3, XI, Remarks 1.6–1.8 for the morphism `ξ : U → F`. Remark 1.6
  calls a morphism of functors `X → G` formally étale if for every affine
  `S′` over `S` and every closed subscheme `S′₀` defined by a nilpotent ideal,
  the map `X(S′) → X(S′₀) ×_{G(S′₀)} G(S′)` is bijective, that is, every
  commutative square `S′₀ → X`, `S′ → G` has exactly one diagonal filler.
  Remark 1.7 defines "formally étale at a point `x` of `X`" by imposing the
  condition only for local `S′` and squares whose map `S′₀ → X` is compatible
  with `x` at the closed point; when `X` is a scheme, this compatibility says
  that the closed point of `S′₀` is sent to the point `y` of `X` underlying
  `x`. Remark 1.8 calls the morphism infinitesimally étale at `x` when the
  condition holds for local artinian `S′`. In the Lean definition `X = U`,
  `G = F`, `S′ = Spec A` with `A` local artinian (`Spec A` has one point,
  which is closed), and `S′₀ = Spec (A/J)`.

## Statements

- `MurreChartGluingStatement.{u, v}` (Murre's Lemma 3, in the form of SGA 3,
  XI, Proposition 3.5): let `S : Scheme.{u}` be locally noetherian and let
  `F : (Over S)ᵒᵖ ⥤ Type v` satisfy `SmallValues F`, `ZariskiSheaf F`,
  `FaithfullyFlatSheaf F`, `FilteredColimits F` and `AdicLimits F`. Let
  `ι : Type u`, `U : ι → Over S` and `ξ : ∀ i, F.obj (op (U i))` be such that
  every `(U i).hom` is locally of finite type, every `ξ i` satisfies
  `IsMonoElement F (ξ i)` and `InfinitesimallyEtaleAt F (ξ i) y` for every
  point `y` of `(U i).left`, and every point of `F` with values in a field
  factors through some `ξ i`: for every field `K : Type u`, every
  `f : Spec K ⟶ S` and every `η : F.obj (op (Over.mk f))` there are `i` and
  `h : Over.mk f ⟶ U i` with `F.map h.op (ξ i) = η`. Then there are
  `Y : Scheme.{u}`, `q : Y ⟶ S` and `e : F.RepresentableBy (Over.mk q)` such
  that `q` is locally of finite type, for every `i` the underlying morphism of
  schemes `(e.homEquiv.symm (ξ i)).left : (U i).left ⟶ Y` of the `S`-morphism
  corresponding to `ξ i` is an open immersion, and every point of `Y` lies in
  the range of one of these open immersions.
- `MurreNoetherianChartsStatement.{u, v}` (the inductive step of Murre's proof
  of Proposition 2 over an affine noetherian base, before the final
  application of Lemma 3): let `R : CommRingCat.{u}` be noetherian and let
  `F : (Over (Spec R))ᵒᵖ ⥤ Type v` satisfy `MurreConditions F`. Suppose that
  `UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F)` holds for
  every point `s : Spec R`, and that
  `UnramifiedRepresentable (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F)`
  holds for every ideal `I ≠ ⊥` of `R`, that is, the base change of `F` to
  every closed subscheme `Spec (R/I)` other than `Spec R` itself is represented
  by a separated, locally of finite type, formally unramified scheme. Then
  there are `ι : Type u`, `U : ι → Over (Spec R)` and
  `ξ : ∀ i, F.obj (op (U i))` such that for every `i` the morphism `(U i).hom`
  is locally of finite type and formally unramified, `IsMonoElement F (ξ i)`
  holds and `InfinitesimallyEtaleAt F (ξ i) y` holds for every point `y`, and
  every point of `F` with values in a field factors through some `ξ i`, in the
  same sense as in the previous statement.

- `MurreLocalToGlobalStepsStatement.{u, v}` is the conjunction
  `MurreChartGluingStatement ∧ MurreNoetherianChartsStatement`.

None of these statements is proved here.

## Sources and provenance

- J. P. Murre, *Representation of unramified functors. Applications (according
  to unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp. 294
  (1964–65), registered as `murre-1965-bourbaki-294-unramified-functors`
  (SHA-256 `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`. Proposition 2, its remark and
  Lemma 2 with the remark after it: printed p.250 (PDF p.9). Lemma 3 and
  Lemma 4: printed p.252 (PDF p.11). Proof of Proposition 2: printed
  pp.252–253 (PDF pp.11–12).
- A. Grothendieck, SGA 3, Exposé XI, provisional recomposition by P. Gille
  and P. Polo (version of 5 December 2008), registered as
  `sga3-exposes-xi-xii-xiv-gille-polo-2008` (folder SHA-256
  `dd37c114bfb569a0d39c1cce727a0d87a8d40abf545d13e0b1a2d886d03b7498`), file
  `Expo11.pdf`. Printed page `p` is PDF page `p − 84`. Remark 1.5:
  printed pp.87–88 (PDF pp.3–4). Remarks 1.6–1.8: printed pp.88–89 (PDF
  pp.4–5). Proposition 3.5, Remark 3.6 and the proof of
  3.5: printed pp.96–97 (PDF pp.12–13). The Library has no errata note for
  this source.

### `IsMonoElement` and `InfinitesimallyEtaleAt`

Murre's Lemmas 3 and 4 and the proof of Proposition 2 speak of morphisms
`ξ : U → F` that are monomorphisms and étale. In the remark after Lemma 2 he
defines "`ξ` is étale at `y`" through the representing scheme of the base
change of `F` to `Spec 𝒪_{S,s}`, and notes that the notion can be defined
entirely in terms of the functor, citing SGA 3, XI, Remarks 1.6 and 1.7. The
helpers use the functorial notion, in the infinitesimal form of SGA 3, XI,
Remark 1.8, which is the notion in the hypotheses of SGA 3, XI,
Proposition 3.5 (b). Over a locally noetherian base, when the base changes of
`F` to the local schemes `Spec 𝒪_{S,s}` are represented by schemes locally of
finite type, the two notions agree for `U` locally of finite type (SGA 3, XI,
Remark 1.5 with Remark 1.7); this comparison is not formalized here and is not
used by the statements.

### `MurreChartGluingStatement`

Murre's Lemma 3 reads: "Let `F` be as in proposition 2. Suppose that for
every point `x ∈ F` … there exists `T : U → S` and `ξ : U → F` such that `T`
is of finite type, `ξ` a monomorphism and étale. Then `F` is representable
(follows from SGA 3, XI, prop. 3.5)." The statement follows SGA 3, XI,
Proposition 3.5, with this correspondence.

- "`S` localement noethérien" is `[IsLocallyNoetherian S]`.
- Hypothesis (a): "`F` est un faisceau pour la topologie fidèlement plate
  quasi-compacte" is `ZariskiSheaf F` together with `FaithfullyFlatSheaf F`
  (Murre's (F1)); "commute aux limites inductives d'anneaux" is
  `FilteredColimits F` (Murre's (F2)); "commute aux limites projectives
  adiques d'anneaux locaux artiniens" is `AdicLimits F` (Murre's (F3)).
  Murre's Lemma 3 assumes all conditions of Proposition 2; only these are
  needed for SGA 3's proof, so the statement assumes only these.
- `SmallValues F` is required because `F` takes values in `Type v` while the
  representing scheme must lie in `Scheme.{u}`; it is part of `MurreConditions`.
- The family `(Xᵢ, uᵢ)_{i ∈ I}` of `S`-schemes locally of finite type with
  `S`-morphisms `uᵢ : Xᵢ → F` is `U : ι → Over S` with
  `LocallyOfFiniteType (U i).hom` and `ξ i ∈ F(U i)`. The index type is
  `u`-small.
- Hypothesis (b): the `uᵢ` are monomorphisms (`IsMonoElement F (ξ i)`) and
  infinitesimally étale in the sense of 1.8, that is, at every point
  (`∀ y, InfinitesimallyEtaleAt F (ξ i) y`).
- Hypothesis (c): the family is "ensemblistement surjective", which
  Remark 3.6 explains: every point of `F` with values in a field `k` comes from
  a point of some `Xᵢ` with values in an extension of `k`. The statement
  assumes the stronger condition that every point of `F` with values in a
  field `K` comes from a `K`-valued point of some `U i`, without extending the
  field. This matches Murre's formulation ("for every point `x ∈ F` there
  exists … `ξ : U → F`" through which `x` factors), and it makes the statement
  a special case of Proposition 3.5. Fields range over `Type u`.
- Conclusion: "`F` est représentable par un préschéma localement de type fini
  sur `S` (et les `uᵢ` sont des immersions ouvertes, qui font de la famille des
  `Xᵢ` un recouvrement ouvert de `F`)". The representing scheme is
  `q : Y ⟶ S` with `e : F.RepresentableBy (Over.mk q)` and
  `LocallyOfFiniteType q`. Under `e`, `ξ i` corresponds to the `S`-morphism
  `e.homEquiv.symm (ξ i) : U i ⟶ Over.mk q`, whose underlying morphism of
  schemes is required to be an open immersion; the images of these open
  immersions cover `Y`.

### `MurreNoetherianChartsStatement`

Provenance is derived from Murre's proof of Proposition 2 (PDF pp.11–12):
"We proceed by noetherian induction. Starting with `x ∈ F`, i.e. `x ∈ F_s`
for some `s ∈ S`, we take an open affine neighbourhood of `x` in `X(s)` and
we take `U(s)` to be of finite type over `Spec(𝒪_{S,s})`. Then we obtain
(EGA IV 8.8.2) a `T : U → S` of finite type such that
`U ×_S Spec(𝒪_{S,s}) = U(s)`; we can take `U` so small that `U` is
non-ramified and separated over `S` and that there exists a `ξ : U → F` (use
(F2)) such that `ξ` restricted to `Spec(𝒪_{S,s})` is the canonical injection.
Moreover, using lemma 1, we can assume that `ξ` is étale [this uses Lemma 2].
We want to show that we can take `U` so small that `ξ` is a monomorphism …
[by Lemma 4 and EGA IV 8.8.2]. Finally we do this for every point `x ∈ F`, and
we apply lemma 3." The statement is this argument up to the application of
Lemma 3, with these choices.

- **Affine noetherian base.** Noetherian induction needs a noetherian base.
  The statement is made over `Spec R` with `R` noetherian; Murre's induction
  runs over the closed subschemes of a noetherian base, and representability
  is local on `S`.
- **Induction hypothesis.** Murre's Lemma 2, used in the step "we can assume
  that `ξ` is étale", assumes that "`F` is representable on all closed
  subschemes of `S` (strictly contained in `S`)". The closed subschemes of
  `Spec R` are the `Spec (R/I)`, and `Spec (R/I)` is strictly contained in
  `Spec R` exactly when `I ≠ 0`. Representability of `F` on `Spec (R/I)` is
  representability of the base change
  `baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F`. As in
  `MurreLocalToGlobalStatement`, representability is by a separated, locally
  of finite type, formally unramified scheme (Murre's remark after
  Proposition 2).
- **Hypotheses of Proposition 2.** `MurreConditions F` and the representability
  of the base changes to every `Spec 𝒪_{Spec R, s}` are the hypotheses of
  `MurreLocalToGlobalStatement` over `Spec R`.
- **Charts.** The conclusion is the family of all the morphisms `ξ : U → F`
  constructed in the argument, indexed by a `u`-small type. Each `U` is
  required to be locally of finite type over `Spec R` (Murre obtains finite
  type) and formally unramified (Murre takes `U` non-ramified); separatedness
  of `U` is not recorded. Each `ξ` is a monomorphism and infinitesimally étale
  at every point (the functorial notion explained above). "We do this for
  every point `x ∈ F`" is recorded as: every point `η` of `F` with values in a
  field `K` factors through some `ξ i` by a `K`-valued point of `U i`. In
  Murre's construction such an `η`, lying over `s`, is a `K`-point of the
  scheme `X(s)` representing the base change of `F` to `Spec 𝒪_{S,s}`, and it
  factors through the chart built from an affine neighbourhood of its image
  point in `X(s)`.
