# Fppf Picard classes of a proper flat family with integral fibres and a section

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). The proposition restates,
for the Library's fppf Picard class sheaf, Kleiman's description of
`Pic_{(X/S)(fppf)}(T)` as `Pic(X_T)/Pic(T)` when `f` has a section and
`O_S ⥲ f_*O_X` holds universally. The assembly proof of Kleiman's Theorem 4.8 in
Task 5705 needs it in this explicit form: every section of the sheaf is the
class of an actual line bundle, and two line bundles have the same class
exactly when they differ by the pullback of an invertible module on the base.

No proof is asserted here.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`).

### Hypotheses

It quantifies over schemes `S X : Scheme.{u}` and a morphism `f : X ⟶ S`, and
assumes that

- `f` is proper (`IsProper`), flat (`Flat`), locally of finite presentation
  (`LocallyOfFinitePresentation`) and geometrically integral
  (`GeometricallyIntegral`: every fibre over the spectrum of a field is
  integral);
- `f` has a section: there is `ε : S ⟶ X` with `ε ≫ f = 𝟙 S`.

### Conclusion

For every scheme `T` over `S` (an object `T : Over S`, with no finiteness
condition), write `X_T = (relativeSpace f).obj T`, which is the Library's
chosen fibre product `pullback T.hom f`, and
`g = (relativeProjection f).app T = pullback.fst T.hom f : X_T ⟶ T.left`.
Then both of the following hold.

1. **Every class comes from a line bundle.** Every element
   `ξ : (RelativePicard.classSheafPresheaf f).obj (op T)` equals
   `RelativePicard.sheafClassOf f T L` for some `L : LineBundle X_T`.
2. **Equality of classes.** For `L L' : LineBundle X_T`,
   `sheafClassOf f T L = sheafClassOf f T L'` if and only if there is a module
   `N : T.left.Modules` with `Scheme.Modules.IsInvertible N` and an isomorphism
   of modules `L.obj ≅ L'.obj ⊗ (Scheme.Modules.pullback g).obj N`.

The Library objects used are:

- `RelativePicard.classSheafPresheaf f`
  (`Langlands/AlgebraicGeometry/Picard/RelativePicardSheaf.lean`): the
  underlying presheaf of the fppf sheafification, for
  `Scheme.fppfTopology.over S`, of `RelativePicard.classPresheaf f`. That
  presheaf sends `T` to the set of isomorphism classes of line bundles on `X_T`,
  so it is Kleiman's absolute functor `Pic_X` (Definition 2.1) on `S`-schemes;
- `RelativePicard.sheafClassOf f T L`: the image of the isomorphism class of
  `L` under the sheafification unit;
- `LineBundle X_T`: modules on `X_T` that are locally free of rank one
  (`IsLocallyFreeRankOne`); `L.obj` is the underlying module.

The tensor product `⊗` elaborates to the FLT port's monoidal structure on
module sheaves (`AlgebraicGeometry.Scheme.Modules.monoidalCategory`, from
`Def_SheafOfModules_MonoidalV2`). `Scheme.Modules.IsInvertible` is the FLT port's
notion of an invertible module. These are the same tensor product and
invertibility predicate as in the accepted companion statement
`PicardHilbertPolynomialPiecesStatement`, whose twist-invariance clause has the
same shape (`L ≅ L' ⊗ g^* N` with `N` invertible).

## Source and derivation

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), registered as `kleiman-2005-picard-scheme-arxiv-math0504020v1`.

- **Definition 2.2** (p.17) defines `Pic_{X/S}(T) := Pic(X_T)/Pic(T)` and its
  fppf sheaf `Pic_{(X/S)(fppf)}`. The paragraph after it notes that this sheaf
  is also the sheaf associated to the absolute functor `Pic_X`. This is why the
  Library's sheafification of `classPresheaf f` (classes in `Pic(X_T)`, not
  divided by `Pic(T)`) is Kleiman's `Pic_{(X/S)(fppf)}`.
- **Exercise 3.11** (p.25): if `f` is proper and flat with geometrically reduced
  and connected fibres, then `O_S ⥲ f_*O_X` holds universally. Geometrically
  integral fibres are geometrically reduced and connected.
- **Theorem 2.5** (p.18): if `O_S ⥲ f_*O_X` holds universally, then
  `Pic_{X/S} → Pic_{(X/S)(fppf)}` is injective (Part 1). If moreover `f` has a
  section, it is an isomorphism (Part 2). Hence for every `T`,
  `Pic(X_T)/Pic(T) ⥲ Pic_{(X/S)(fppf)}(T)`, induced by `L ↦ sheafClassOf L`.
- Conclusion 1 is the surjectivity in Part 2.
- Conclusion 2 is the injectivity in Part 1, written out. The class of `L` in
  `Pic(X_T)/Pic(T)` is the class of `L` modulo the image of
  `g^* : Pic(T) → Pic(X_T)`. So two line bundles have the same image exactly
  when `L ≅ L' ⊗ g^* N` for an invertible `N` on `T`. (Kleiman's proof of
  Part 1, p.19, produces such an `N` by pushing forward a line bundle, using
  Lemma 2.7, p.18.)

**Scope beyond Kleiman's convention.** Kleiman works throughout with locally
noetherian schemes (p.15). He also notes that the restriction can be removed by
a standard limit argument. This statement imposes no noetherian or finiteness
condition on `S` or `T`. It assumes `f` locally of finite presentation in place
of finite type over a locally noetherian base. The general form is already
supported by the Library, which proves both ingredients on the whole slice
category:

- `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralRigidifiedComparison.relativeProjection_app_isIso`
  (`Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralRigidifiedComparison.lean`)
  shows that `O_T ⥲ g_*O_{X_T}` on every open of every `T : Over S`, for `f`
  proper, flat, locally of finite presentation and geometrically integral.
  This is Exercise 3.11 without noetherian hypotheses.
- `RigidifiedLineBundle.properFlatIntegralClassIso` (same file) is an
  isomorphism, for every `T : Over S`, between `ε`-rigidified line-bundle
  classes on `X_T` and `RelativePicard.classSheafPresheaf f` at `T`, whose
  forward map forgets the rigidification and sheafifies. This is Part 2 of
  Theorem 2.5 in rigidified form; Kleiman's proof (pp.19–20) also passes
  through rigidified sheaves, Lemmas 2.9 and 2.10.

The proposition is therefore a derived restatement of Theorem 2.5 together with
Exercise 3.11, in the explicit form "every class is `sheafClassOf L`, and the
fibres of `L ↦ sheafClassOf L` are the `Pic(T)`-orbits". It is not a verbatim
statement of the source.

## Conventions and scope

- The hypotheses on `f` are exactly those of the Library's
  `properFlatIntegralClassIso`, written as explicit arguments, with the
  section as an existential.
- Both conclusions are stated for every `T : Over S`. The intended consumer, the
  assembly proof for Task 5705, uses them for locally noetherian `T`; there
  `S` is the spectrum of a noetherian ring.
- The invertible module `N` in conclusion 2 is existential and not asserted to
  be unique. (Uniqueness up to isomorphism also holds, by Kleiman's Lemma 2.7,
  but is not part of this proposition.)
