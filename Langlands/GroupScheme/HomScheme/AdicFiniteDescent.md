# Finite étale descent of algebraized adic Hom systems

This internal module contains the descent argument for the finite étale step of
SGA 3, Exposé IX, Théorème 7.1. It does not prove the affine case. Instead, it
takes the affine existence and uniqueness of algebraizations as explicit
hypotheses. It then shows that they give bijectivity of the restriction map
`System.restrict I H G` whenever the source group becomes diagonalizable after a
finite étale surjective base change.

Throughout, `A` is a commutative ring with ideal `I`, and `H`, `G` are group
schemes over `Spec A`. `System I H G` is the type of compatible adic Hom
systems. `System.IsAlgebraization s a` is the predicate from
`Langlands.GroupScheme.HomScheme.AdicAlgebraization`: `a` induces `s` on every
test scheme lying over some thickening `Spec A/I^(n+1)`. No noetherian or
completeness hypothesis appears in this module. Those hypotheses enter only
through the two affine inputs.

## Finite test schemes are spectra of finite algebras

`exists_spec_iso_of_isFinite` takes a test scheme `V` over `Spec A` with finite
structure map. It produces a commutative ring `C`, a finite ring map
`ψ : A →+* C`, and an isomorphism `Over.mk (Spec.map ψ) ≅ V` over `Spec A`.
Here `C` is the ring of global sections of `V`, which is affine because finite
morphisms are affine. `ψ` is the global-sections map composed with
`Γ(Spec A) ≅ A`, and it is finite by `finite_appTop`. The isomorphism is
`V.isoSpec` inverted. Compatibility with the structure maps is
`Scheme.isoSpec_inv_naturality`.

`isDiagonalizable_of_overIso` transfers diagonalizability of the pulled-back
source group along an isomorphism `W ≅ V` of test schemes. It combines
`IsDiagonalizable.baseChange` with `IsDiagonalizable.of_iso`, using the
canonical comparison isomorphism between the two iterated base changes.

## The affine inputs, as hypotheses

* `AffineAlgebraizationExists I H G`: for every finite ring map
  `ψ : A →+* C` such that `H` becomes diagonalizable over `Spec C`, every
  system `s` has an algebraization over `Over.mk (Spec.map ψ)`.
* `AffineAlgebraizationUnique I H G`: under the same hypotheses on `ψ`, any
  two algebraizations of the same system over `Over.mk (Spec.map ψ)` are equal.

These are `Prop`-valued definitions used only as hypotheses here. The companion
module `Langlands.GroupScheme.HomScheme.AdicFiniteTest` proves them, for
noetherian `I`-adically complete `A` and affine `G`, from the diagonalizable
comparison statement.

`exists_isAlgebraization_of_isFinite` and `eq_of_isAlgebraization_of_isFinite`
move these inputs from spectra of finite algebras to arbitrary finite test
schemes `V` on which `H` becomes diagonalizable. Choose `V ≅ Spec C` as above.
For existence, evaluate the affine algebraization along the inverse
isomorphism. `System.isAlgebraization_evaluate` keeps the algebraization
property. For uniqueness, evaluate both algebraizations along the isomorphism,
apply affine uniqueness, and evaluate back. `evaluate_comp` and `evaluate_id`
show that evaluating along the isomorphism and then its inverse is the
identity.

## Descent along a finite étale surjective cover

Let `p : S' → Spec A` be a morphism of schemes. `overlapFst p` and
`overlapSnd p` are the two projections of the double overlap `S' ×_A S'`,
viewed as maps of test schemes from `Over.mk (fst ≫ p)` to `Over.mk p`.

`compatible_of_evaluate_eq` takes `f : RelativeHom H G (Over.mk p)` whose
evaluations along the two overlap projections agree. It proves that `f` is
compatible with the canonical descent data of the Library's
`Descent.canonicalDatum p H` and `Descent.canonicalDatum p G`. By definition,
evaluation along an overlap projection is `Descent.pullHom`. So the hypothesis
is an equality of conjugates by the comparison isomorphisms
`Descent.pullbackComparison`. Conjugating back gives the identity
`Descent.Compatible`.

`restrict_bijective_of_finiteEtale` assumes `IsFinite p`, `Etale p`,
`Surjective p`, the two affine hypotheses, and diagonalizability of
`(baseChange p).obj H`. It concludes that `System.restrict I H G` is bijective.

* **Injectivity.** Suppose `f g : H ⟶ G` have the same restriction system.
  By `System.isAlgebraization_restrict`, the constant families of `f` and `g`
  over `Over.mk p` both algebraize that system. Uniqueness over the finite test
  scheme `Over.mk p` makes them equal. The pullback functor `Over.pullback p`
  on schemes over `Spec A` is faithful: `p` is étale, hence flat and locally
  of finite presentation, and surjective, so Mathlib's faithfulness instance
  for pullback along such morphisms applies. Applying
  `(Over.pullback p).map_injective` to the underlying scheme maps gives
  `f = g` as group-scheme homomorphisms, by `Grp.hom_ext`.
* **Surjectivity.** Let `s` be a system. Existence over `Over.mk p` gives an
  algebraization `fU`. The double overlap `Over.mk (fst ≫ p)` is again finite
  over `Spec A`, and `H` is diagonalizable over it: base-change
  diagonalizability along `fst`, then use the comparison isomorphism. Both
  evaluations of `fU` along the overlap projections algebraize `s`, by
  `System.isAlgebraization_evaluate`. Uniqueness over the overlap makes them
  equal. By `compatible_of_evaluate_eq`, `fU` is compatible with the canonical
  descent data. The Library's étale descent of homomorphisms,
  `Descent.EtaleHomDescent.hom`, produces `f : H ⟶ G` with
  `(baseChange p).map f = fU`, by `Descent.EtaleHomDescent.baseChange_hom`.

  It remains to show `restrict I H G f = s`. Fix a level `n` and write
  `q : Spec A/I^(n+1) → Spec A` for the thickening. Let `T` be the pullback of
  `p` along `q`, with projections `r : T → Spec A/I^(n+1)` and `t : T → S'`.
  The map `r` is flat, surjective and quasi-compact, being a base change of
  `p`. So `evaluate_injective_of_flat_surjective` reduces the claim to
  equality after evaluating along `r`. The level-`n` restriction of `f`,
  evaluated along `r`, is the constant family of `f` on `T`. This equals
  `evaluate t ((baseChange p).map f) = evaluate t fU`, by `evaluate_baseChange`
  twice and then `baseChange_hom`. Since `fU` algebraizes `s`, this is the
  evaluation of `s.hom n` along `r`.

## Provenance

The provenance is internal. The argument follows the finite étale descent step
in the proof of SGA 3, Exposé IX, Théorème 7.1. There, homomorphisms over a
finite étale cover and its double overlap are compared with their formal
counterparts, and the resulting equalizer rows give the conclusion. Here the
comparison over the cover and the overlap is expressed through
`System.IsAlgebraization`. Effective descent of homomorphisms is the Library's
`Descent.EtaleHomDescent`. The transport from finite test schemes to spectra of
finite algebras is elementary and original to this development.
