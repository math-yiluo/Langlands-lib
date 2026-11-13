# Reduction of reduced-norm-one presentations of inner type A to four inputs

This helper module, namespace `Langlands.GroupScheme.InnerTypeANormOneReduction`, proves
that four prerequisite propositions imply the target
`Langlands.GroupScheme.InnerTypeANormOneStatement`. All results are at universe
parameter `u`. The main theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Main theorem

`innerTypeANormOne_of_inputs` has hypotheses

- `h1 : SpecialLinearSimplyConnectedPinningStatement`: `SL_{n+1}` over any field has a
  split pinning whose coroots span the cocharacter lattice and whose simple pairings
  form the Cartan matrix of type `A_n`;
- `h2 : Langlands.LinearAlgebra.CorootSpanCartanEquivStatement`: two finite reduced
  root data with spanning coroots, and a bijection of their simple roots that preserves
  simple pairings, admit an isomorphism of root data extending the bijection;
- `h4 : SpecialLinearInnerFormNormOneStatement`: a group with a finite-Galois
  quasi-split inner-form presentation whose model is isomorphic to `SL_{n+1}` is
  isomorphic to the reduced-norm-one group of a central simple algebra of reduced
  degree `n + 1`;
- `h5 : StarActionFiniteStageStatement`: Galois pinning data over the separable closure
  can be realized over a finite Galois extension `L ⊆ K_s`, compatibly with the root
  datum, the base and the star actions;

and concludes `InnerTypeANormOneStatement`. It does not prove any of the four inputs.

## Helper lemmas

- The imported
  `Langlands.LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv`
  transports the spanning property of coroots along an equivalence of root data.
  The reduction uses this published declaration directly.
- `aut_eq_one_of_simple`: an automorphism of a root datum whose coroots span the
  coweight lattice, and which fixes every simple index of a base, is the identity. Its
  weight map preserves the pairing with each simple coroot
  (`RootPairing.Hom.weight_coweight_transpose_apply`). Since the simple coroots span,
  a weight is determined by these pairings
  (`RootDatumSimpleCorootEquiv.eq_of_pairing_simpleCoroot`). So the weight map is the
  identity, and an equivalence is determined by its weight map
  (`RootPairing.Equiv.weightHom_injective`).
- `finiteStage_starAction_eq_one`: let `d` be Galois pinning data over `K_s` whose star
  action fixes every simple vertex, and let `d'` over a finite Galois `L` with `ι`,
  `e`, `hbase`, `hcomp` be as in the conclusion of `h5`. If the coroots of `d'` span,
  then `d'.starAction σ = 1` for every `σ ∈ Aut_K(L)`. Make `K_s` an `L`-algebra through
  `ι` and lift `σ` to `τ = σ.liftNormal K_s`, so that `τ ∘ ι = ι ∘ σ`. By `hcomp`,
  `e` intertwines the star action of `σ` with that of `τ`, which fixes simple vertices.
  So the star action of `σ` fixes every simple index of `d'`. Then it is trivial by
  `aut_eq_one_of_simple`.
- A local instance `innerTypeABaseChangeAffine`: the base change of an affine group
  scheme along a field extension is affine (the pullback projection is affine).

## Proof of the main theorem

Let `K`, `G`, `d : TitsIndexData G`, `n` be given, with `G` simply connected and
absolutely almost simple, and `d.HasInnerTypeA n`. That gives a numbering
`eA : d.Vertex ≃ Fin n` with Cartan matrix `CartanMatrix.A n` and trivial absolute star
action on all vertices.

1. **Finite Galois stage.** Apply `h5` to the absolute pinning `d.pinning`. This gives
   a finite Galois `L/K`, `ι : L →ₐ[K] K_s`, Galois pinning data `d'` of `G` over `L`, and
   a base-preserving equivalence `e` of root data that intertwines star actions.
2. **Simple connectedness over `L`.** `isSimplyConnectedFieldExtension` gives that
   `G_L` is simply connected, and `splitSimplyConnectedCorootSpan` (applied to the split
   maximal torus of `d'`) gives that the coroots of `d'` span the cocharacter lattice.
3. **Trivial star action over `L`.** `finiteStage_starAction_eq_one` gives
   `d'.starAction σ = 1` for every `σ ∈ Aut_K(L)`.
4. **Split model.** `h1` gives a split pinning `p` of `SL_{n+1}` over `K` with spanning
   coroots and type-`A_n` numbering `e1`. Its base change `pL = p.baseChange (F := L)`
   has root datum equivalent to that of `p` (`baseChangeRootDatumEquiv`). So its coroots
   span (`corootSpan_eq_top_of_equiv`), and its simple roots correspond to those of `p`
   (`baseChangeSimpleEquiv`).
5. **Matching simple roots.** The bijection `e2` from the simple roots of `pL` to the
   simple roots of `d'` is the composite of `baseChangeSimpleEquiv⁻¹`, `e1`, `eA⁻¹` and
   the inverse of the restriction of `e` to simple roots. It preserves simple pairings.
   Pairings of `d'` equal those of `d` through `e` (`RootPairing.Hom.pairing`), and
   those equal `d.cartan`, hence `CartanMatrix.A n` through `eA`. That matrix is the
   matrix of `p` through `e1`, and the pairings of `p` equal those of `pL`.
6. **Root datum isomorphism.** `h2` applied to `pL`, `d'` and `e2` gives
   `f : RootPairing.Equiv pL.rootDatum d'.rootDatum` extending `e2`. Since `f` extends
   a bijection of simple roots, it maps the base support exactly onto the base support.
7. **Pinned isomorphism.** `pinnedIsomorphism` (isomorphism theorem for split pinned
   reductive groups) gives a pinned isomorphism `E : pL ≅ d'`. In particular
   `E.groupIso : SL_{n+1,L} ≅ G_L`.
8. **Inner form.** Choose an adjoint quotient `q` of `SL_{n+1}` over `K`
   (`adjointQuotientExistence`). The split group is quasi-split (`p.isQuasiSplit`), and
   so is its adjoint quotient (`adjointQuotientQuasiSplitStatement`).
   `TrivialStarInnerTwist.hasInnerDiscrepancy` (with step 3) shows that
   `LocalGroupIso.ofBaseChangeIso E.groupIso` has inner discrepancy. So
   `QuasiSplitInnerForm.ofInnerDiscrepancy` builds a quasi-split inner-form presentation
   of `G` whose model is `SL_{n+1}` itself.
9. **Conclusion.** `h4` applied to this presentation and the identity isomorphism of
   the model gives the required central simple algebra `A` of reduced degree `n + 1` and
   `G ≅ normOne K A`.

The hypotheses "positive rank" (`0 < n`) and absolute almost-simplicity are not used.

## Literature

The route follows the classical argument: a simply connected group of inner type `A_n`
is an inner form of the split group `SL_{n+1}` (Tits 1966, §2.3, printed p.39).
Milne 2017, §24.c (printed p.517) identifies the split special-linear model;
Corollary 23.53 (printed p.500) treats quasi-split inner forms, and §24.f,
Theorem 24.43 (printed p.524) gives the norm-one classification.
Inner forms of `SL_{n+1}` are the groups `SL_1(A)`
(Knus–Merkurjev–Rost–Tignol 1998, Theorem 26.9, printed p.366; Platonov–Rapinchuk 1994,
Proposition 2.17, printed p.87). The Lean proof follows this route through the four
inputs above.
