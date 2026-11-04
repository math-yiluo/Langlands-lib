# The semidirect product `U ⋊ S` as an fppf-local product inside its ambient group

Worker 1405 wrote this module. It is the product half of the split solvable envelope
`S ⋉ R_us,k(P)` at the start of the proof of Theorem C.2.5 in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), printed p. 595 (PDF p. 621, registered source
`conrad-gabber-prasad-2015-pseudo-reductive`). The other half, split solvability of the
semidirect product, is in `Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeSeries`.
The two halves are assembled in
`Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProof`.

## Setting

All results are in namespace `Langlands.GroupScheme.SplitSolvableEnvelope` over `Spec k` for a
field `k`. They take:

* a group scheme `P`;
* a commutative group scheme `S` with a homomorphism `s : S.toGrp ⟶ P`;
* a group scheme `U` with a homomorphism `j : U ⟶ P` such that `j.hom.hom` is a monomorphism;
* `hn : (range j).IsNormalizedBy (range s)`.

The Library's `AutomorphicAction.ofNormalizedConjugation j s hn` is the conjugation action of `S`
on `U`. Its semidirect product has underlying scheme `U.X ⊗ S.X`. The Library's
`SubgroupFunctor.normalizedProductHom j s hn` is the homomorphism from this semidirect product
to `P` given by `(u, t) ↦ j(u) s(t)` (`normalizedProductHom_hom`).

## Reordering

* `reorder : S.X ⊗ U.X ⟶ U.X ⊗ S.X` is `(t, u) ↦ (t u t⁻¹, t)`, where the first coordinate is the
  action morphism. `reorderInv` is `(u, t) ↦ (t, t⁻¹ u t)`.
* `reorder_reorderInv`, `reorderInv_reorder`: these are mutually inverse. The proofs use the
  Library's action identities `act_inv_act` and `act_act_inv`. Hence `isIso_reorder`, and
  `isIso_reorder_left` for the underlying morphism of schemes.
* `reorder_mul`: after `reorder`, the map `(u, t) ↦ j(u) s(t)` becomes `(t, u) ↦ s(t) j(u)`.
  This is `lift_comp_normalizedConjugation_comp`, which says `j(t u t⁻¹) = s(t) j(u) s(t)⁻¹`.
* `reorder_normalizedProductHom`: the same identity with `normalizedProductHom j s hn` in
  place of the product map.

## Closedness and the fppf product

The remaining results assume `S` and `U` are affine.

* `mono_normalizedProductHom`: assume `s.hom.hom` is a monomorphism, `S` is a split torus,
  `U` is unipotent and `j` is a closed subgroup. Then `normalizedProductHom j s hn` is a
  monomorphism. Its kernel is trivial on every test scheme: if `j(u) s(t) = 1`, then
  `t ≫ s = u⁻¹ ≫ j`. So `t = 1` by `IsSplitTorus.eq_one_of_comp_eq_comp`
  (`Langlands.GroupScheme.Unipotent.SplitTorusSubgroupHom`). Then `u = 1` because `j` is
  monic. The Library's `semidirectPointsEquiv` identifies points of the semidirect product
  with pairs `(u, t)`. A homomorphism with trivial kernel on points is a monomorphism.

The last two results also assume that `S` and `U` are smooth, that `P` is affine and locally of
finite type, and that the semidirect product is connected.

* `isClosedSubgroup_normalizedProductHom`: under these hypotheses `normalizedProductHom j s hn`
  is a closed subgroup. The Library's `HomImage.exists_image` factors it as `fac ≫ inc`. Here
  `inc` is a closed subgroup and `fac` is flat, surjective, quasi-compact and locally of finite
  presentation, hence an effective epimorphism of schemes. `fac` is a monomorphism because the
  composite is. `RelativeRoot.isIso_of_effectiveEpi_factorization` makes `fac` an isomorphism.
  So the composite is a closed immersion. The semidirect product is smooth and affine by the
  Library's semidirect-product instances, which is what `HomImage.exists_image` requires.
* `isFppfProduct_normalizedProductHom`: under the same hypotheses `normalizedProductHom j s hn`
  satisfies `IsFppfProduct (range s) (range j)`. This applies the Library's
  `isFppfProduct_of_fppf_factorization` to the closed subgroup above and to `reorder`, which is an
  isomorphism and hence flat, surjective and locally of finite presentation.
  `reorder_normalizedProductHom` supplies the required ordered product identity.

## Assembly

* `exists_envelope_of_isSplitSolvable`: let `G` be a smooth affine group scheme over `k` and
  `i : P ⟶ G` a closed subgroup. Let `s` be a split subtorus of `P` (`IsSplitSubtorus s`) and
  `j` a split unipotent radical of `P` (`IsSplitUnipotentRadical j`). Assume `hA`: whenever `U` is
  smooth, affine and connected, every semidirect product `a.semidirectProduct` of `S` acting on
  `U` is split solvable. Then some split solvable group scheme `H` has a homomorphism
  `h : H ⟶ P` with `IsFppfProduct (range s) (range j) h`. The witness is
  `normalizedProductHom j s hn`. The normalizing hypothesis `hn` comes from normality of the
  radical (`hj.isNormal`). The hypotheses of the previous results are derived as follows:
  * `P` is affine and locally of finite type because `i` is a closed immersion and `G` is affine
    and smooth.
  * `U` is affine because `j` is a closed immersion into `P`. It is smooth and connected by `hj`.
  * `s` and `j` are monomorphisms because they are closed immersions.
  * `S` is smooth and affine because it is a split torus.
  * The semidirect product is connected by the `connectedSpace` field of `hA`.

  The hypothesis `hA` is discharged in
  `Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProof`.

## Provenance

CGP state that `S ⋉ R_us,k(P)` maps isomorphically onto a closed subgroup of `P` without spelling
out the argument. The steps above are the standard ones: the torus and the unipotent radical
meet trivially (Milne, *Algebraic Groups* (2017), Corollary 14.17, printed p. 284, registered
source `milne-2017-algebraic-groups`), and a homomorphism with trivial kernel from a smooth
connected group is a closed immersion.
