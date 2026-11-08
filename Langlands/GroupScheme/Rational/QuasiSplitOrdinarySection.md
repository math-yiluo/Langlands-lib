# Descended Steinberg sections for orthogonal simple-root orbits

This module is an internal prerequisite for the quasi-split Steinberg quotient
task. It formalizes the descent step in the proof of Steinberg's Theorem 9.4
and Corollary 9.5 (R. Steinberg, *Regular elements of semi-simple algebraic
groups*, Publ. Math. IHÉS 25 (1965), §9). The split Steinberg product is taken
in Galois-orbit order, and the simple roots of each orbit are assumed mutually
orthogonal. Then its image descends to a closed subscheme of the group over the
ground field. Composed with the canonical class quotient map, this subscheme
gives a section over the ground field, so every rational point of the quotient
lifts to a rational point of the group.

Steinberg obtains orthogonality by excluding simple components of type `A_n`
with `n` even. Here orthogonality is an explicit hypothesis,
`OrthogonalSimpleOrbits`. When it fails, the orbit dichotomy of
`Rational/QuasiSplitPinningOrbitPairs` gives a
Galois element that swaps an `A₂` pair of simple roots. In that case the module
asserts no rational section; compare Steinberg's Remark 9.6. Steinberg
assumes `k` perfect and works over an algebraic closure. Here the descent is
along a finite Galois splitting field, by fpqc descent, and needs no
perfectness.

Throughout, `k` and `K` are arbitrary fields in one universe `u` with an
algebra `k → K`. `G/k` is a group scheme with affine structure morphism, and
`G_K` is its base change along `algebraBaseMap k K`. No perfectness,
characteristic or infinitude assumption is made.

## Descent of closed immersions

The namespace `DescendedClosedImmersion` contains general facts about schemes.
Let `p : X ⟶ Y`, let `J` be an ideal sheaf on `Y`, and let `m : Z ⟶ X` satisfy
`m.ker = J.comap p` (`h`).

- `lift p J m h : Z ⟶ J.subscheme` is the factorization of `m ≫ p` through
  the closed subscheme of `J`. It exists because `J ≤ (m ≫ p).ker` follows
  from `h` by the published `ideal_comap_le_ker_iff`.
- `lift_subschemeι` states `lift p J m h ≫ J.subschemeι = m ≫ p`.
- `isPullback` assumes that `m` is a closed immersion. It states that the
  square with sides `m`, `lift p J m h`, `p` and `J.subschemeι` is a pullback.
  The proof is Mathlib's `isPullback_of_isClosedImmersion`, whose kernel
  condition is `h`.

For schemes over bases, let `b : S' ⟶ S`, `X : Over S`, and let `J` be an ideal
sheaf on `X.left`.

- `subOver X J` is the closed subscheme `J.subscheme` over `S`, with structure
  map `J.subschemeι ≫ X.hom`. `subOverι X J : subOver X J ⟶ X` is its
  inclusion.
- Let `m : Z ⟶ (Over.pullback b).obj X` have a closed immersion as underlying
  morphism, and suppose `m.left.ker = J.comap (pullback.fst X.hom b)` (`h`).
  `isPullback_pasted` pastes the square of `isPullback` with the defining
  pullback square of `(Over.pullback b).obj X`. It shows that `Z` is the
  pullback of `subOver X J` along `b`.
- `overIso b m h : Z ≅ (Over.pullback b).obj (subOver X J)` is the resulting
  isomorphism in `Over S'`. `overIso_hom_comp` states
  `(overIso b m h).hom ≫ (Over.pullback b).map (subOverι X J) = m`.
- `pullback_map_subOverι` restates this as
  `(Over.pullback b).map (subOverι X J) = (overIso b m h).inv ≫ m`.

## The descended section

Let `D : GaloisCompatiblePinningData k K G`.

- `D.orbitProduct` abbreviates the published canonical Steinberg product
  `SplitPinning.steinbergProduct` of `D.pinning`. Its simple-root ordering is
  `simpleOrbitOrdering D.action`, which places each Galois orbit in one
  contiguous block. Its root maps are `D.rootMaps`, and its reflection
  representatives are `canonicalSimpleReflectionRepresentatives D.rootMaps`.
- `orbitProduct_isClosedImmersion` assumes `IsSemisimple G`. It states that
  the underlying morphism of `D.orbitProduct` is a closed immersion. The proof
  applies the proved `splitSteinbergImmersion` to the split pinning of `G_K`.
  Semisimplicity of `G_K` is the proved `isSemisimpleFieldExtension`.

The remaining declarations assume `K/k` Galois and
`horth : D.pinning.OrthogonalSimpleOrbits D.action`. By the published
definition, this says that any two distinct simple roots in one orbit of
`D.action` are orthogonal.

- `sectionScheme D horth : Over (Spec k)` is `subOver G.X I`, where `I` is
  the ideal of `D.definingIdealDescent horth`. That descent datum, from
  `Rational/QuasiSplitCompatiblePinning`,
  writes the kernel of `D.orbitProduct` as the pullback of `I` along
  `pullback.fst G.X.hom (algebraBaseMap k K)`.
- `sectionι D horth : sectionScheme D horth ⟶ G.X` is `subOverι G.X I`;
  `sectionι_eq` records this definition.
- `quotientComposite_sectionι` states, by definition, that the published
  `ClassFunctions.BaseChange.quotientComposite k K G (sectionι D horth)` is the
  base change of `sectionι D horth` followed by `ClassFunctions.rho G_K`.
- `isIso_sectionι_rho` assumes that `D.orbitProduct` is a closed immersion
  (`himm`) and that `D.orbitProduct ≫ ClassFunctions.rho G_K` is an
  isomorphism (`hq`). It concludes
  `IsIso (sectionι D horth ≫ ClassFunctions.rho G)`. The published
  `ClassFunctions.BaseChange.isIso_quotientComposite_iff` reduces this to the
  base-changed composite. By `pullback_map_subOverι`, the base change of
  `sectionι D horth` is an isomorphism followed by `D.orbitProduct`, so `hq`
  applies.
- `exists_rationalLift` has the hypotheses of `isIso_sectionι_rho`. For every
  `v : 𝟙_ (Over (Spec k)) ⟶ ClassFunctions.quotient G` it gives
  `x : 𝟙_ (Over (Spec k)) ⟶ G.X` with `x ≫ ClassFunctions.rho G = v`. The
  witness is `v`, followed by the inverse of `sectionι D horth ≫ rho G`, then
  by `sectionι D horth`.
- `exists_rationalLift_of_isSimplyConnected` replaces `himm` and `hq` by three
  premises: `SplitSteinbergQuotientStatement`, `IsSimplyConnected G` and
  `IsSimplyConnected G_K`. Simple connectedness of `G` gives semisimplicity,
  hence `himm` by `orbitProduct_isClosedImmersion`. The split statement,
  applied to `G_K`, its pinning and the orbit ordering, gives `hq`.

## Pairing-compatible data and quasi-split groups

`PairingCompatiblePinningData.rationalLift_or_exists_pair` takes
`D : PairingCompatiblePinningData k K G` with `K/k` Galois. It assumes
`SplitSteinbergQuotientStatement`, `IsSimplyConnectedFieldExtensionStatement`
and `IsSimplyConnected G`. It concludes one of two alternatives:

- `D.pinning.OrthogonalSimpleOrbits D.action`, and every `k`-point of
  `ClassFunctions.quotient G` is `x ≫ ClassFunctions.rho G` for some `k`-point
  `x` of `G`;
- there are `σ` and a simple root `a` with `D.action σ a ≠ a`, both pairings
  of `a` and `D.action σ a` equal to `-1`, and
  `D.action σ (D.action σ a) = a`.

The proof applies the orbit dichotomy
`orthogonalSimpleOrbits_or_exists_pair` of `Rational/QuasiSplitPinningOrbitPairs`. In the orthogonal case it applies
`exists_rationalLift_of_isSimplyConnected`, where simple connectedness of
`G_K` comes from the field-extension statement.

`IsQuasiSplit.exists_pairingCompatiblePinningData_rationalLift_or_exists_pair`
assumes `ParabolicDynamicStatement`, `RootDatumExistenceStatement`,
`SplitSteinbergQuotientStatement`,
`IsSimplyConnectedFieldExtensionStatement`, `IsSimplyConnected G` and
`IsQuasiSplit G`. It gives a finite Galois extension `K/k` and
`D : PairingCompatiblePinningData k K G` satisfying the conclusion of
`rationalLift_or_exists_pair`. The data comes from
`IsQuasiSplit.exists_pairingCompatiblePinningData` of
`Rational/QuasiSplitPinningOrbitPairs`.

The four named statements are explicit premises and are not proved here.

## Scope

The module does not decide which alternative holds for a given group. It does
not construct Steinberg's substitutes `N''` and `N'''` for swapped `A₂` pairs
(Steinberg 9.7 and 9.11), and it asserts no rational section in that case. It
does not prove the fibre properties of the canonical quotient. All
declarations use only the standard axioms.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
