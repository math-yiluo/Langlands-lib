# The local order of a cyclic norm-kernel character: proof

`Langlands.Global.HeckeCharacter.cyclicNormKernelUnramifiedOrder` proves
`CyclicNormKernelUnramifiedOrderStatement.{uF, uE}` for independent universes
`uF` and `uE`. Let \(E/F\) be a cyclic Galois extension of number fields, and let
\(\eta\) be a Hecke character of \(F\) whose kernel is the idele-class norm image
\(N_{E/F}C_E\) (`η.HasNormKernel E`). On one cofinite set of finite places \(v\) of
\(F\), the proof shows three things. The character \(\eta\) is unramified at \(v\).
Every place \(w\mid v\) of \(E\) has ramification index one. The order of
`η.finiteUniformizerValue v` equals the inertia degree `w.asIdeal.inertiaDeg (𝓞 F)`.

The proof first treats \(F\) and \(E\) in one universe through the relative Weil
transfer. It then reduces the general case to that one by replacing \(E\) with an
isomorphic copy in the universe of \(F\).

## Same universe: norms of uniformizer powers

`exists_pow_mem_range_ideleClassNorm_iff` assumes \(F\) and \(E\) share a universe
and \(E/F\) is cyclic Galois. It takes a finite place \(z\) of \(F\) and a place
\(w\mid z\) of \(E\) with ramification index one. It produces
\(a\in F_z^\times\) of valuation `WithZero.exp (-1)`, i.e. a uniformizer. Let
\([a]\) be its idele class (`IdeleClassGroup.ofAdicCompletion`). Then for every
\(k\in\mathbb N\),
\[
  [a]^k\in N_{E/F}C_E \iff f(w/z)\mid k .
\]
The proof proceeds in the following steps.

1. `localRelativeClassFormation` and `fundamentalClass_exists` give an
   arithmetically normalized family of global fundamental classes, hence the
   relative Weil group \(W_{E/F}\). Its transfer \(t\colon W_{E/F}\to C_F\),
   projection \(p\colon W_{E/F}\to\operatorname{Gal}(E/F)\) and inclusion
   \(\iota_C\colon C_E\to W_{E/F}\) are the Library maps
   `RelativeWeilGroup.transfer`, `projection` and `inclusion`.
   `RelativeWeilGroup.relativeWeilTransferReciprocity` identifies \(\ker t\) with
   the commutator subgroup. The projection lands in an abelian (cyclic) group,
   so `Abelianization.commutator_subset_ker` gives \(\ker t\le\ker p\).
2. `LocalClassField.geometricWeilReciprocityExistenceUniqueness` gives a
   reciprocity candidate for the completion \(E_w\). From it
   `localRelativeWeilMapExistence` produces a local relative Weil map
   \(\iota\colon W_{F_z}\to W_{E/F}\). On \(E\), the projection of \(\iota(g)\)
   acts through the closure embedding as the local projection of \(g\).
3. Let \(y\) be the local geometric Frobenius, which has degree one
   (`localGeometricFrobenius_degree`).
   `RelativeWeilGroup.exists_transfer_eq_inv_ofAdicCompletion` (which needs
   \(e(w/z)=1\)) gives the uniformizer \(a\) with \(t(\iota(y))=[a]^{-1}\).
4. *Norms are transfers of the kernel.* For \(s\in W_{E/F}\),
   \(t(s)\in N_{E/F}C_E\iff p(s)=1\). Suppose \(t(s)=N(b)\). By
   `RelativeWeilGroup.transfer_inclusion`, \(N(b)=t(\iota_C b)\). Then
   \(s\,(\iota_C b)^{-1}\in\ker t\le\ker p\), and
   \(\iota_C b\in\ker p\) by exactness (`RelativeWeilGroup.exact`), so \(p(s)=1\).
   Conversely, if \(p(s)=1\), exactness writes \(s=\iota_C b\), and then
   \(t(s)=N(b)\).
5. The norm image is closed under inverses. Therefore
   \([a]^k\in N_{E/F}C_E\iff t(\iota(y^k))=[a]^{-k}\in N_{E/F}C_E\). By step 4
   this holds iff \(p(\iota(y^k))=1\). The kernel of \(p\) is the range of
   \(\iota_C\) (`RelativeWeilGroup.ideleClassSubgroup` after exactness), so this
   says \(\iota(y^k)\) lies in the idele-class subgroup.
   `RelativeWeilGroup.mem_ideleClassSubgroup_iff` turns this into
   \(y^k\) lying in the range of the completion Weil map
   \(W_{E_w}\to W_{F_z}\).
   `RelativeWeilGroup.mem_completionWeilMap_range_iff` (again using
   \(e(w/z)=1\)) turns that into divisibility of \(\deg(y^k)=k\) by the local
   residue degree of \(E_w/F_z\).
   `extensionResidueDegree_completionPadicAlgHom` identifies that local degree
   with `w.asIdeal.inertiaDeg (𝓞 F)`.

## Same universe: the order

`orderOf_finiteUniformizerValue_of_sameUniverse` adds the hypotheses that
\(\eta\) has the norm kernel for \(E\) and is unramified at \(z\). Take \(a\) from
the previous lemma. By `HeckeCharacter.finiteComponent_eq_finiteUniformizerValue`,
\(\eta([a])\) is `η.finiteUniformizerValue z`. For each \(k\),
\[
  \eta([a])^k=1 \iff [a]^k\in\ker\eta=N_{E/F}C_E \iff f(w/z)\mid k .
\]
So `orderOf_dvd_of_pow_eq_one` and `pow_orderOf_eq_one` give divisibility in both
directions, and `Nat.dvd_antisymm` gives the equality. The exact kernel
hypothesis is what makes the order exact rather than a divisor of \(f(w/z)\).

## Independent universes: changing the extension field

`exists_algEquiv_baseUniverse` shows that a finite separable extension \(E/F\) is
\(F\)-isomorphic to a field \(E'\) in the universe of \(F\). A primitive element
\(\alpha\) gives \(E'=\) `AdjoinRoot (minpoly F α)`, with
\(E'\simeq F(\alpha)=E\) via `IntermediateField.adjoinRootEquivAdjoin`. Fix an
\(F\)-algebra isomorphism \(\varphi\colon E\simeq E'\). Then \(E'\) is a number
field (`NumberField.of_ringEquiv`). It is Galois over \(F\)
(`IsGalois.of_algEquiv`) and cyclic (via `AlgEquiv.autCongr φ`). This route
leaves \(F\), \(\eta\) and its finite components untouched, so no transport of
uniformizer values is needed. Two things are transported along \(\varphi\).

*The norm image.* `ideleClassNorm_ideleClassEquiv_algEquiv` shows
\(N_{E'/F}(\varphi_*y)=N_{E/F}(y)\) for \(y\in C_E\), where \(\varphi_*\) is
`ideleClassEquiv φ.toRingEquiv`. Inclusion \(C_F\to C_{E'}\) is injective
(`ideleClassGaloisDescent`). After inclusion, each norm is the product of the
Galois conjugates of its argument (`ideleClassNormGaloisProduct`). The proof uses
three facts:

- \(\varphi_*\) carries the inclusion \(C_F\to C_E\) to the inclusion
  \(C_F\to C_{E'}\) (`ideleClassEquiv_algEquiv_ideleClassInclusion`). At finite
  places this comes from compatibility of the completed transport with the
  completed embeddings of \(F_p\), proved by density of \(F\). At infinite places
  it comes from functoriality of `infiniteAdeleMap`.
- \(\varphi_*\) intertwines \(\sigma\) with \(\varphi\sigma\varphi^{-1}\)
  (`relativeIdeleClassAut_autCongr`).
- The product over \(\operatorname{Gal}(E/F)\) can be reindexed along
  `AlgEquiv.autCongr φ`.

Hence `range_ideleClassNorm_algEquiv` gives
\(N_{E'/F}C_{E'}=N_{E/F}C_E\), and \(\eta\) has the norm kernel for \(E'\) too.

*Inertia degrees.* For a place \(q\) of \(E\) over \(v\), let \(q'\) be the
corresponding place of \(E'\), the preimage of \(q\) under \(\varphi^{-1}\)
(`finitePlaceEquiv φ.symm.toRingEquiv q`). Then \(q'\) lies over
the same place \(v\) (`liesOver_finitePlaceEquiv_algEquiv`).
`inertiaDeg_finitePlaceEquiv_algEquiv` shows \(f(q'/v)=f(q/v)\), using
`Ideal.inertiaDeg_eq_of_isMaximal` and the \(\mathcal O_F/v\)-algebra isomorphism
of residue fields `Ideal.Quotient.algEquivOfEqComap` induced by
`RingOfIntegers.mapAlgEquiv`.

## The main theorem

`HeckeFunctionalEquation.exists_finset_isUnramifiedAt` gives a finite set \(S\)
outside which \(\eta\) is unramified. `eventually_ramificationIdx_eq_one`, applied
to \(E/F\) and \(E'/F\), gives cofinitely many \(v\) at which every place above
\(v\) in \(E\), respectively \(E'\), has ramification index one. On the
intersection of these three cofinite sets, the first two conclusions are
immediate. For \(w\mid v\) in \(E\), rewrite \(f(w/v)\) as \(f(w'/v)\) for the
corresponding place \(w'\) of \(E'\), which also has ramification index one. Then
apply the same-universe order lemma to
\(E'/F\), \(\eta\), \(v\) and \(w'\).

The theorem has level parameters `uF`, `uE` and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Sources

- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula* (1989), `arthur-clozel-1989-base-change`. In the proof of
  Chapter III, Theorem 3.1, printed p. 201 (PDF p. 215), \(\eta\) vanishes exactly
  on \(F^\times N(\mathbb A_E^\times)\). With \(S\) such that \(E/F\) is
  unramified outside \(S\), the value \(\zeta_v=\eta_v(\varpi_v)\) is a root of
  unity of order \(f_v\). In Chapter III, §6, printed p. 216 (PDF p. 230),
  the proof of Theorem 6.2 uses the inert case \(\eta(\varpi_v)=\zeta\), a
  primitive \(\ell\)th root of unity.
- J. Tate, *Number theoretic background*, Corvallis Part II (1979),
  `tate-1979-number-theoretic-background`. It gives the Weil-group facts behind
  the transfer computation. (1.2.2), printed p. 4 (PDF p. 13): transfer after
  inclusion \(C_E\to W_{E/F}\) is the norm. Printed p. 5 (PDF p. 14): the case
  \(n=-2\) of (1.2.3) gives \(\operatorname{Gal}(E/F)^{\mathrm{ab}}\simeq
  C_F/N_{E/F}C_E\). (1.4.1), printed p. 6 (PDF p. 15): uniformizers correspond
  to the inverse of Frobenius. The Lean proof uses the Library's relative Weil
  group and its proved transfer and local-map theorems rather than these
  statements directly.
