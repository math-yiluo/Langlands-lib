# Actual opposite Jacquet spectra over all standard Levis

Worker 148. This internal construction forms the actual opposite-parabolic
Jacquet-exponent family used in the maximal-norm step of Renard VII.4.2(iii).
It fixes a connected reductive group, a maximal split torus and a generic
cocharacter. Labels are all subsets of the actual simple relative roots,
reusing `StandardJacquetFamily.Index`.

At each label `opposite` applies `oppositeLeviParabolic` to the original
canonical standard datum. `datum` packages its actual opposite parabolic,
geometric radical and multiplication isomorphism, keeping exactly the
original standard Levi scheme. `datum_M` records that scheme equality;
`datum_l_comp_p` proves that the ambient Levi map is the original canonical
`Standard.leviHom`. The point images of the standard and opposite
parabolics intersect in precisely that Levi point image, as recorded by
`intersection`. These facts use the published actual opposite construction,
which realizes the original parabolic and Levi by a cocharacter and takes
its inverse dynamic parabolic.

`component` reuses the same split component, its inclusion in the original
standard Levi and its map into the fixed maximal split torus already chosen
by `StandardJacquetFamily.component`. Thus the standard root-presentation
data can continue to use these original maps. No equality of the standard
and opposite Jacquet spectra is asserted.

`isIso_full_p` proves the full-label opposite inclusion is an isomorphism.
The original full standard parabolic is an isomorphism, and its rational
Levi is consequently an isomorphism as well. The opposite ambient Levi map
equals this original composite, so its all-test range is top. That range
lies in the range of the opposite parabolic inclusion; the latter is a
monomorphism, hence the full-range isomorphism theorem applies.

Over a nonarchimedean local field, `exponents` is the dependent sum of the
actual normalized Jacquet exponent sets for these opposite data and the
chosen split components. A label and a smooth character of its own split
component are retained in every element. The ambient rational-point
topology is canonical; local compactness and the nonarchimedean group
property are explicit hypotheses.

`nontrivial_full_jacquet` uses the full-label isomorphism and the published
actual full-parabolic Jacquet equivalence to transfer nontriviality of the
original representation. The actual-Levi and image-Levi Jacquet modules
have the same carrier. `finite_exponents` uses admissibility and finite
length together with finiteness of the actual label type and the published
finite tagged-spectrum theorem. `nonempty_exponents` uses admissibility
and full-label nontriviality; it does not require finite length.
`maximalExponent` and `norm_le_maximalExponent` apply the finite selector
to an arbitrary supplied map `positive` into a normed additive group.
The representation-carrier and normed-target universes are independent
of the field universe.

The provenance is internal composition of the published standard datum,
actual opposite construction, chosen standard split components,
full-parabolic Jacquet equivalence and finite actual-spectrum selector.
The original motivation is Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition, VII.1.1, printed pp.220–221 / PDF
pp.226–227, and VII.4.2(iii), printed pp.243–244 / PDF pp.249–250.
The latter uses the spectra of Jacquet modules for the opposites of the
standard parabolics. Standard parabolics and Levis are treated in V.3.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Real-character lifts and positive-part decompositions are still required
to instantiate the arbitrary supplied map `positive` as in the source.
This unit proves no cone comparison, temperedness, exhaustion or
Langlands classification.
