# Open-subgroup Hecke preliminaries

These are internal constructions and proved helper lemmas for Renard,
*Représentations des groupes réductifs p-adiques* (2026), III.2.6, final Remark,
printed p.77 / PDF p.83. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The general Haar normalization below is an internal extension of the source's
restricted-measure inclusion, needed for the functor comparison with arbitrary
choices of Haar measure.

For an open subgroup \(H\) of the Hausdorff locally compact nonarchimedean group
\(G\), equipped with its induced topology and a locally compact instance, the
module proves that the two modular characters agree on \(H\). It follows that
both published relative modular characters are identically one.

The modular-character proof compares regular Haar measure on \(G\) with its
comap to \(H\). Both right-pushforward identities are evaluated on the same
compact open subgroup contained in \(H\). Its positive finite Haar mass cancels.
The relative-character lemmas then use the definitions and the character inverse
identities.

For arbitrary left Haar measures \(\mu_G,\mu_H\), put
\(\nu=\mu_G.\mathrm{comap}(H\hookrightarrow G)\) and
\[
 c=\operatorname{haarScalarFactor}(\mu_H,\nu)\in\mathbf C.
\]
`openDensity` is this positive real scalar viewed in \(\mathbf C\).
`openHeckeLinear` sends \(a\) to \(c\) times its extension by zero.
`openHeckeInclusion` packages this map as a nonunital ring homomorphism between
the actual Haar Hecke algebras. Its pointwise values are \(c\,a(h)\) on \(H\)
and zero outside \(H\).

`integral_haar_complex` derives the continuous compact-support Haar uniqueness
formula from its real version by taking real and imaginary parts. Thus the
construction requires no regularity assumption on the supplied measures.
`zeroExtension_mul_apply` uses the subtype comap integration formula and the
vanishing of zero extension outside \(H\). Together these formulas prove
`open_leftModule_eq`: the published left action is multiplication by
`openHeckeLinear a`. The multiplicativity proof evaluates this action on the
extension of a second test function, separately on and outside \(H\).

The scalar is nonzero. Restriction to the closed subspace \(H\), followed by
division by \(c\), gives a preimage of every test function vanishing outside
\(H\); this is `openHeckeLinear_surj_supported`. Haar-weighted inversion commutes
with this extension because the modular characters agree. The published
definition of the right action and the convolution-reversing property of Haar
inversion then give `open_rightModule_eq`.

Finally, if \(\mu_H(s)=\mu_G(\operatorname{Subtype.val}(s))\) for every subset
\(s\) of \(H\), the measures \(\mu_H\) and \(\nu\) coincide. The Haar scalar of a
measure with itself is one, proving `openDensity_eq_one`. In this case the map
is ordinary extension by zero. These helpers do not yet assert the natural
isomorphism between the pseudo-forgetful and forgetful functors.
