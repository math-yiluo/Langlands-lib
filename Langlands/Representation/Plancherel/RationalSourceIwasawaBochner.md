# Actual Iwasawa weighted measure and Bochner integration

Author: Worker 200.

This is a derived extension of Waldspurger (2003), I.1, first formula (2),
printed p.240 / PDF p.6, DOI 10.1017/S1474748003000082,
registered as `waldspurger-2003-plancherel`. The original normalization
paragraph gives every closed subgroup Haar mass one on its intersection
with the chosen special compact. The source states its formula for
complex locally constant compactly supported functions. This module uses
the actual rational-point setting and original common-compact Haar
normalization of `RationalSourceIwasawaIntegration` and extends its
nonnegative formula to Bochner-integrable functions.

The group scheme is affine and locally of finite type over an arbitrary
nonarchimedean local field, with no characteristic, splitness or
quasisplitness restriction. A field-defined cocharacter gives the actual
parabolic P, Levi M and radical U. Topology is the canonical
`rationalPointTopology` and measurable structure is Borel. The target real
normed space has an independent universe.

`sourceIwasawaMap` sends `(u,(m,k))` to `u*m*k`.
`sourceIwasawaProductHaar` is the original `du*(dm*dk)`, where `dk` is the
probability Haar on the supplied compact open K. `sourceIwasawaDensity` is
the inverse actual radical-conjugation modulus at m. It is measurable and
finite. `sourceIwasawaMeasure` pushes forward the product weighted by that
density. The definition introduces no scaling coefficient or assumed
integration identity.

`lintegral_sourceIwasawaMeasure` follows by measurable map and density
integration and two applications of Tonelli. The inverse modulus is moved
outside the innermost compact integral. The comparison
`ambientHaar_eq_sourceIwasawaMeasure` follows by measure extensionality from
the nonnegative Iwasawa source-order formula. It retains two explicit
premises: actual P K factorization of every rational point, and stability
of P intersect K under `Dynamic.limitHom`. There is no gamma factor.
Neither connected reductivity nor ambient or Levi right invariance is an
additional premise of this comparison.

Every ambient-integrable function has an integrable weighted coordinate
pullback with respect to the original product measure. This follows from
the measure identity, measurable pullback and the finite-density
integrability criterion; no separate measurability or pointwise fiber
integrability is assumed. The product Bochner formula follows by map and
density integration. The iterated U,M,K formula follows by Fubini using the
proved product integrability and its almost-everywhere integrable
sections. The real inverse-modulus scalar moves outside the innermost
compact integral. These formulas use Mathlib's Bochner integral, defined
to be zero for an incomplete target. For Banach targets they are the usual
Bochner integral formulas.

The explicit factorization and compact-limit premises are not proved for
every reductive group here, and K has not been identified with the source's
special maximal compact. The source Iwasawa expression for gamma,
same-Levi independence, spectral normalizations and the main Plancherel
conclusions remain separate obligations.

This module uses ten distinct explicit local instance names with the
`sourceIwasawaBochner` prefix so that the Iwasawa and gamma branches can be
imported together. This internal naming correction leaves every instance
type and body, mathematical declaration, hypothesis and proof unchanged.
