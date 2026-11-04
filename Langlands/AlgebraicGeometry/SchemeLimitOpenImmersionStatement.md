# Open-immersion descent along an actual affine limit

`RelativeOpenImmersionDescent` is the affine-scheme-limit form of the
open-immersion clause of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2).
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The data consist of a small cofiltered diagram of affine schemes over an
affine scheme S, an actual limit cone with its universal-property witness,
and a compatible structure map from its point to S. Both model structure
maps a and b are locally of finite presentation, quasi-compact and
quasi-separated: these are Conrad's finite-presentation hypotheses.
The equation f ≫ b = a makes f a relative morphism. Its actual
`baseChangeMap` at the limit is an open immersion if and only if its
actual `baseChangeMap` at some stage is an open immersion.
All objects and the index share arbitrary universe u. Neither model is
required to be affine or separated, and no injectivity hypothesis is
imposed on transition maps.

The scheme-limit interface is a derived reformulation of the source's
filtered-ring interface. The proof descends the quasi-compact open image
of the limiting open immersion using `exists_preimage_eq`, factors its
inverse through a stage by local finite presentation, and descends the
two inverse identities. In the reverse direction open immersion is stable
under base change. The original ring-system specialization and the other
source-property clauses remain separate obligations. This file defines
only the proposition; its paired proof is submitted separately.
