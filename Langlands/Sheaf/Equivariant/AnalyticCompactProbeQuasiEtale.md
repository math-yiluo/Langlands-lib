# Twisted compact-probe quasi-étale sheaves

The underlying space is a localized analytic atlas over a complete
ultrametric normed field. For an analytic isomorphism of bases,
`QuasiEtaleSite.isCocontinuous_translate_compactProbe` proves cocontinuity
of the existing translation of site categories. To test a translated sieve
at a compact Hausdorff probe, translate the probe and choose the finite
jointly surjective family given by the covering hypothesis. Compose the
structure maps of that family's sources with the inverse base isomorphism.
The underlying sources and point maps are unchanged. The counit of
translation accounts for their membership in the pulled-back sieve.

`twistedCompactProbeQuasiEtaleTopology` uses these translations to apply the
existing `TwistedOver` construction. A twisted sieve covers when its
arrows of twist one cover for `compactProbeQuasiEtaleTopology`.
`CompactProbeQuasiEtaleGSheaf` is the full category of sheaves on this
site with discrete action on sections over the compact Hausdorff tests of
`compactLiftSystem`. It is defined for concrete coefficients. The universes
of the ground field, analytic spaces and acting group are independent.

This is a derived implementation of Berkovich, *Étale equivariant sheaves
on p-adic analytic spaces* (1995–1996), §1.2, printed p. 3, and §1.4,
p. 7 through Definition 1.4.1 on pp. 7–8. The covering prescription in §1.2 is based on the ordinary analytic site.
Definition 1.4.1 uses translated sections and the discrete action of open
subgroups on compact tests. Here the covering test is the Library's compact-probe rule. Comparison
with the source's chart-neighbourhood rule and the equivalence in Theorem
1.4.2 are separate propositions.
Literature ID `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The retained PDF *Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf*
has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
