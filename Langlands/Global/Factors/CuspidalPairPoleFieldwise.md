# Completed cuspidal pair pole data over one number field

`Langlands.Global.CuspidalPairPoleAt.{u,uQ} F` is the body of the Library's
completed pair pole proposition over a fixed number field `F : Type u`. Its
existence, pole profile and vertical-strip bound clauses retain the
spectral factor universe `uQ`, the finite-place presentations, and the
archimedean parameter families. Applying the unrestricted statement to `F`
gives this body. Applying the totally complex statement to `F` also gives
this body when the corresponding instance is available.

This auxiliary proposition allows a fieldwise proof from either version of
Getz–Hahn 2024, Theorem 11.7.1, printed p. 309 (PDF p. 320). Its function is
to reuse the common hypotheses and conclusion of the two Library versions.
The module proves the two restrictions.
