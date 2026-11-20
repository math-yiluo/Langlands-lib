# Finite-place family of cuspidal isobaric sums

`Langlands.Global.CuspidalIsobaricFiniteFamilyStatement` concerns a finite
family of actual cuspidal realizations of general linear groups over a number
field `F`. The ranks of the inputs are `m i + 1`, with sum `r + 1`. Assume
compactness of the additive adele quotient and supply a spectral presentation
for each realization whose finite local components are irreducible and
admissible.

The conclusion gives a family `A v` of actual irreducible admissible smooth
complex representations of `GL_(r+1)(F_v)` and one finite set `S` of finite
places. At every finite place `v`, `A v` is an `IsIsobaricSum` of the
presentations' canonical p-adic objects and an `IsSubquotientOf` their
canonical normalized block induction in the supplied block order. For
`v ∉ S`, `A v` has a nonzero vector fixed by `GL_(r+1)(𝒪_v)`. The number
field and the local carriers are in universe `u`. The presentations use the
independent factor universe `uQ`.

## Provenance

This derived statement collects the local inputs to the global step of
Getz–Hahn's proof of Theorem 10.7.5. Pooling the input multisegments implements
their isobaric sum in (10.33). The local subquotient assertion in the supplied
block order uses Tadić's product result for the Langlands quotients, and
sphericity is measured on the actual objects by the integral subgroup.
The family and finite set can be supplied to the induced-constituent
automorphy theorem.

| Registered source | SHA-256 | Locator |
| --- | --- | --- |
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.33), p. 284 (PDF p. 296), Theorem 10.6.3, p. 285 (PDF p. 297), and proof of Theorem 10.7.5, p. 288 (PDF p. 300) |
| `tadic-1986-unitary` | `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683` | Proposition A.4(ii), p. 372 (PDF p. 39) |
