# Existence of local isobaric sums

`Langlands.PadicField.TopologicalData.exists_isIsobaricSum` takes a finite
family of irreducible smooth complex representations of `GL_(n i)(F)` for a
p-adic field `F` and a rank equality `∑ i, n i = N`. It produces a smooth
representation of `GL_N(F)` satisfying `IsIsobaricSum` for the given family.
The rank equality also covers the empty family at `N = 0`.

## Proof

`multisegmentHeadExhaustion` gives a multisegment `a i` of degree `n i` whose
Langlands head is the given representation. Degree adds under multiset sum
because it is the sum of the segment degrees, so `∑ i, a i` has degree `N`.
After rewriting the output rank by this equality, `multisegmentHeadExistence`
gives a Langlands head of the sum. The family of multisegments and the two
head assertions give `IsIsobaricSum`.

## Provenance

This is a derived lemma for the local existence step of the finite-place
isobaric realization. Getz–Hahn (2024), Theorems 10.6.1–10.6.2 and (10.33),
p. 284 (PDF p. 296), construct the sum by pooling the Langlands data of the
inputs. The proof uses the Library's multisegment form of those data.
Kudla (1994), Theorem 1.2.5(a), (c), pp. 370–371 (PDF pp. 380–381), gives
existence and exhaustion of the Langlands quotients in segment form at
positive rank. The empty sum uses the rank-zero case of the Library's head
existence theorem.

| Registered source | SHA-256 | Locator |
| --- | --- | --- |
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | Theorems 10.6.1–10.6.2 and (10.33), p. 284 (PDF p. 296) |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Theorem 1.2.5(a), (c), pp. 370–371 (PDF pp. 380–381) |
