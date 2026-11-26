# Arithmetic of absolute upper ramification

`Langlands.Ramification.Local.absoluteHerbrandArithmetic` proves
[`AbsoluteHerbrandArithmetic`](LocalAbsoluteStatement.md) for every
nonarchimedean local field `K` of either characteristic and every separable
closure `Ω` of `K`, with independent universe parameters.

The proof introduces `K`, `Ω`, and their instances, then uses the anonymous
constructor for the conjunction with these five proofs in order.

1. `Wintenberger.localAbsoluteUpperFiniteImage K Ω` gives the exact image of
   each upper group at `v ≥ -1` in every finite Galois quotient.
2. `absoluteUpperInertia K Ω` identifies the absolute upper group at `0`
   with the kernel of the residue action.
3. `absoluteUpperLeftContinuity K Ω` expresses each absolute upper group at
   `v > -1` as the intersection of the groups indexed by `-1 ≤ w < v`.
4. `absoluteUpperClosedRightImage K Ω` identifies the image of the Krull
   closure of the supremum over `w > v` with the corresponding finite
   supremum, for `v ≥ -1`.
5. `absoluteUpperWildInertia K Ω` identifies wild inertia with the
   intersection of the restriction preimages of the first lower groups.

The components use the inertia and upper-numbering conventions in
Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV §1, Proposition 1, p. 62, and §3, pp. 73–75,
including Proposition 14 and Remark 1. Section 2, Proposition 7 and
Corollaries 1–4, pp. 67–68, describes the finite first lower group.
The registered source is `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
