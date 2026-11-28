# Finite twist-orbit interpolation at a compact open level

`TwistedLeviFiniteOrbitCornerStatement` uses the setting of
`TwistedLeviDiscretePaleyWienerStatement`. The base field `F : Type u` is a
nonarchimedean local field of characteristic zero and the cyclic extension
`E : Type v` carries its `F`-module topology. The Levi products have the
Hausdorff, locally compact and totally disconnected topology and its Borel
σ-algebra. On the Levi product `M = B.Levi E`, the measure `μ` is an arbitrary
Haar measure and `θ = leviAut σ B` acts entrywise. The complex representation
carriers lie in `Type z`, independent of `u` and `v`.

Fix a compact open subgroup `K` of `M` with `θ⁻¹(K) ⊆ K`. Let `s` be a
finite set of irreducible admissible representations, each with a nonzero
`K`-fixed space and an isomorphism to its pullback by `θ`. Given a complex
linear functional `Φ` on `Distribution M` satisfying
`IsLeviSigmaInducedRegularFunctional σ B μ Φ`, the proposition asserts the
existence of a single Schwartz–Bruhat function `f` in
`Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup`. For every
irreducible admissible `π` isomorphic to an unramified twist of a member of
`s` by a `θ`-invariant character, and every isomorphism `A : π ≅ π ∘ θ`,
the twisted trace of `f` for `(π, A)` equals `Φ` applied to that pair's
twisted distribution. Unramified characters are trivial on `K`, so the
twists retain the nonzero fixed space. For a pair with zero `K`-fixed
space, the trace of any `f` from this corner is zero because its integrated
action has image in the `K`-fixed space.

## Provenance

Bernstein–Deligne–Kazhdan §4.2 interpolate on a finite union of
unramified twist orbits using the finite fibers over the character
group of a central lattice. Rogawski invokes that argument for
invariant unramified twists in the proof of Proposition 11.2.
In the fixed-level form, `exists_twistedDistribution_corner_values`
supplies interpolation for the inequivalent representations in each
finite fiber at the given `K`. The determinant-order lattice gives
the degrees for extracting coefficients as in
`Langlands.BaseChange.TwistedCharacter.FiniteTwistInterpolation`.
Multiplication by lattice characters and restriction to a determinant
degree preserve bi-invariance because `K` has degree zero. Central
translations also preserve the corner. Linearity in the intertwiner
and the one-dimensional intertwining line extend an identity for one
isomorphism to every isomorphism on the same representation.

## Sources

- J. Bernstein, P. Deligne and D. Kazhdan, *Trace Paley-Wiener theorem for
  reductive p-adic groups*, J. Analyse Math. 47 (1986), 180–192. §4.2,
  printed pp. 184–185 (PDF pp. 5–6). Literature ID
  `bernstein-deligne-kazhdan-1986-trace-paley-wiener`, SHA-256
  `2f422d01982c19c65541cb15297694b573ec517220fe7ecd3c0ec180c8c1e472`.
- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229. §11, condition (II) and the proof
  of Proposition 11.2, printed pp. 228–229 (PDF pp. 14–15). Literature ID
  `rogawski-1988-twisted-trace-paley-wiener`, SHA-256
  `86fbe930fc1db80a3a0f279db5d83af85b7e37dc7e041d813ebc9f5fdcb7c274`.
