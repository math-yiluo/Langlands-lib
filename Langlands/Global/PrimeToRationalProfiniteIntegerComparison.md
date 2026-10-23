# Normalized prime-to-modulus residue and finite-adele comparison

Author: Worker 142.

This module states the missing comparison between the published away residue
scalar ring and the published finite adeles away from a natural modulus. It
also states compatibility with restriction from the full scalar rings. Both
declarations return `Prop`; the module proves neither declaration and supplies
no unconditional comparison map.

## Objects and hypotheses

`PrimeToRationalProfiniteIntegerAdeleComparison h m` takes a natural number
`m` and an explicit proof
`h : Langlands.Global.RationalProfiniteIntegerAdeleComparison`. The full
comparison remains a separate mathematical obligation.

The full comparison proposition existentially supplies a topological ring
equivalence from `ProfiniteIntegerRing` to `integralFiniteAdeles ℚ`, normalized
on integers, followed by a compatible rational algebra equivalence. Inside the
new proposition, `eFull₀ := h.choose` and
`eFull := h.choose_spec.2.2.2.choose` are those coupled witnesses. These are
definitionally the choices named `integralEquiv h` and `rationalEquiv h` in
`Langlands.AbelianScheme.Tate.RationalScalars`. The statement imports only the
scalar modules, so it can be used without importing Tate modules.

The source `PrimeToProfiniteIntegerRing m` is the actual inverse limit of
`ZMod n` over positive integers coprime to `m`, with all divisibility reduction
maps. Its topology is the subspace topology of the product of the finite
discrete residue rings. `PrimeToProfiniteIntegerRing.intCastHom m` maps an
integer to its residue family, and `PrimeToProfiniteIntegerRing.restrict m`
forgets the full family's coordinates at orders not coprime to `m`.

The target `PrimeToFiniteAdeles m` is the existing restricted product of the
actual completions of `ℚ`, indexed by finite places whose prime ideal does not
contain the image of `m`. Integrality is relative to the completed integer
rings. `primeToIntegralFiniteAdeles m` is its everywhere-integral subring with
the inherited subspace topology. All topology here is the existing topology;
the ambient adele ring retains the restricted-product topology.
`primeToIntegralRestriction m` and `primeToFiniteRestriction m` are the
published restrictions from the full integral and finite adeles.

For prime `m = p`, these are the prime-to-`p` rings. For positive composite `m`,
they omit the primes dividing `m`. The statement also includes `m = 1` (all
orders and all finite places) and `m = 0` (only residue order one and no finite
places). In the latter case the away rings are trivial. No primality,
nontriviality, or characteristic assumption is silently imposed.

## Required witnesses and equations

For each `h` and `m`, the proposition requires:

1. A ring equivalence
   `e₀ : PrimeToProfiniteIntegerRing m ≃+* primeToIntegralFiniteAdeles m`
   continuous in both directions.
2. Integer normalization: the underlying adele of
   `e₀ (PrimeToProfiniteIntegerRing.intCastHom m z)` is the diagonal image of
   `(z : ℚ)` for every integer `z`.
3. Integral restriction compatibility, for every full residue family `a`:
   `e₀ (PrimeToProfiniteIntegerRing.restrict m a) =
   primeToIntegralRestriction m (eFull₀ a)`.
4. A `ℚ`-algebra equivalence
   `e : (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) ≃ₐ[ℚ] PrimeToFiniteAdeles m`.
   For every rational `q` and away residue family `a`, it must satisfy
   `e (q ⊗ a) = algebraMap ℚ (PrimeToFiniteAdeles m) q * (e₀ a)`.
5. Rational restriction compatibility on every pure tensor of the full
   rationalized residue ring:
   `e (q ⊗ PrimeToProfiniteIntegerRing.restrict m a) =
   primeToFiniteRestriction m (eFull (q ⊗ a))`.

The last equation is deliberately included although it follows from the
integral restriction equation, the two pure-tensor formulas, and preservation
of multiplication and rational scalars by restriction. Stating it makes the
required coupling explicit. Pure tensors generate the algebraic tensor
product, so this describes the restriction square for the rationalized map.
The Lean proposition asks for the displayed pointwise equation on pure tensors;
it does not introduce or separately prove a bundled tensor-restriction map.

`PrimeToRationalProfiniteIntegerAdeleComparisons` universally quantifies the
preceding proposition over `h` and `m`. It does not assert the full comparison's
truth. To obtain away comparison witnesses, a consumer must supply both this
proposition's proof and the full comparison proof. No topology is asserted on
either algebraic tensor product, and no rational continuity claim is made.

## Provenance and scope

This is a derived comparison obligation between already constructed scalar
rings. The intended mathematical route is the Chinese remainder description of
compatible residues as products of local integer rings, with the corresponding
place identifications, followed by clearing the finitely many denominator
primes in a restricted adele. The integer normalization fixes the continuous
integral comparison on the dense integer residue families, so the away maps
must be compatible with the full normalized witnesses. This explains the
formulation; none of this route is proved in the submitted module. It belongs
to a separate exact-target proof task after publication.

The motivation is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26), which
defines the away Tate module and its rationalization over `ℤ`, and Chapter III,
printed p.92 (PDF p.100), which uses the prime-to-`p` finite-adelic scalars in
the modified level structures. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Those passages were read directly. The normalized two-model comparison and
its extension to every natural modulus are internal formulations, not results
quoted verbatim from the source.

The actual adele model is imported from `Langlands.Global.PrimeToFiniteAdeles`;
this module creates no replacement adele ring or natural-prime-indexed model.
It concerns scalar rings only. Tate-module restricted products, scalar
actions, finite étaleness, ranks, geometric monodromy, Weil pairings, and PEL
level structures remain separate constructions.
