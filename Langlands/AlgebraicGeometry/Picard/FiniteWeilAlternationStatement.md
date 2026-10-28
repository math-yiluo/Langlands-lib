# Alternation of the actual finite pairing of a relative polarization

`Langlands.AbelianScheme.RelativeFiniteWeilAlternationStatement` is a
proposition definition asserting that the constructed finite pairing of
an actual relative polarization is trivial on the diagonal. For a
positive integer `n`, write `P = A[n]` for the actual multiplication
kernel. The asserted equation in `Over S` is

```text
P -- diagonal --> P ×_S P -- finiteWeilAlongHomPairing(lam,n) --> μ_n
 =
P ----------------------- constant identity -----------------> μ_n.
```

The diagonal is exactly `prod.lift (𝟙 P) (𝟙 P)`. The right hand side
is `1` in the group of morphisms from `P` to the existing commutative
group scheme `mu S n`. Thus it is the morphism constant at the identity
section, without a choice of roots of unity. Equivalently, for every
test scheme `T/S` and every `x : T → A[n]`, the assertion is

```text
e_n^lam(x,x) = e_n(x,lam[n](x)) = 1  in Hom_S(T, μ_n).
```

The existing `finiteWeilAlongHomPairing_points` formula identifies the
left side with this value. Conversely, testing the point equation on
`T = A[n]` and its identity point recovers the displayed morphism
equation. This formulation includes nonreduced test schemes.

## Actual polarization and pairing

The homomorphism `lam` has target the existing
`dualAbelianSchemeFromEvaluation` of `A`. The hypothesis is exactly
the published `IsPolarization` predicate. It requires an actual
finite, flat, surjective isogeny, and an ample Mumford presentation
on each geometric fibre after a possible extension of that fibre's
field. It does not assume a pairing or an alternation law.

The pairing is exactly `finiteWeilAlongHomPairing`. It first applies
the actual torsion restriction `finiteWeilAlongHomTorsionMap` of
`lam` to the second coordinate and then the constructed
`finiteWeilPairing`. Its intrinsic point value is the Poincaré-derived
character evaluation `beta(lam[n](y))(x)`. The statement preserves
that argument order and normalization.

The quantifiers retain a quasi-separated base scheme `S`, the actual
abelian scheme `A/S`, its chosen `HasDualScheme` witness, the actual
dual's smoothness, properness and geometrically connected fibres,
and an inverse Poincaré line bundle with its tensor evaluation
isomorphism. They also retain the seven tensor/Picard constructor
propositions needed by the pairing, and the two propositions
`MumfordBundlePicardZeroStatement` and
`PicardZeroUniversalBaseChangeStatement` needed by the polarization
predicate. These propositions have their published meanings; none
states the alternation equation.

Only positive `n` is included. There is no requirement that `n` be
invertible on `S`, no principal-polarization hypothesis, and no
assumed trivialization of the root-of-unity group scheme.
Alternation is the diagonal identity itself, including in
characteristic two.

## Provenance and relative proof obligation

The motivating original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, registered
as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter XI, Corollary (11.22), printed p.168 / PDF p.172, states
that for a polarization of an abelian variety over a field and
positive `n`, this pairing is alternating on points valued in
every scheme over that field. Its proof combines the isogeny
composition compatibility in (11.21)(ii) with the line-bundle
pairing comparison in (11.20), applied to a positive tensor power
of an ample line bundle after passage to an algebraic closure.

This proposition is an unproved **relative extension target** for
the Library's exact polarization and finite pairing. The cited
field corollary does not itself prove it over a general base.
A proof must establish the relative compatibility of the
Poincaré-derived pairing with the polarization's ample
presentations, including any required descent and rigidity
arguments, for these exact maps. Checking only geometric points
does not establish the equality of scheme morphisms.

The file introduces no proof or new axiom. A separate proof task
must prove this exact declaration after its publication.
This target asserts neither Cartier perfectness nor
nondegeneracy, transition compatibility, dual-homomorphism
functoriality, an inverse-limit pairing, or a completed PEL
level structure. In particular, it makes no assertion of
integral perfectness for arbitrary nonprincipal polarizations.
