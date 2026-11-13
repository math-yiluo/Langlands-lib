# Fundamental-group inertia targets and torus comparisons

This module applies the actual inertia quotient construction to the algebraic
fundamental group of a connected reductive group. The original objects occur
in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Construction
11.3.1, Fact 11.3.5, Lemma 11.3.6 and §11.5, printed pp. 427–430 / PDF
pp. 458–461, source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 2024 corrections do not alter these passages.

The field tower is `k → K → E`, with `K/k` normal. `FundamentalInertia` is
`A = π₁(G)_I`, using the actual chosen maximal-torus quotient and its actual
Galois representation. Here `I` is the kernel of restriction from `Aut_k(E)`
to `Aut_k(K)`. `fundamentalInertiaProjection` is its linear quotient map, and
`fundamentalInertiaTorsion` is the full finite-order subgroup `A_tor`.

When `E/k` is also normal, `fundamentalGammaRepresentation` is the descended
action of the actual group `Aut_k(K)`, and `FundamentalInvariants` is its fixed
submodule `A^Γ`. `fundamentalInvariantTorsion` is the finite-order subgroup of
this fixed submodule: exactly `(A_tor)^Γ`, because the inclusion of the fixed
submodule into `A` preserves and reflects finite order. `Multiplicative` changes
notation only. These definitions retain the distinction between
`A^Γ/(A_tor)^Γ` and `(A/A_tor)^Γ`; the latter is not used.

`IsFundamentalInertiaMap` characterizes the descent of the actual induced map
on fundamental groups by its value on every quotient representative.
`fundamentalInertiaMap` selects a linear map with this law. Its definition does
not assume a proof of equivariance or existence; the unconditional companion
statement records these obligations.

For a torus `T`, `torusPresentationMap` composes actual geometric cocharacters
with the inclusion of the chosen maximal torus into `T`. The representative
law `IsTorusFundamentalComparison` characterizes `π₁(T) → X_*(T)`, and
`torusFundamentalComparison` selects that linear map. Connected reductivity
needed to choose the presentation is supplied by the published theorem for
tori. `IsTorusInertiaComparison` characterizes its further descent to
`π₁(T)_I → X_*(T)_I`, and `torusInertiaComparison` selects it. Both comparisons
are to the original torus and its original cocharacter action, with no supplied
lattice identification. Existence, uniqueness, bijectivity and equivariance
remain unconditional statement obligations.

The quotient and action wrappers reuse the previously defined integral
coinvariants. The representative characterizations and selected comparisons
are implementation details derived from Fact 11.3.5 and functoriality, rather
than separately numbered assertions in KP. No Kottwitz homomorphism or desired
kernel is input to this unit.
