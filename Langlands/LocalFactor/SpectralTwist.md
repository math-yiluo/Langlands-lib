# Spectral twists of continuous exact virtual representations

Worker 20 connects the published degree characters and nonzero spectral
parameter to actual finite representations and their exact virtual group.
This provides the spectral-shift operation required before evaluating an
explicit local-constant system. No such system is assumed or chosen here.

## Character and representation

The inputs are a group `G` with a topology, a supplied continuous degree
`d : G →ₜ* Weil.Degree`, a real number `q`, and a proof `0 < q`.
`Weil.Degree` is the existing discrete multiplicative copy of the integers.
The group and representation-carrier universes are independent.

`character d q hq s` is exactly

```
Weil.Local.unramifiedCharacter d (LocalFactor.spectralParameter q hq s).
```

Both component constructors are published. In particular, its value at `g` is
the complex unit with complex value

```
exp(-s * log(q)) ^ (d g).toAdd.
```

The integer power is the existing degree-character construction, including
negative degrees. `character_apply` proves this formula.
`character_on_kernel` proves triviality on the actual kernel of `d`.
`character_degree_one` proves that every supplied geometric degree-one element
has value `q^(-s)`, represented by the existing nonzero spectral parameter.
The sign agrees with norm value `q⁻¹` at geometric degree one.

`spectralParameter_zero` and `spectralParameter_add` follow from the complex
exponential identities. Pulling them through the published
`unramifiedCharacterHom` gives `character_zero` and `character_add`.

`representation d q hq s A` is the published scalar twist of `A` by this
character. `representation_isContinuous` applies the proved continuous-twist
closure from the accompanying `ExactTwist` module. It applies to all continuous
finite-dimensional complex representations, without semisimplicity or
irreducibility hypotheses.

## Exact virtual action

`ContinuousVirtual` abbreviates the existing `ExactGrothendieckGroup` with the
published `FiniteRepresentation.IsContinuous` predicate. It introduces no new
equivalence relation or virtual-representation model.

`virtual d q hq s` is the actual integer-linear automorphism supplied by
`ExactGrothendieckGroup.continuousTwist`. `virtual_ofRepresentation` computes its
value on the class of an actual continuous representation.
`virtual_preserves_degree` uses the proved unchanged-rank property.
`virtualDegreeZero` restricts that same linear map to the actual kernel of the
virtual degree map.

`virtual_zero` proves identity at zero spectral shift. `virtual_add` proves

```
virtual(s) ∘ virtual(t) = virtual(s + t).
```

Both equalities are equalities of linear maps on the actual quotient.
Generator extensionality reduces them to actual representations. The proofs
then use the character identities and the genuine identity/product twist
equivalences from `ExactTwist`. Thus these laws hold on all virtual classes,
including differences and negative integer combinations.

## Original source and scope

John Tate, *Number theoretic background*, Corvallis Part II (1979):

- Section 2 opening and section 2.2, printed pages 9–10 / PDF pages 18–19:
  the exact virtual group, continuous quasicharacters, and the norm characters
  `ωˢ` used to twist Weil representations.
- Section 3.3.2, printed page 14 / PDF page 23: geometric Frobenius and the
  spectral interpretation through `Vωˢ`.
- Section 3.4.5, printed page 15 / PDF page 24: spectral twisting in the
  measure-dependent local-constant formula.

Literature ID: `tate-1979-number-theoretic-background`.
Retained original:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The original pages were read directly. The formulas and quotient construction
above are a derived implementation of these operations; no local-factor
identity or analytic theorem from the cited pages is claimed.

This module deliberately takes the degree and positive `q` as inputs.
The arithmetic specialization must use the actual local Weil degree and
`q = #k_F`; this module neither constructs that group nor identifies an
arbitrary degree with it. The pending local Weil assembly remains a separate
dependency. For each complex parameter the character is continuous in `G`;
no topology on the exact virtual group or analytic dependence of its
automorphism group is asserted.

There is no evaluation of an L-factor, so no poles are discarded. This module
does not define epsilon, prove nonabelian-system existence, choose a self-dual
measure, or assert a conversion between Deligne and Langlands conventions.
It supplies the actual twist to be used by those subsequent definitions.
The accompanying `Langlands/VirtualRepresentation/ExactTwist` pair is included
in the same candidate; all other imports are published.
