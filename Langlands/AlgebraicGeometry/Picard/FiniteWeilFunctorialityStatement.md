# Dual-homomorphism compatibility of the actual finite Weil pairing

`Langlands.AbelianScheme.RelativeFiniteWeilFunctorialityStatement`
is a proposition definition asserting the following equation of
scheme morphisms over a quasi-separated base `S`. Let `f : A → B`
be a homomorphism of actual abelian schemes, let `Aᵛ` and `Bᵛ` be
their constructed dual group schemes, and let `n` be positive.
Then

```text
A[n] ×_S Bᵛ[n]  -- id × fᵛ[n] -->  A[n] ×_S Aᵛ[n]
       |                                  |
   f[n] × id                            e_(A,n)
       |                                  |
       v                                  v
B[n] ×_S Bᵛ[n]  -------- e_(B,n) ------->  μ_n
```

commutes. Equivalently, for every test scheme `T/S`, every
`x : T → A[n]` and every `y : T → Bᵛ[n]`, the asserted equation is

```text
e_(B,n)(f[n](x), y) = e_(A,n)(x, fᵛ[n](y))
```

in `Hom_S(T, μ_n)`. The assertion is an equality in `Over S` and
therefore includes nonreduced test schemes. The homomorphism `f`
is arbitrary; no isogeny hypothesis is imposed.

The map `f[n]` is exactly `Langlands.GroupScheme.Tate.kernelLevelMap`
applied to the actual underlying group-scheme homomorphism
`Langlands.AbelianScheme.groupHom f`. The dual map is exactly
`dualCommGroupSchemeMapFromEvaluation ... f`, whose underlying
scheme morphism is `dualSchemeMap homPicardZeroPullback f hA hB`.
It classifies pullback of rigidified Picard-zero classes and goes
from `Bᵛ` to `Aᵛ`. Applying `kernelLevelMap` to its underlying
group-scheme homomorphism gives `fᵛ[n]`. In both cases, the
published `kernelLevelMap_ι` equation identifies the composite
with the kernel inclusion as the original map after the source
kernel inclusion. No torsion map or dual map is supplied as data.

The two pairings are the already constructed
`finiteWeilPairing` at `B` and at `A`, respectively. Their point
formula is the intrinsic Poincaré-derived evaluation `beta(y)(x)`
into the actual root-of-unity group scheme. The statement preserves
this argument order and normalization; it does not invert the
value or choose a root-of-unity trivialization.

## Inputs and scope

The quantifiers retain the seven explicit dual-constructor
propositions, the actual abelian schemes `A/S` and `B/S`, chosen
`HasDualScheme` witnesses at both endpoints, actual inverse
Poincaré line bundles `MA` and `MB`, and their tensor evaluation
isomorphisms. The same seven constructor propositions are used
at both endpoints. They concern tensor coherence and Picard-zero
pullback and do not assume the desired pairing compatibility.

No smoothness or properness witness for the dual schemes is needed
to formulate their constructed group-scheme maps and torsion.
The base is quasi-separated as required by the existing pairings.
There is no assumption that `n` is invertible on `S`: the equation
concerns actual scheme-theoretic kernels and `μ_n`. It makes no
finite-étaleness or rank assertion.

## Provenance and separate proof obligation

The motivating original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, registered
as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter XI, Proposition (11.21)(i), printed p.167 / PDF p.171,
states exactly this compatibility for a homomorphism of abelian
varieties over a field and positive `n`, on points valued in any
scheme over that field. Its proof identifies the character of the
dual image with the original character precomposed with the
torsion restriction of the primal homomorphism.

This candidate formulates a **relative extension target** for the
Library's actual constructions. The cited field proposition does
not itself establish this equation over a general base. A proof
must establish the corresponding relative compatibility of the
Poincaré-derived characters and identify the maps with these exact
kernel restrictions and this exact constructed dual map. Equality
only on geometric points would not prove the displayed morphism
equation on nonreduced schemes.

The file supplies the precise `Prop`-valued target, without a proof
or a new axiom. A separate proof task must prove this exact
declaration once it is published. This contribution asserts neither
Cartier duality nor perfectness, alternation, divisibility-transition
compatibility, an inverse-limit pairing, or a completed PEL level
structure.
