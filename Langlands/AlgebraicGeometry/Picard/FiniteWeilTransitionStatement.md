# Divisibility compatibility of the actual finite Weil pairing

`Langlands.AbelianScheme.RelativeFiniteWeilTransitionStatement` is a
proposition definition asserting an equation of actual scheme morphisms.
For an abelian scheme `A/S`, its constructed dual group scheme `Aᵛ`,
and positive integers `n | m`, put `r = m / n`. The equation is

```text
A[m] ×_S Aᵛ[m]  -- e_m -->  μ_m
       |                       |
   ([r], [r])                ζ ↦ ζ^r
       |                       |
       v                       v
A[n] ×_S Aᵛ[n]  -- e_n -->  μ_n .
```

The square commutes. Equivalently, for every test scheme `T/S` and
points `x : T → A[m]`, `y : T → Aᵛ[m]`, the asserted equation is

```text
e_n([r]x, [r]y) = transition_mu(e_m(x,y))
```

in `Hom_S(T, μ_n)`. Under the existing `mu.pointsEquiv`, the right
side is the `r`-th power of the root of unity `e_m(x,y)`. It is not an
equality of elements of two different root groups without a specified
map between them.

Both maps on torsion are exactly
`Langlands.GroupScheme.Tate.kernelTransition`. Their existing
`kernelTransition_ι` equations identify their composites with the
kernel inclusions as multiplication by `r` on the respective group
schemes. Their effects on every test scheme agree with the existing
Tate-level transitions by `kernelLevelEquiv_transition`. The target
map is the existing `Langlands.GroupScheme.mu.transition`, whose
`pointsLevelEquiv_transition` equation identifies it with the actual
roots-of-unity transition `Langlands.TateTwist.transition`. No
transition map is supplied as data.

The horizontal morphisms are the existing `finiteWeilPairing`. Its
point formula is the intrinsic evaluation `beta(y)(x)` constructed
from the Poincaré representative and its kernel character. Thus this
statement constrains that particular pairing, including its argument
order and normalization. It introduces no arbitrary pairing or
character.

## Hypotheses and relative scope

The statement quantifies over a quasi-separated scheme `S`, an actual
abelian scheme `A/S`, its chosen `HasDualScheme` witness, the seven
explicit dual-constructor propositions, and an actual inverse
Poincaré line bundle `MA` with tensor evaluation isomorphism. These
are precisely the inputs needed by `finiteWeilPairing`. The dual
need only have the constructed commutative group-scheme structure;
no extra dual smoothness or properness witness is needed to state
this equation.

Both torsion orders are positive. No assumption that they are units
on `S` is made: the equation concerns scheme-theoretic multiplication
kernels and the root-of-unity group schemes, including in residue
characteristics dividing the orders. It does not assert finite
étaleness or a rank formula. Such assertions retain their separate
invertibility hypotheses.

## Provenance and proof obligation

The motivating source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter XI, Proposition (11.21)(ii), printed pp.167–168 / PDF
pp.171–172, gives compatibility of kernel pairings with composition
of isogenies. Applying its two identities to multiplication by `n`
and by `r`, using duality of multiplication and bilinearity, gives
the divisibility equation over a field. Section (11.23), printed
p.168 / PDF p.172, explicitly uses the prime-power instance

```text
e_(ℓ^a)(x_a, y_a) = e_(ℓ^(a+1))(x_(a+1), y_(a+1))^ℓ
```

to construct the Tate pairing into the roots-of-unity inverse limit.
The source's discussion there concerns an abelian variety over a
field and a prime different from its characteristic.

The present proposition is a **relative extension target** formulated
internally for the Library's actual constructions. It is not a
claim that the cited field result already proves the equation over
an arbitrary base. A proof of this exact declaration must establish
the necessary relative compatibility of the Poincaré-derived kernel
characters, or prove an appropriate relative composition theorem
and identify its maps with these exact constructions. A proof only
on geometric points does not suffice, since the displayed equality
also tests nonreduced schemes.

This file supplies the precise `Prop`-valued target, with no proof
and no new axiom. A separate proof task must establish this exact
published declaration. It states neither Cartier duality nor
perfectness, polarization alternation, dual-homomorphism
functoriality, or an inverse-limit pairing. Once proved or supplied
as an explicit theorem hypothesis, it provides the coherence
required to evaluate compatible torsion families into the existing
Tate twist without choosing roots of unity.
