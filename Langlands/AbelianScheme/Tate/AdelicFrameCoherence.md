# Identity and composition coherence of actual adelic Tate frames

## Scope and provenance

This derived construction proves identity and binary composition coherence for
the ambient full and away frames used in the Harris–Taylor PEL problem. The
carrier conventions come from Harris–Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), printed p.18 (PDF p.26): actual torsion
inverse limits and their rationalizations, including restriction to orders
coprime to excluded primes before rationalization. Section III.1, printed
pp.91–92 (PDF pp.99–100), uses frames linear over the endomorphism algebra
tensored with the full or away finite adeles. The particular coherence
constructions here are derived infrastructure, not quoted assertions of those
pages.

The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Parameters

Fix an abelian scheme `A` over `S`, a rational algebra `D`, and an algebra map
`i : D →ₐ[ℚ] End0 A` into actual rational endomorphisms. The map need not be
injective for these constructions. Full frames are linear equivalences from an
arbitrary module `V` over `D ⊗[ℚ] Global.FiniteAdeles ℚ` to the actual rational
full Tate carrier at a field-valued point `s`. A common explicit comparison
witness `h : Global.RationalProfiniteIntegerAdeleComparison` determines the
constructed Tate module structures at all endpoints.

The away version takes a natural modulus `m`, the carrier `RationalAway`, an
arbitrary module `V` over `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, and a common
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`. Thus the
away scalar witness is coupled to `h`; neither existence nor independence of
these witnesses is proved here. For prime `m`, this is the prime-to-p version.
All points may be valued in arbitrary fields of the indicated universe;
algebraic closedness is unnecessary for these algebraic frame maps.

## Test-scheme isomorphisms

For `e : Over.mk s ≅ Over.mk t`, `adelicFrameTestIso` postcomposes frames by
`finiteAdeleAlgebraTestIso`. Its value on a vector is the original frame value
restricted along `e.inv`. The inverse uses restriction along `e.hom`.
`primeToAdelicFrameTestIso` has the same construction on the away carrier.

For both families, `_apply` and `_symm_apply` give these pointwise formulas.
`_refl` proves that the reflexive test isomorphism leaves a frame unchanged;
`_trans` proves that transport by `e.trans f` equals transport first by `e`, then
by `f`. Extensionality reduces these equations to the corresponding tensor-linear
Tate test-transport laws.

## Abelian-scheme comparison frames

`adelicFrameBaseChangeId` carries a frame for the identity pullback of `A`, with
the actually pulled-back endomorphism action, to a frame for `A` at the same
point. It postcomposes by `finiteAdeleAlgebraBaseChangeId`. Its `_apply` lemma
identifies its underlying map with `rationalMap` of the actual abelian-scheme
identity comparison homomorphism.

For `b : S' ⟶ S` and `c : S'' ⟶ S'`, `adelicFrameBaseChangeComp` carries frames
for direct pullback by `c ≫ b` to frames for successive pullback, first by `b`
and then by `c`. Both sides use the actual corresponding pullbacks of `i` and
the same point over `S''`. It postcomposes by the constructed
`finiteAdeleAlgebraBaseChangeComp`, whose endomorphism intertwining was proved
from actual rational-Hom naturality. The `_apply` and `_symm_apply` formulas
identify the forward and inverse frame values with `rationalMap` of the
homomorphism and inverse of `AbelianScheme.baseChangeCompIso b c A`.

`primeToAdelicFrameBaseChangeId` and `primeToAdelicFrameBaseChangeComp` give
exactly these constructions and formulas for away frames, using the existing
away tensor-linear comparisons.

## Identity and binary composition equations

`adelicFrameBaseChange_id` starts with a frame for the identity pullback at `s`.
It applies the existing pointed frame base-change map, producing a frame at
`s ≫ 𝟙 S`, then transports along `(Over.mapId S).app (Over.mk s)` to the test
scheme at `s`. The result equals `adelicFrameBaseChangeId` applied to the
original frame. This retains the canonical test-scheme isomorphism rather than
identifying its endpoints silently.

`adelicFrameBaseChange_base_comp` starts with a frame for the successive
pullback at `s : Spec Ω ⟶ S''`. Its two routes are:

1. Apply pointed frame base change by `c`, then by `b`. The resulting frame is
   at `(s ≫ c) ≫ b`.
2. Apply the inverse of `adelicFrameBaseChangeComp` to obtain a frame for direct
   pullback, apply pointed frame base change by `c ≫ b`, then transport along
   `(Over.mapComp c b).app (Over.mk s)` from the test scheme at `s ≫ (c ≫ b)`
   to the successively mapped test scheme.

The theorem states equality of these resulting frames. Each proof applies
linear-equivalence extensionality and the corresponding pointwise tensor-linear
Tate base-change coherence theorem to the original frame value. The away
lemmas `primeToAdelicFrameBaseChange_id` and
`primeToAdelicFrameBaseChange_base_comp` follow by the same argument.

These are ambient frame equations. They do not impose a Weil pairing or
geometric monodromy invariance, descend these equations to orbit classes, or
assert separate higher coherence laws. No rational topology or completed PEL
moduli functor is claimed.
