# Identity and composition coherence on actual Tate frame right orbits

## Scope and provenance

This derived construction descends the actual full and away Tate frame
comparisons of `AdelicFrameCoherence` to unrestricted right-orbit classes. It
constructs test-isomorphism, identity-pullback and direct-to-successive-pullback
orbit equivalences, and proves their identity and binary composition equations.
The construction uses equivariance of postcomposition and quotient induction.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 (PDF p.26), supplies the full and away Tate-carrier and
rational-endomorphism conventions. Section III.1, printed pp.91–92 (PDF
pp.99–100), uses orbits of frames over the endomorphism algebra tensored with
full or away finite adeles. Page 91 specifies right precomposition. The
particular quotient comparison constructions and coherence formulas here are
derived infrastructure, rather than quoted assertions of those pages.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Parameters and orbit convention

Fix an abelian scheme `A/S`, a rational algebra `D`, and an algebra map
`i : D →ₐ[ℚ] End0 A`. Full frames are linear equivalences from an arbitrary
module `V` over `D ⊗[ℚ] Global.FiniteAdeles ℚ` to the actual full rational Tate
carrier at a field-valued point `s`. A common explicit hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison` determines the Tate
module structures at every endpoint. No injectivity of `i`, finite dimension,
or existence of a frame is assumed.

A group `G` acts on the source through a homomorphism `ρ` to its linear
automorphisms. The right action on frames is `eta · g = eta ∘ ρ(g)`.
For any subgroup `U` of `G`, `AdelicFrameRightOrbit` is the quotient by this
right `U` action. No normality or topological condition on `U` is needed.
Postcomposition on the target commutes with this right action.

The away family uses a natural modulus `m`, the carrier `RationalAway`, and
coefficients `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, with the common hypothesis
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m` coupled to
`h`. The away carrier selects orders `n` with `Nat.Coprime n m` before
rationalization. For prime `m` it is the prime-to-p carrier. Neither existence
nor independence of the scalar-comparison hypotheses is proved here. The
field-valued points need not be algebraically closed for these constructions.

## Three quotient equivalences

`adelicFrameRightOrbitTestIso` takes `e : Over.mk s ≅ Over.mk t` and sends
`[eta]` to `[adelicFrameTestIso A h i V e eta]`. The underlying Tate transport
restricts along `e.inv`; its inverse restricts along `e.hom`. The `_mk` and
`_symm_mk` lemmas record both representative formulas. The `_refl` and `_trans`
lemmas prove identity transport and transport first by `e`, then by `f`, for
`e.trans f`.

`adelicFrameRightOrbitBaseChangeId` goes from orbit classes for the actual
identity pullback of `A` to orbit classes for `A` at the same point `s`.
The source action of `D` is
`(AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i`.
Its `_mk` lemma sends a class to the class of `adelicFrameBaseChangeId` of its
representative.

For `b : S' ⟶ S` and `c : S'' ⟶ S'`,
`adelicFrameRightOrbitBaseChangeComp` goes from classes on the direct pullback
by `c ≫ b` to classes on the successive pullback, first by `b` then by `c`,
at the same point `s : Spec Ω ⟶ S''`. Both endomorphism actions are pulled
back by the actual corresponding `rationalBaseChangeEnd` maps. The `_mk` and
`_symm_mk` lemmas give the classes of the forward and inverse
`adelicFrameBaseChangeComp` images.

Each construction applies `RightOrbit.equiv` to the corresponding frame
equivalence. Equivariance follows by linear-equivalence extensionality: applying
target postcomposition before or after source precomposition gives the same
value on each vector. The representative formulas are definitional.

## Coherence on classes

`adelicFrameRightOrbitBaseChange_id` starts with a class for the identity
pullback at `s`. Pointed orbit base change gives a class at `s ≫ 𝟙 S`.
Transport along `(Over.mapId S).app (Over.mk s)` gives the same class at `s`
as `adelicFrameRightOrbitBaseChangeId`.

`adelicFrameRightOrbitBaseChange_base_comp` starts with a class for the
successive pullback at `s : Spec Ω ⟶ S''`. Its two equal routes are:

1. Apply pointed orbit base change by `c`, then by `b`, ending at
   `(s ≫ c) ≫ b`.
2. Apply the inverse of `adelicFrameRightOrbitBaseChangeComp`, then pointed
   orbit base change by `c ≫ b`, then test-isomorphism transport by
   `(Over.mapComp c b).app (Over.mk s)` to the same endpoint.

The inverse in the second route is necessary because the comparison was
constructed in the direct-to-successive direction. The proofs use quotient
induction and apply `congrArg (RightOrbit.mk U)` to the corresponding proved
frame equality. The test-isomorphism identity and composition laws use the
same argument.

Every construction and lemma has an away counterpart with the prefix
`primeToAdelicFrameRightOrbit` in place of `adelicFrameRightOrbit`. These use
the away frame comparisons and the same quotient argument.

These results concern unrestricted ambient frame classes. They impose neither
a Weil-form condition nor geometric fundamental-group fixedness; the PEL
levels in the source require both additional conditions. No rational-topology
result, separate higher coherence law, or complete moduli functor is claimed.
