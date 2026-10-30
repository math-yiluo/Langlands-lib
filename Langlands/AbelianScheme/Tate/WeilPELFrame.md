# Source coordinates on actual Weil-compatible PEL frames

Worker 142. This derived construction specializes the published source-similitude
and form-isomorphism machinery to the actual full and prime-to-modulus Weil
frames of `WeilFrame`. A chosen actual compatible frame gives an equivalence
between the existing source-similitude group and the whole compatible frame
space. No frame existence assertion is made.

The hypotheses are the original abelian scheme, dual-scheme geometry,
Poincare evaluation and pullback coherence inputs, finite Weil transition
compatibility, actual dual-valued homomorphism `polarizationMap`, rational
endomorphism-algebra map `i`, geometric point, and finite-adele scalar comparison.
For the away version, the same full comparison is coupled to its existing
prime-to-modulus comparison. The target pairing and Tate twist are exactly
those of `WeilAdelicFrame` and `WeilPrimeToAdelicFrame`; they are not arbitrary
forms or replacement modules.

The rational source is equipped with `RationalPELConditions sigma psi` and
explicit `[Nontrivial V]`. The predicate includes finite dimension, faithfulness,
alternation, nondegeneracy and the involution identity. Its nondegeneracy and
the nonzero-source hypothesis imply that the scalar-extended form takes the
value one. The constructions actually need only this consequence; the other
source conditions remain part of the stated PEL specialization.

`weilAdelicFrameSourceEquiv eta` maps a source similitude `g` to `eta` composed
with its actual underlying operator. Its bijectivity proof reuses
`FormIso.precomp_injective`, supplied with
`hPEL.baseChange_attains_one`, and `FormIso.exists_precomp_eq`. The former
recovers the multiplier from a value-one pair; the latter compares the
existential twist trivializations of two compatible frames. `Equiv.ofBijective`
then supplies the inverse. This inverse is the unique source similitude
relating the two frames. No twist trivialization or roots of unity are
retained in the output.

The application lemma identifies the forward equivalence with the existing
`weilAdelicFrameRightAction`. The injectivity lemma proves freeness in the
explicit sense that `g` maps injectively to `op g` acting on a given frame.
The unique-existence lemma uses the inverse equivalence and its injectivity:
for any two actual frames `eta` and `xi` there is a unique `g` with
`op g` acting on `eta` equal to `xi`. The prime-to-modulus constructions and
three lemmas give the same conclusions for `PrimeToFiniteAdeles m`. In each
case the right-action convention is `(eta * g)(x) = eta(g(x))`.

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
Section 5, printed pp.390-391 (PDF pp.18-19), defines the level orbit with its
Tate twist and states simple transitivity when the frame set is nonempty.
The rational input is fixed on printed p.389 (PDF p.17). Registered source:
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the consulted project notes.
The full-adele version and the equivalence based at a frame are internal derived
specializations of the same algebraic argument. The Lean proof follows the
published `FormIso` lemmas and normalization result described above.

This unit gives source coordinates conditional on a given actual frame.
It does not prove nonemptiness, assert that every dual-valued homomorphism is
a polarization, establish geometric nondegeneracy of its target pairing, or
prove an involution identity for the target action. Those geometric and PEL
compatibilities remain separate obligations. No topology, compact open level,
monodromy or transport assertion is introduced here.
