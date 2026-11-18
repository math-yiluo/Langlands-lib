# Modulus cancellation under reversal of the minimal parabolic

Worker 248, Task 5460. `RationalReversedModulusStatement.{u}` is a Prop-valued
statement at arbitrary universe `u`; `rationalReversedModulus` proves it.
This derived module transports the published actual
opposite-radical Haar reciprocity to the exact `standardUnipotentModulus`
characters used by the constant-term target. It also cancels those characters
in the published reversed minimal-modulus factorization. It supplies no
spherical-function estimate or weighted-integrability theorem.

For a connected reductive group over a nonarchimedean local field, a maximal
split torus, generic cocharacter `nu`, and standard face `J`, the standard
Levis for `(nu,J)` and `(-nu,-J)` are the same actual subgroup. If `m` and `n`
are their subtype presentations of the same ambient point, the first theorem
proves that their radical moduli multiply to one. The proof chooses a
standard cocharacter for `J`, identifies the two radicals with the dynamic
unipotent groups of its opposite cocharacters, and invokes the published
`dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`. Its root
reflection and central-split-torus inputs are discharged by published
unconditional proofs. A private equality helper identifies the closed Haar
characters at the same ambient conjugating element, independently of which
Levi subtype contains that element.

The second theorem applies the published `rationalMinimalModulus_eq_mul` to
the reversed chamber. Multiplication by the original radical modulus cancels
the reversed radical factor and leaves exactly the reversed minimal Levi
modulus. Its domain is the actual reversed minimal parabolic inside the
common Levi, with no Cartan-covering, compact subgroup or analytic premise.

Provenance is derived from the published Library character identities. This
is the modulus cancellation used in the proof of Waldspurger's Proposition
II.4.5 (printed pp.262-263), after changing the minimal parabolic as allowed
in its following remark. Source: Waldspurger (2003), registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
