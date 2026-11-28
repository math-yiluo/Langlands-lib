# Cocharacters transported across local group identifications

Let `φ : LocalGroupIso G H U` identify two group schemes over the cover `U`. The homomorphism
`φ.transportedCocharacter χ` is the pullback of `χ : Gm → H` followed by the inverse of the
actual group isomorphism recovered from `φ`. This preserves closed immersions by base change
and composition with an isomorphism.

On a test scheme `Z` with cover point `a`, the transported homomorphism evaluates at `t` to
`φ_a⁻¹(χ(t))`, using the pullback point equivalences to project back to `G(Z)`. If a cocycle
`ξ` records the discrepancy of `φ` for conjugation, evaluating the discrepancy at
`φ_b⁻¹(χ(t))` gives `Int(ξ(a,b))(φ_b⁻¹(χ(t))) = φ_a⁻¹(χ(t))`. The argument applies over
any base scheme, in particular over imperfect fields and over number fields.

Suppose a cocharacter `ν : Gm → G` over the base has pullback conjugate to the transported
homomorphism by a section `p` of the pulled-back group. Projecting `p` gives a cochain `g`.
On a test with cover point `a`, the corresponding value of the transported homomorphism is
`g(a) ν(t) g(a)⁻¹`. Substituting these expressions for both cover points shows that
`g(a)⁻¹ ξ(a,b) g(b)` commutes with `ν(t)`. The proof applies the same identity on every
further test, using naturality of the twisted cocycle to obtain membership in
`torusCentralizer ν`. If the cover is surjective and fppf, closedness descends to `ν`
from the conjugacy of its pullback with the transported closed immersion.

The construction gives the transport and adjustment used to reduce an isotropic inner twist
to a split torus centralizer. The number-field application of that reduction is in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8, proof of
Proposition 6.22, printed p. 378. The all-test construction follows directly from base change
and the discrepancy equation.
