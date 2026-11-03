# Existence target for the actual adjoint determinant on P and M

`DynamicAdjointDeterminantExistenceStatement` is an unproved proposition target
over every field and universe. Its only structural inputs are an actual
connected reductive `G`, a cocharacter, and inclusions representing its dynamic
parabolic `P`, centralizer `M`, and unipotent subgroup `U`.

It concludes affineness of these three groups and the existence of a rank,
natural finite coordinates on the actual `Lie(U)`, a matrix representation of
`P`, and algebraic characters of `P` and `M`. The representation is required to
equal the construction from `parabolicAdjointAction`; its action on every test
algebra must recover the actual differential in those coordinates. The
character of `P` equals `adjointDeterminantCharacter`. The character of `M`
equals both its restriction along the actual `centralizerToParabolic` inclusion
and the determinant constructed from `centralizerAdjointAction`. Both
characters evaluate to their intrinsic Lie determinants on every test algebra.

All affine instances and finite coordinates occur in the conclusion. Neither
a representation nor a character nor its existence is assumed. The actions
are the actual normalized conjugations `p*u*p⁻¹` and `m*u*m⁻¹` after the
given inclusions into `G`. Test algebras include arbitrary scalar extensions
and nonreduced algebras. The target allows rank zero, arbitrary characteristic,
and nonsplit groups.

This is a derived algebraic package, not a literal local-field theorem in
the motivating sources. Renard, 9 July 2026 version, §V.3.1–V.3.4, printed
p.110 (PDF p.116), describes actual parabolics, their Levi factors and
normalization, and Lie roots; §V.5.4, printed pp.126–127 (PDF pp.132–133),
computes the analytic modulus with root multiplicities. Waldspurger (2003),
§I.1, journal pp.238–239 (PDF pp.4–5), fixes actual parabolic/Levi subgroups,
algebraic characters and Lie roots. Neither passage asserts the unrestricted
field/test-algebra existence statement here.

The derived route uses the structural and coordinate-existence target,
the constructed finite differential representation and determinant morphism,
and compatibility with restriction of the actual action. For the underlying
tangent and scalar-extension mechanism, see Conrad–Gabber–Prasad, second
edition (2015), §2.1, printed pp.52–54 (PDF pp.78–80), and §A.7,
printed pp.529–530 (PDF pp.555–556), especially formula (A.7.2). This statement
does not claim a proof of those remaining structural or comparison targets.

Registered sources: `renard-2026-representations-groupes-reductifs-padiques`,
`waldspurger-2003-plancherel`, and
`conrad-gabber-prasad-2015-pseudo-reductive`. Haar measures, absolute values,
and square roots are outside this target.
