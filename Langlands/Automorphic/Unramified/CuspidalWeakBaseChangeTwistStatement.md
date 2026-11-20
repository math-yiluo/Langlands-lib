# Determinant twists in a weak base-change fibre

`Langlands.Automorphic.Unramified.CuspidalWeakBaseChangeNormTwistStatement`
uses the weak base-change relation on actual full cuspidal classes.
Twisting a lower class by a finite-order character trivial on the
extension norm leaves its given weak lift unchanged. For a cyclic
extension this is the twist direction of the fibre assertion in
Arthur–Clozel (1989), III.6.3, printed p. 217. The same local calculation
applies over a general finite extension of number fields. The proof
uses the actual `IsoClass.HasSpectralSystem.determinantTwist` construction.
Away from the finitely many ramified and exceptional places, if `w` lies
above `v` with residue degree `f`, the norm of an upstairs uniformizer is
a downstairs uniformizer to the power `f` times a unit. A norm-trivial
character unramified at `v` therefore scales the lower spectrum by an
`f`-th root of unity. The upper spectrum remains attached to its supplied
class, and the powers in the weak relation are preserved.

`Langlands.Automorphic.Unramified.CuspidalDeterminantTwistArithmeticComapStatement`
is the naturality of the finite-order twist and pullback on actual
classes. The proof compares multiplication by the character of the adelic
determinant before and after pullback, including the transported finite,
compact and enveloping actions. This is the pullback/twist compatibility
used in the Galois convention of Clozel–Rajan, *Solvable base change*,
§1.1, PDF p. 2, and §2, PDF pp. 6–7. In the cyclic tower it permits the
iteration of a twist relation with a Galois-invariant character. No
spectral uniqueness theorem is needed for this naturality statement.
