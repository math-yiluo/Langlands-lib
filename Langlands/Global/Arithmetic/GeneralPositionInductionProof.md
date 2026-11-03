# Irreducibility from separated normal-subgroup characters

This module is an internal algebraic component of the proof of
`Langlands.Global.GeneralPositionOfExactStabilizerStatement`, implementing
the Clifford–Mackey step used by Harris in the proof of Lemma 4.7,
condition (4.12). The original source is Michael Harris, *The local
Langlands conjecture for GL(n) over a p-adic field, n < p* (1998),
Definition 4.5, printed p.201 / PDF p.25, and the proof of Lemma 4.7,
printed pp.204–206 / PDF pp.28–30, registered as
`harris-1998-local-langlands`. The finite-coordinate argument here is an
internal proof of the algebraic assertion, rather than a transcription of
an expanded argument in Harris.

The public helper `induce_irreducible_of_separation` takes a subgroup `H`
of finite index in an arbitrary group `G`, a normal subgroup `N ≤ H`, and
a complex unit-valued character of `H`. Its hypothesis says that the
conjugate restrictions of this character to `N` distinguish every two
right cosets of `H`. Its conclusion is irreducibility of the actual
`FiniteRepresentation.induce H (characterLine χ)` used in the Library.
There is no finite-order hypothesis and no assumption of semisimplicity
for other representations.

The proof uses `FiniteRepresentation.Induction.coordinates`, the
Library's linear equivalence from the equivariant-function induction
model to functions on the finite set of right cosets. The character
carrier is `ULift ℂ`; applying the linear equivalence `ULift.moduleEquiv`
at each coordinate gives scalar-valued functions.

There are three steps.

1. For a submodule stable under diagonal operators whose eigenvalue
   functions distinguish coordinates, each coordinate component of a
   vector also lies in the submodule. To preserve coordinate `i` while
   killing `j`, apply `(a(i)-a(j))⁻¹ (T-a(j))`. Induction over all other
   coordinates produces `Pi.single i (v i)`. The inverse exists by the
   separation hypothesis.
2. For a representation expressed in finite scalar coordinates, suppose
   such diagonal operators come from group elements, and group elements
   can carry any chosen source coordinate to any chosen target
   coordinate. A nonzero invariant subspace has a vector with a nonzero
   coordinate. Coordinate isolation, translation, a second isolation,
   and scalar multiplication yield every coordinate vector. Their finite
   sum yields every vector, proving irreducibility. Nonemptiness of the
   coordinate set also establishes that the representation is nonzero.
3. For the actual induced character, right translation by `n ∈ N` acts
   at the coset represented by `x` through the scalar `χ(x n x⁻¹)`.
   Normality puts the conjugate in `N`, and `N ≤ H` permits evaluating
   the character. The equivariance law of the coinduced functions proves
   this formula. The given character separation is precisely the
   separation of these scalar eigenvalues, since units inject into ℂ.
   Right translation by `y⁻¹x` carries evaluation at `x` to evaluation at
   `y`. The preceding invariant-subspace argument therefore applies.

The universes of the group and coordinate set are unrestricted. The
character line in this helper has carrier universe zero, matching the
line in the general-position target; the induced module has the
universe required by the Library's induction construction.
