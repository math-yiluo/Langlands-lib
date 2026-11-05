# Power factorization and full finite quotient of a diagonalizable group

Author: Worker 1341. This is an internal construction derived from the published
diagonalizable character interface and the finitely generated abelian-group
structure theorem in Mathlib.

Fix an additive equivalence `e : Λ ≃+ (I → ℤ) × A`. Character projection onto the
free factor defines `freeInclusion : D(I → ℤ) → D(Λ)`. This is an actual closed
subgroup, since that character projection is surjective. If `I` is finite its
source is a split torus, by the published `splitIso`.

Character inclusion of `A` defines `finiteProjection : D(Λ) → D(A)`. It is flat
and surjective over a nonzero ring. The theorem `kernel_finiteProjection` proves
that its full represented kernel is the range of `freeInclusion`. The proof
works on every test scheme: a character trivial on the `A` factor factors through
the free factor, and conversely every such factored character is trivial on `A`.
Over a Noetherian ring, finite generation of `Λ` and `A` gives local finite
presentation of this map, so `isFppfQuotient_finiteProjection` supplies the
published represented fppf quotient predicate.

For a natural number `n`, inclusion of the free character factor after
multiplication by `n` defines `powerToFree : D(Λ) → D(I → ℤ)`. For `n ≠ 0` this
map is flat and surjective over a nonzero ring, and schematically dominant over
any ring: the coordinate group-algebra map is injective. If `n` kills `A`, its
composition with `freeInclusion` is the actual `n`th power endomorphism of
`D(Λ)`. This includes inseparable powers in positive characteristic.

The derived lemma `exists_freeFiniteEquiv` expresses the finitely generated
abelian-group structure theorem with both factors in the original arbitrary
universe, using `ULift` as in the published diagonalizable decomposition.
`exists_power_torus_finiteQuotient` chooses `n` to be the exponent of the finite
factor. Over an arbitrary field it supplies the closed split torus, the
schematically dominant power factorization, the full finite diagonalizable
target, and its actual represented fppf quotient. The finite target retains its
entire scheme structure, including characteristic torsion and nilpotents.
No reducedness or perfectness hypothesis is used.
