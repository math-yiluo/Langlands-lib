# Pointed separable residue extensions over strictly Henselian algebras

This internal derived construction, for lifting prescribed diagonalizations to
clopen subgroups over strictly Henselian local rings, uses the relative
Henselian etale lifting of `Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift`
and combines existing prime-local G-ring approximation, etale residue extensions, separably closed field embeddings,
and Henselian lifting. All carriers have an arbitrary fixed universe `u`.

`etaleCompletionApproximation_atPrime` exposes finite-order etale approximation
for the maximal-ideal completion of `T_q` for every prime `q` of a finite-type
integer algebra `T`. The proof applies the published `finiteTypeIntGRing`
theorem and `etaleCompletionApproximation_of_regularAlgebra_completion` to
the regular completion map of the prime localization. No maximality of `q`
is assumed.

`exists_pointed_etale_residue_extension` takes a commutative ring `T`, a
Henselian local `T`-algebra `A`, and a separably closed field `k` with a
surjective algebra map `A → k` compatible with its `T`-algebra structure.
For a prime `q` of `T`, supply a compatible `κ(q)`-algebra structure on `k`.
Let `K/κ(q)` be a finite separable extension with compatible `T`-algebra
structure. The result constructs an etale `T`-algebra `E`, a prime `Q` of
`E`, a ring equivalence `e : κ(Q) ≃ K`, and a map `σ : E →ₐ[T] A` such that:

- `Q` lies over `q`;
- `e` respects the original `T`-scalar maps;
- the inverse image of the maximal ideal of `A` under `σ` is exactly `Q`;
- `σ` extends to a local `T`-algebra homomorphism `σloc : E_Q → A`.

The implemented proof first uses the published etale residue-extension theorem
to realize `K` as `κ(Q)` with its scalar equation. A separably closed embedding
`K → k` gives a residue-valued point of `E`; the relative Henselian etale
lifting theorem lifts it to `σ`. Injectivity of both field maps identifies
the residue kernel with `Q`. Every element outside `Q` maps to a unit, so
localization extends `σ`. Its composite into `k` is the residue map of `E_Q`
followed by a field embedding. This is a local homomorphism, hence `σloc`
is local as well.

The field and scalar hypotheses imply that the original point is compatible
with the Henselian algebra; arbitrary residue structures are not silently
substituted. Neither theorem asserts that the finite-type ring or its prime
localization is Henselian. The point-extension theorem itself requires no
Noetherian or finite-type assumptions on `T` or `A`. It does not construct
the group-scheme coefficient model used in the full lifting theorem.
