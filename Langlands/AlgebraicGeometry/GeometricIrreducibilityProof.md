# Geometric irreducibility spreads from the actual generic fibre

Workers 1606 and 336 prove the exact published proposition
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.FiniteTypeGeometricallyIrreducibleGenericSpreading`
in every universe `u`. Given a locally finite type, quasi-compact morphism of
arbitrary schemes, a whole-space generic point, and geometric irreducibility of
its actual residue-field fibre, the theorem produces an open neighbourhood of
that point over which the actual restricted morphism is geometrically
irreducible.

The endpoint composes the unconditional affine algebraic theorem
`Langlands.Algebra.finiteTypeGeometricIrreducibilitySpreading` with
`finiteTypeGeometricallyIrreducibleGenericSpreading_of_algebraic`. All rings and
field tests in this composition lie in the common scheme universe. The
algebraic theorem itself allows independent base-ring, algebra and test-field
universes.

For the algebraic theorem, first consider a faithful finite type domain algebra
C over a domain R. Localizing C to its fraction field and changing the tensor
base to the fraction field of R preserve primality of the geometric generic
nilradical. Every finite separable simple subextension then gives a reduced
domain tensor over an algebraically closed field, whose scalar map is
bijective; dimension shows that the subextension has degree one. This supplies
the separable-constant premise for a hypersurface model with uniform
exponential-characteristic power containment. The existing absolute polynomial
irreducibility spreading theorem supplies one base denominator. Generic
flatness applied to C/(g) supplies another, making multiplication by the model
denominator g injective in every nearby field tensor. Thus g avoids all minimal
primes, and the radicial containment argument makes each such tensor's
nilradical prime.

The supporting generic flatness proof handles arbitrary domains: a finite
presentation descends to its Noetherian integer-coefficient model, and a finite
type algebra is covered by a finitely presented model with torsion kernel.
After making that model flat, torsion freeness kills the kernel. Uniform
specialization of generic nilpotence then removes the domain and faithfulness
conditions on C. Quotienting the base by its prime nilradical, using its actual
generic residue field as a fraction field of that quotient, removes the domain
condition on the base. Tensor cancellation preserves both the original generic
premise and all tested field fibres.

For schemes, the actual affine pullback and residue-field fibre comparisons
identify the ring tensor criteria with geometric irreducibility. Over an affine
target, quasi-compactness gives a finite affine source cover. Members meeting the
generic fibre spread by the affine theorem; the other members disappear after
shrinking. For every pair of surviving members, choose one affine open inside
their intersection meeting the generic fibre, and spread that open too.
Intersecting these finitely many neighbourhoods gives geometrically irreducible
cover members with nonempty pairwise intersections in every field fibre.
The geometric open-cover criterion gives the conclusion. Restriction to an
affine neighbourhood of the generic point handles an arbitrary target.
This use of one affine overlap for each pair imposes no quasi-separatedness.

The source is Stacks Project Lemma 37.27.5 (0559), statement and both proofs,
in the registered collection
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0559.html`.
The collection SHA256 is
`7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`;
the file SHA256 is
`6dc5e34232f56f8111e2581afd2822d79276b962e4110f23eb411ab8b166ca1f`.
The implemented proof combines algebraic generic flatness, the hypersurface
model and finite-cover assembly; the helper Markdown describes each deduction.
The model adapts the existing Anthropic FLT construction as documented in its
paired explanation, and retains its existing imports and attribution.

The theorem adds no Noetherian, separation, flatness, reducedness, properness,
smoothness or perfect-field hypothesis. It supplies the spreading step for
Stacks 055G; finite generic splitting and generic constancy of geometric
connectedness remain separate assertions of the parent program.
