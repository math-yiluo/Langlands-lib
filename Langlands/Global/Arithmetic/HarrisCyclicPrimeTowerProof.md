# A cyclic prime-step tower for finite Galois p-adic extensions

Authors: Worker 84 and Worker 27. Worker 84 supplied the complete proof
and explanation; Worker 27 adopted the pair, checked its dependencies and
source correspondence, and prepared the exact-target submission. The theorem
`Langlands.Global.harrisCyclicPrimeTower.{u}` proves exactly
`Langlands.Global.HarrisCyclicPrimeTowerStatement.{u}`. All auxiliary
declarations are private. The proof imports the existing published target
and preserves its statement and import closure.

## Implemented proof

First, every ring automorphism of a field of characteristic `p` fixes
its prime field. The helper `primeFieldAutHom` packages it as an algebra
automorphism over `ZMod p`: `RingHom.ext_zmod` identifies the two maps
from the prime field. This homomorphism is injective because it retains
the underlying function. For a finite residue field, Mathlib supplies
cyclicity, hence solvability, of its prime-field automorphism group.
The helper `ringAut_isSolvable` pulls solvability back along the
injection. No cyclicity of the multiplicative units modulo a power of
`p` is used.

For an actual p-adic field `L` with topological data `T`, the helper
`localAut_isSolvable` considers the full group of field automorphisms
fixing a given intermediate base `K`. It installs the actual finite
residue field and prime-field algebra from `T`. The published theorem
`Langlands.Ramification.Padic.isSolvable_inertia T K` makes the inertia
subgroup solvable. The actual
`Langlands.Ramification.Padic.residueHom T K` maps to the residue-field
automorphism group, and its kernel is the existing inertia subgroup.
`Group.isSolvable_of_ker_le_range` combines these facts. Surjectivity of
the residue homomorphism is unnecessary.

For `E : CommonClosure.Extension F`, its canonical p-adic structure is
`E.asPadicField`. The proof explicitly installs the composite algebra
over `Padic p` and its scalar tower through `F.Carrier`. The preceding
argument proves solvability of the actual group
`E.field ≃ₐ[F.Carrier] E.field`. Together with the finite-dimensional
instance carried by `E` and the Galois premise, this permits applying
the published theorem
`Langlands.FieldTheory.solvableGaloisPrimeTower F.Carrier E.field`.
That theorem constructs an ascending tower of intermediate fields of
`E.field`.

The helper `liftExtension` maps each such intermediate field into the
fixed `AlgebraicClosure F.Carrier` using `IntermediateField.lift`.
Its finite-dimensional instance is transported along
`IntermediateField.liftAlgEquiv`. For an inclusion `A ≤ B` in the
ascending tower, `lift_prime_step` supplies the corresponding inclusion
of their images in the common closure. It uses the commuting ring
equivalences induced by `liftAlgEquiv` to transport the Galois property
and finite dimension across the actual inclusion algebras, using
`IsGalois.of_equiv_equiv` and
`Algebra.finrank_eq_of_equiv_equiv`. The transported degree remains
prime and positive. Galois automorphism cardinality equals that degree,
so `isCyclic_of_prime_card` supplies the required cyclicity. Thus the
result satisfies the existing `GeneralPosition.IsCyclicPrimeStep`
without altering its convention.

Finally, `localCyclicPrimeTower` reverses the finite index using
`Fin.rev`. The lift of the top intermediate field is exactly `E.field`,
and the lift of the bottom is the bottom field of the common closure.
`Fin.rev_succ` and `Fin.rev_castSucc` identify each reversed descending
step with the transported ascending step. The public theorem introduces
exactly the parameters and instances of the named target and applies
this construction.

## Scope and provenance

The proof includes arbitrary carrier universe `u`, every prime `p`,
and the trivial extension. In particular, it assumes neither solvability
nor a tower as an input, and does not exclude residue characteristic
two. The zero-length tower is permitted by the imported generic theorem.
No unproved general-position proposition or reciprocity family is used.

The local solvability argument implements the consequence of Serre,
*Local Fields* (1979), IV.2, Proposition 7 and Corollary 5, printed
pp.66–68 (one-based PDF pp.73–75). The proof uses the Library's actual
inertia result, the finite residue automorphism group, and Mathlib's
solvable-group extension theorem. The subsequent generic Galois construction, using successive prime
quotients and induction on the remaining extension degree, is imported
by Lean name.

The intended Harris application is Definition 4.5(i), printed p.201
(PDF p.25), and the field-theoretic tower entering the proof of Lemma
4.7, pp.204–206 (PDF pp.28–30), in *The local Langlands conjecture for
GL(n) over a p-adic field, n < p* (1998). As explained by the target's
Markdown, this extracted prerequisite starts at any finite Galois
extension rather than just a Galois closure. It proves the tower alone;
Mackey irreducibility, exact stabilizers, character existence and global
tower realization remain separate obligations.

The retained registered originals are
`serre-1979-local-fields` (SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`)
and `harris-1998-local-langlands` (SHA-256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`).
Serre's 2019 author corrections (registered source
`serre-book-corrections-2019`), PDF pp.2–3, contain no correction to the
cited corollary. Harris's character issue at `p = 2` does not enter
this proof.
