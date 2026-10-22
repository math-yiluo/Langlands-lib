# The profinite-integer scalar ring and its prime-to-p analogue

`Langlands.Global.ProfiniteIntegerRing` is the actual ring of compatible residue
families

\[
 \widehat{\mathbb Z}=\{(x_n)_{n\in\mathbb N_{>0}}\in
 \prod_{n>0}\mathbb Z/n\mathbb Z:\quad
 x_m\bmod n=x_n\text{ whenever }n\mid m\}.
\]

The topology is the subspace topology inherited from the product of the finite
discrete residue rings. Addition, multiplication, negation, zero and one are
coordinatewise. In particular its ring unit has coordinate `1` at every modulus;
its additive zero has coordinate `0`.

## Construction and intrinsic laws

The shared construction `ResidueLimit modulus` allows any index type `ι` and any
map `modulus : ι → ℕ+`. Its underlying type is the carrier of the explicitly
constructed subring `ResidueLimit.compatibleSubring modulus` of
`∀ i, ZMod (modulus i : ℕ)`. The only equations defining membership are reduction
compatibility; no theorem or equivalence is assumed as extra structure data.
The commutative ring and topology are the standard subring and subtype instances.

`ResidueLimit.transition h` is `ZMod.castHom h _` for a natural-number
divisibility proof `h : (n : ℕ) ∣ (m : ℕ)`. It maps `ZMod m` to `ZMod n`.
`transition_self` and `transition_comp` give identity and composition, proved by
representing each residue by an integer. `transition_intCast` gives the
normalization on every integer.

`ResidueLimit.reduction i` is evaluation at coordinate `i`, as a ring
homomorphism. `compatible` and `transition_comp_reduction` express its
compatibility with reduction. `ext` states that all coordinates jointly detect
equality. `intCastHom : ℤ →+* ResidueLimit modulus` is the canonical integer
ring homomorphism, with `reduction_intCast` asserting its exact residue at every
coordinate. `reduction_surjective` follows because every residue has an integer
representative; that integer supplies a compatible family.

For any `NonAssocSemiring R` and family of ring homomorphisms
`f i : R →+* ZMod (modulus i : ℕ)` satisfying
`(transition h).comp (f j) = f i` whenever the corresponding moduli divide,
`lift f hf : R →+* ResidueLimit modulus` assigns the family `fun i => f i r` to
`r`. The equation `reduction_lift` and uniqueness theorem `lift_unique` give the
ring inverse-limit universal property. No restriction on the universe of `R`
is imposed beyond Lean's ordinary universe parameters.

The compatibility locus is closed: for each `i`, `j` and divisibility proof,
the two continuous maps to the finite Hausdorff ring `ZMod (modulus i)` have a
closed equalizer; intersect these equalizers. Thus the limit is compact, as a
closed subspace of a product of compact finite spaces. Hausdorffness and total
disconnectedness descend from that product to the subtype. The pointwise ring
operations restrict continuously to the subring. These results are exposed as
`CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` and `IsTopologicalRing`
instances for `ResidueLimit modulus`.

`continuous_reduction` proves continuity of every projection. `continuous_iff`
states that a map into the limit is continuous exactly when all its coordinate
maps are continuous. `continuous_lift` and `existsUnique_continuous_lift` give
the corresponding universal property with continuity. The latter quantifies
over every topological `NonAssocSemiring R`; no compatibility between its
operations and topology is needed for this stronger coordinate criterion.
In particular it applies to all topological rings.

## Full and prime-to-p interfaces

The full type specializes `modulus` to the identity on `ℕ+`.
`ProfiniteIntegerRing.reduction n` and `ProfiniteIntegerRing.intCastHom` are
short names for the generic maps. A Tate module indexed by positive integers
can use the image under `reduction n` as its scalar on the `n`-torsion
coordinate; this file constructs no Tate module or group scheme.

`PrimeToModulus p := {n : ℕ+ // Nat.Coprime (n : ℕ) p}` and
`PrimeToProfiniteIntegerRing p` is the same construction on this index type.
It is defined for every natural number `p`; when `p` is prime it is precisely
the residue limit over the positive integers prime to `p`. No primality
hypothesis is needed for the construction or any stated law.
`PrimeToProfiniteIntegerRing.reduction` and `.intCastHom` expose its maps.
The commutative ring, compact Hausdorff totally disconnected topology, and
universal properties are inherited from the shared construction.

`PrimeToProfiniteIntegerRing.restrict p` is the ring homomorphism from the full
limit which forgets all coordinates not coprime to `p`. It is continuous by
`continuous_restrict`; `reduction_restrict` identifies each of its remaining
coordinates. No surjectivity assertion for this restriction is included.

## Provenance and scope

This is an internal elementary residue-limit construction for the scalar ring
needed by the full Tate-module project. It is a derived analogue of the
compatible-residue scalar action in the following original sources, not a claim
that either source proves every general topological-ring statement here:

- Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), Chapter I, printed p.18 (PDF p.26), defines the full Tate
  limit over positive integers and its away-from-a-set-of-primes version.
  Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`;
  SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
  (10.2), printed p.142 (PDF p.146), explicitly defines the Tate-ℓ inverse
  limit and its coordinatewise action by compatible residues of an ℓ-adic
  integer. Registered source:
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`; SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The implemented proofs use Mathlib's `ZMod.castHom`, subrings, product and
subspace topologies, compactness of products, and closed equalizers. The
construction and proofs above explain the additional internal derivation from
the source motivation.

`Langlands.Weil.ProfiniteIntegers` remains the separately defined profinite
group completion of `Multiplicative ℤ`. This module does not import or change
that group and does not assert an identification with it. The intended later
bridge is an additive-group equivalence, expressed using `Multiplicative` if
necessary and normalized on integers by
`n ↦ Langlands.Weil.frobenius (Multiplicative.ofAdd n)`. Its group identity
corresponds to additive zero, not to the scalar ring unit. The bridge statement
and its proof are separate work. There is likewise no identification here with
a product of p-adic integer rings or with any finite-adele ring; rational
comparison work must use the published `Langlands.Global.FiniteAdeles ℚ`.
