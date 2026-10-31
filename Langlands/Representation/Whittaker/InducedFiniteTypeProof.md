# Finite type of upper-parabolic induction

Author: Worker 172.

`Langlands.inducedFiniteType.{uF,uV}` proves exactly the closed proposition
`Langlands.InducedFiniteTypeStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.InducedStatement`.
For every prime, actual p-adic field with its canonical topology, positive total
rank, ordered positive block shape, and family of admissible complex block
representations finitely generated over their group algebras, the actual
unnormalized upper-parabolic smooth induction of their external tensor product
is finitely generated over the ambient GL group algebra.

The field universe `uF` and common block-carrier universe `uV` remain independent.
The factors may be reducible or zero. Finite type means group-algebra finite
generation; it imposes no finite complex dimension. The target and all its
imported pairs are unchanged.

## Implemented proof

Write `T = F.canonicalTopologicalData`, and let `χ_i` be
`T.blockInverseHalfCharacter B i`. These are the inverse restrictions of the
upper Levi half-modulus to the block coordinates. The published module
`Langlands.Representation.Induction.BlockCharacterAbsorption` constructs them
with open kernels.

1. Apply the published `Langlands.glAdmissibleFiniteLength` to each original
   block representation, using its admissibility, its given group-algebra finite
   generation, and positivity of the block size. This gives finite length of the
   original factors. That theorem uses `F.canonicalTopology`, whereas the target
   uses `T.topology`; `PadicField.canonicalTopologicalData_topology` supplies the
   required equality of topologies.
2. Twist each factor by `χ_i`. The private helper `finiteLength_twist` transports
   both chain conditions through `twistSubrepresentationOrderIso` and the order
   isomorphisms between invariant subrepresentations and group-algebra
   submodules. The published `isAdmissible_twist_iff`, using the open kernel,
   gives admissibility of each twisted factor. Package these factors as actual
   `SmoothRep` objects on their original carriers in `Type uV`.
3. Apply the published closed theorem
   `Classification.admissibleFiniteLengthProductPreservation F T` to these
   admissible finite-length factors and the original ordered block shape. Its
   conclusion is finite length of their actual normalized product induction.
4. Use the published actual representation equivalence
   `T.normalizedProductInverseHalfAbsorptionEquiv B π`. It identifies this
   normalized induction of the inverse-half-twisted factors with the target
   unnormalized induction of the original factors. The half-modulus and its
   inverse cancel in the left covariance. Both sides use the same upper
   parabolic and right translation; the equivalence preserves function values.
5. The private helper `finite_of_finiteLength_equiv` converts its intertwiner
   into a surjective group-algebra linear map. Finite length transfers along
   this map. Its Noetherian consequence supplies `Module.Finite` for the target.

Thus the normalized product theorem is applied only after the original blocks
have been proved to have finite length. Finite generation of the induced
representation is obtained in the last step. All finite-length and normalization
inputs are published theorems with their displayed hypotheses discharged here.

## Provenance and source conventions

This is an internal composition of the named Library results and the two
elementary transport helpers described above. The mathematical assertion is the
finite-type part of Jacquet, Piatetski-Shapiro and Shalika, *Rankin--Selberg
Convolutions* (1983), §2.3, printed p.386 (PDF p.21). The original passage was
read visually. It states admissibility and finite type for the induced
representation of admissible finite-type blocks.

The implemented proof uses Casselman's finite-length route:
*Introduction to the theory of admissible representations of p-adic reductive
groups*, draft of 1 May 1995, Theorem 6.3.10, printed/PDF pp.60–61, supplies the
source of the published block finite-length criterion, and Corollary 6.3.8,
printed/PDF p.60, supplies the arbitrary-parabolic finite-length preservation
underlying the published block-product proof. Those original passages were read
directly. Casselman §3.1, printed/PDF p.32, defines normalized induction using the
positive half-modulus and the right action, as in the Library.

JPSS formulates its assertion with normalized lower induction. Here the
finite-length theorem applies directly to the actual upper parabolic, and the
published inverse-half absorption equivalence proves the precise normalization
change needed for the target. The proof therefore establishes the upper
unnormalized assertion directly, without appealing to an unproved comparison
with JPSS's lower model. Its conclusion is finite generation; admissibility of
induction and Whittaker heredity are separate propositions.

Registered originals:

- `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
  retained at
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- `casselman-1995-admissible-representations`, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
  retained at
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.

No source-specific erratum affecting these passages was identified in the
supplied source records. The tensor absorption and chain-condition transports
are derived algebraic arguments, with their implemented maps described above.
