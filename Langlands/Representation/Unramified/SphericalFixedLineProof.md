# The actual spherical fixed space is a line: proof

`Langlands.Unramified.sphericalFixedLine` proves
`Langlands.Unramified.SphericalFixedLineStatement.{uF, uV}`, imported unchanged from
`Langlands.Representation.Unramified.SphericalClassificationStatement`. The theorem
type is exactly this proposition, with no extra parameters or assumptions.

The statement covers every prime `p` and finite extension `F : PadicField p`, every
rank `r + 1`, and every actual irreducible admissible smooth complex representation
`A : AutomorphicObject F r.succPNat` of `GL_(r+1)(F)`, with carrier in an arbitrary
universe and possibly infinite-dimensional. It uses the canonical topology. If the
`sphericalSubgroup F r = GL_(r+1)(O_F)`-fixed space of `A` is nonzero, its complex
`finrank` is one.

Provenance: Borel (1979), *Automorphic L-functions*, §7.2 (printed page 39, PDF
page 48), and Gross (1998), *On the Satake isomorphism*, §6 (PDF page 11), record this
fact. The Lean proof is the internal route described below.

## Proof

After introducing `p`, `F`, `r`, `A` and the nonvanishing hypothesis, the proof
applies `Langlands.Hecke.finrank_fixedVectors_eq_one_of_corner_comm`, from
`Langlands.Representation.Hecke.CommutativeCornerFixedLine`, with these inputs:

- the group `GL_(r+1)(F)` with its canonical topology and topological-group
  structure, passed explicitly in the same way as the published
  `standardHeckeOperator`, because the object's group index is `r.succPNat` rather
  than `r + 1`;
- the Haar measure `sphericalHaar F r` and the compact open subgroup
  `sphericalOpenSubgroup F r`, whose underlying subgroup is `sphericalSubgroup F r`;
- smoothness `A.obj.isSmooth`;
- commutativity of the corner, `sphericalHeckeAlgebra_mul_comm F r`, from
  `Langlands.Representation.Unramified.SphericalHeckeCommutativity`;
- irreducibility `A.property.1`;
- finiteness of the spherical fixed space, `A.property.2.2 (sphericalOpenSubgroup F r)`,
  from the admissibility clause, which applies to every open subgroup;
- the nonvanishing hypothesis.

In summary: the fixed space is a simple module over the commutative corner
(Bernstein–Zelevinsky 2.10, `isSimpleModule_fixedVectors`). It is finite-dimensional
by admissibility, so each corner element acts by a scalar, and simplicity then
forces dimension one. Commutativity comes from Gelfand's trick with the
inverse-transpose automorphism and the Cartan decomposition.

The development check of this module reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
