# Equivalence of the geometric and bundled abelian-scheme definitions

Author: Worker 133.

`Langlands.AbelianScheme.sourceDefinitionEquivalence.{u}` proves exactly
`Langlands.AbelianScheme.SourceDefinitionEquivalence.{u}` from the published
`SourceDefinition` module. For every scheme `S : Scheme.{u}` and actual group
scheme `G : GroupScheme S`, it gives

```text
GroupScheme.IsAbelian G ↔ ∃ A : AbelianScheme S, A.toGrp = G.
```

The geometric predicate consists of smoothness, properness and geometrically
connected fibres of the structure morphism. The bundle additionally records
commutativity. The theorem retains every base and universe of the statement,
and the equality on the right retains the supplied group object and its actual
group law. The statement and its imported definitions are unchanged.

The proof applies the published reduction
`sourceDefinitionEquivalence_of_inverse_isMonHom` from `InversionCriterion`.
For its inversion obligation, fix `S`, `G` and `hG : GroupScheme.IsAbelian G`.
Install the smoothness and properness components of `hG` as local instances.
Smoothness supplies local finite presentation, while properness supplies
quasi-compactness and quasi-separatedness of the structure map. These discharge
the three target hypotheses of the published arbitrary-base theorem
`pointedMorphismRigidity`, imported from `PointedMorphismRigidityProof`.

Apply that theorem with both source and target equal to `G`, using `hG` for
the source geometry and the actual inversion morphism `ι[G.X]` for the map.
Mathlib's `GrpObj.one_inv` proves that this morphism preserves the unit. Rigidity
therefore gives `IsMonHom ι[G.X]`, with no further hypothesis.

The imported reduction completes both directions. Its forward construction
uses multiplicative inversion to prove commutativity on every represented
group of points, then uses `isCommMonObj_iff_isMulCommutative` to obtain
commutativity of the group object. It packages this with the three geometric
properties and sets `toGrp := G`, so the required equality is reflexive. In the
reverse direction it substitutes `A.toGrp = G` and applies `A.isAbelian`.

This final deduction is derived from the published inversion criterion and
arbitrary-base rigidity theorem. The latter's geometric proof, documented in
its companion Markdown, uses field rigidity, relative global functions and
section factorization. The new module supplies the inversion application and
introduces no additional geometric assumption.

The algebraic route follows Lan, *Arithmetic compactifications of PEL-type
Shimura varieties* (2008 thesis), Corollary 1.3.1.7, printed p.108/PDF p.148,
which applies the preceding pointed-morphism corollary to inversion. The
geometric definition is Definition 1.3.1.1, printed p.103/PDF p.143.
The registered original is `lan-2008-arithmetic-compactifications-pel-thesis`,
SHA256 `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`.
Lan's 2021-03-14 revision explicitly assumes a separated target in Corollary
1.3.1.6, printed pp.70–71/PDF pp.98–99; its Corollary 1.3.1.7 on p.71 applies
it to inversion as above. In the present application properness of `G` implies
separatedness, and the imported rigidity theorem in fact proves the stronger
internal target without a separatedness premise. Its companion Markdown
records the source correction and the independent geometric route. The
locally noetherian scope of GIT Chapter 6 is not used to restrict the base here.
