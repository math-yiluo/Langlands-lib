# The socle of an ordered product of distinct supercuspidal factors: proof

The module `Langlands.AllFieldBZ.Representation.Classification.RegularCuspidalProductSocleProof`
proves `Langlands.AllFieldBZ.Classification.RegularCuspidalProductSocleStatement`
as the theorem `Langlands.AllFieldBZ.Classification.regularCuspidalProductSocle`,
for every nonarchimedean local field `F : LocalFieldPackage.{uF}` with its
topological data `T`, in the universe-polymorphic form `.{uF, uV}` of the
statement.

## What is proved

Fix a positive rank \(n\), an ordered block shape `B` of \(n\) with blocks
\(n_1, \dots, n_r\), and smooth irreducible supercuspidal representations
\(\rho_i\) of \(\mathrm{GL}_{n_i}(F)\) whose cuspidal data
\((n_i, [\rho_i])\) are pairwise distinct. Let
\(\pi = \rho_1 \times \cdots \times \rho_r\) be the normalized parabolic
induction from the standard upper block parabolic of `B`
(`T.normalizedProductInductionFunctor B`). Then `HasIrreducibleSocle` holds
for \(\pi\): there is an irreducible representation with an injective
intertwiner into \(\pi\), and every injective intertwiner from an irreducible
representation into \(\pi\) has the same image subspace.

## The proof

Write \(\sigma = \rho_1 \otimes \cdots \otimes \rho_r\) for the external
tensor product (`FiniteTensor.externalSmoothObject`), a smooth representation
of the Levi subgroup \(M = \prod_i \mathrm{GL}_{n_i}(F)\), and let
\(J = r_{B}\) be the normalized Jacquet functor along the same upper block
parabolic, regarded as a functor from smooth representations of
\(\mathrm{GL}_n(F)\) to representations of \(M\) (the private functor
`upperJacquetToRep`).

1. **The inducing tensor.** `glCuspidalTensor` shows that \(\sigma\) is
   irreducible and cuspidal for the Levi subgroup.

2. **The Jacquet module of the product.** The blocks of `B` are associated
   with themselves, so `associatedJacquetFiltration` gives a finite filtration
   of \(J(\pi)\) whose subquotients are the Weyl transports
   \(w \cdot \sigma\), one for each minimal conjugating permutation \(w\) from
   `B` to `B` (`MinimalConjugatingPermutations B B`). Each transport is
   irreducible (`CuspidalSupport.JacquetLength.isIrreducible_transport`). By
   `finiteFamilyFiltrationMultiplicity`, the Jordan–Hölder multiplicity of
   \(\sigma\) in \(J(\pi)\) is therefore the number of these \(w\) with
   \(w \cdot \sigma \cong \sigma\), that is, the cardinality of
   `AssociatingPermutations B B σ σ`.

3. **The stabilizer is trivial.** The private lemma
   `distinctTensor_stabilizer_count` shows that this cardinality is one. The
   identity permutation is a minimal representative and lies in the set.
   Conversely, let \(w\) be a minimal conjugating permutation with an
   equivalence \(E : w \cdot \sigma \cong \sigma\). Fix a source block \(i\)
   and let \(j\) be the target block to which the underlying permutation
   sends it (`blockMap B B v i`). Restrict \(E\) to the copy of
   \(\mathrm{GL}_{n_j}(F)\) in the \(j\)-th factor of the target Levi
   subgroup (`MonoidHom.mulSingle` at \(j\)). On pure tensors this subgroup
   acts on the transported tensor \(w \cdot \sigma\) only through its
   \(i\)-th factor, via the entry-permutation isomorphism
   `factorHom hw i` from \(\mathrm{GL}_{n_j}(F)\) to \(\mathrm{GL}_{n_i}(F)\)
   (`external_leviConjugation_symm_mulSingle`), and it acts on \(\sigma\)
   only through its \(j\)-th factor (`external_mulSingle_tprod`). The
   factor-action lemma `nonempty_equiv_of_factor_actions`, using
   irreducibility of \(\rho_j\) and of the pullback of \(\rho_i\)
   (`isIrreducible_comp_of_surjective`), then gives an equivalence between
   \(\rho_i\) pulled back along `factorHom hw i` and \(\rho_j\).
   `cuspidalDatum_eq_of_equiv` turns it into the equality of cuspidal data
   \((n_i, [\rho_i]) = (n_j, [\rho_j])\), and the distinctness hypothesis
   forces \(j = i\). So \(w\) sends each block to itself. Then \(w\)
   lies in the block Weyl group of `B`, so it has the same double coset as
   the identity, and `weylDoubleCoset_injective` identifies the two minimal
   representatives.
   Hence \(\sigma\) occurs in \(J(\pi)\) with multiplicity exactly one.

4. **The functor is suitable.** \(J\) is additive, and it preserves
   monomorphisms: the coinvariants under the unipotent radical preserve
   injections into smooth representations
   (`coinvariants_map_injective_of_smooth`), because every finite subset of
   the radical lies in a compact open subgroup
   (`Parabolic.unipotentFiniteContainment`).

5. **An irreducible subrepresentation exists.** \(\sigma\) is irreducible and
   cuspidal, so `cuspidalInductionLength` shows that \(\pi\) has finite length.
   The rank is positive, so `B` has at least one block, and
   `Derivative.ProductVanishing.nontrivial_normalizedProduct` shows that
   \(\pi\) is nonzero. `exists_irreducible_subrepresentation_of_finiteLength`
   then gives an irreducible smooth subrepresentation of \(\pi\).

6. **Every irreducible subrepresentation sees \(\sigma\).** Let
   \(i : Q \hookrightarrow \pi\) be an injective intertwiner from an
   irreducible \(Q\). Evaluation at the identity
   (`exists_ne_zero_normalizedJacquet_hom`) gives a nonzero intertwiner
   \(J(Q) \to \sigma\), the Frobenius reciprocity map of the inclusion. Since
   \(J(i)\) is injective and \(\sigma\) is irreducible,
   `jordanHolderSubobjectSimpleMapDetection` shows that \(J(Q)\) has a
   Jordan–Hölder count of \(\sigma\) that is positive and at most one.

7. **Conclusion.** `Langlands.Classification.multiplicityOneSocleCore`
   applies to the functor \(J\), the representation \(\pi\) and the test
   object \(\sigma\). If two irreducible subrepresentations had different
   images, they would meet in zero, so their direct sum would embed in
   \(\pi\). Since \(J\) is additive, it carries that direct sum to the direct
   sum of the two Jacquet modules, and since \(J\) preserves monomorphisms,
   this sum embeds in \(J(\pi)\). Each summand contains \(\sigma\) with
   positive count by step 6, so the Jordan–Hölder count of \(\sigma\) in
   \(J(\pi)\) would be at least two. This contradicts step 3. So all
   irreducible embeddings into \(\pi\) have the same image, which is
   `HasIrreducibleSocle`.

## Dependencies

- `Langlands.AllFieldBZ.CuspidalSupport.glCuspidalTensor`: irreducibility
  and Levi cuspidality of the external tensor of supercuspidal factors.
- `Langlands.AllFieldBZ.CuspidalSupport.associatedJacquetFiltration`: the
  filtration of the normalized Jacquet module of quasicuspidal induction
  between associated Levi subgroups by Weyl transports (the geometric lemma).
- `Langlands.AllFieldBZ.CuspidalSupport.cuspidalDatum_eq_of_equiv`:
  equivalence of supercuspidal representatives after an entry permutation
  gives equality of cuspidal data.
- `Langlands.AllFieldBZ.CuspidalSupport.cuspidalInductionLength`: finite
  length of irreducible cuspidal induction.
- `Langlands.AllFieldBZ.CuspidalSupport.exists_ne_zero_normalizedJacquet_hom`:
  the nonzero Jacquet map obtained by evaluating at the identity.
- `Langlands.AllFieldBZ.Derivative.ProductVanishing.nontrivial_normalizedProduct`:
  a normalized product of nonzero factors with at least one block is nonzero.
- `Langlands.finiteFamilyFiltrationMultiplicity` and
  `Langlands.jordanHolderSubobjectSimpleMapDetection`: Jordan–Hölder
  multiplicities from a filtration by an irreducible family, and positivity of
  a count detected by a nonzero map to a simple object.
- `Langlands.Classification.multiplicityOneSocleCore`: a multiplicity-one
  count in the image of an additive, monomorphism-preserving functor, together
  with positivity on every irreducible subrepresentation, gives a unique
  irreducible submodule.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. The module sets `maxHeartbeats` to 1200000.

## Relation to the literature

The statement is the unique-submodule part of Zelevinsky, *Induced
representations of reductive p-adic groups II. On irreducible representations
of GL(n)*, Ann. Sci. ENS (4) 13 (1980), Proposition 2.10, printed p. 180
(`zelevinsky-1980-induced-ii`). Zelevinsky's proof describes the whole lattice
of submodules of \(\pi(\lambda)\) through orientations of a graph (2.8–2.9)
and the length-two products of 1.11. The Lean proof uses only the
multiplicity count in step 3. That count is part of Zelevinsky's
Proposition 2.1(a), printed p. 176: for multiplicity-free support every
irreducible inducing tensor occurs exactly once in the Jacquet modules of
\(\pi(\lambda)\). Frobenius reciprocity, as in step 6, then shows that every
irreducible submodule contains that tensor in its Jacquet module.
