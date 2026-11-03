# Duality term comparison from standard Weyl classes and conjugation

This internal construction combines the published actual Jacquet and induction
conjugation comparisons with the conditional duality factorization. It uses a
locally compact nonarchimedean group in universe `uG`, complex smooth
representation carriers in `max uG uV`, and an independent finite label type in
universe `uI`. The underlying representations and exact finite-length
Grothendieck groups are the existing ones.

`conjugateJacquet_preservesFiniteLength` considers actual decompositions
`Q = L ⋉ V` and `P = M ⋉ U` with closed radicals. The displayed element `g`
conjugates the literal Levi and radical subgroups, in the convention
`x ∈ M ↔ g⁻¹*x*g ∈ L` and `x ∈ U ↔ g⁻¹*x*g ∈ V`.
Jacquet preservation of finite length for `P` implies that preservation for `Q`.
No conjugacy hypothesis on `P` and `Q` is needed for this Jacquet assertion.

For a finite-length ambient object `A`, the published `jacquetConjugationIso`
identifies the pullback of `rQ A` along the actual continuous Levi group
equivalence `conjugationEquiv g hLM` with `rP A`. The latter has finite length
by the displayed preservation premise. The published `hasFiniteLength_of_iso`
therefore gives finite length of the pullback. The reverse implication of
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`, applied to that group
equivalence, gives finite length of `rQ A` itself. This last theorem compares
invariant-subspace lattices for an actual surjective group homomorphism.

`conjugateJacquetFiniteLengthObject` pairs the actual object `rQ A` with this
derived certificate. Its value remains the existing normalized Jacquet object;
it can be inserted into the existing exact finite-length Grothendieck group.

`contragredientTermComparison_of_duality_of_weylConjugacy` retains the standard
family `P I = M I ⋉ U I`, its `ParabolicFiniteLength` premises, ambient
compact-open cofinality, and ambient smooth-dual finite-length preservation.
Its additional explicit inputs are:

* `inducedClassWeylConjugacy` for the standard family and the subgroup `T`;
* actual decompositions `Q I = M I ⋉ V I` with closed radicals;
* a cardinality-preserving equivalence `e` on the finite-subset indices;
* actual normalizer elements `n I` for `T`, with
  `x ∈ P (e I) ↔ (n I)⁻¹*x*n I ∈ Q I` and the same membership convention
  for the Levi and radical subgroups;
* actual isomorphisms `rP(D A) ≅ D(rQ A)` for every finite-length ambient
  object, and `D(iP σ) ≅ iP(D σ)` for every finite-length standard Levi
  object. Here `D` is the actual smooth contragredient.

The proof obtains Jacquet finite-length preservation for each `Q I` from
`conjugateJacquet_preservesFiniteLength`, applied to the standard decomposition
at `e I`. The published
`conjugateInductionClass_eq_of_weylConjugacy` obtains `[iQ σ] = [iP σ]` from
the same actual subgroup conjugation and the supplied standard induced-Weyl
class predicate. This class theorem allows arbitrary finite-length witnesses
for the two induced objects. Those two derived inputs complete the hypotheses
of `contragredientTermComparison_of_duality`, which gives exactly the
existing `ContragredientTermComparison`.

Thus opposite Jacquet finite-length preservation and a separate same-Levi
opposite-induction class equality need not be supplied again once the actual
conjugation and standard induced-Weyl class theorem are known. The family `Q`
is arbitrary in this internal result. A rational-point application must still
identify it with the actual opposite family and prove the displayed subgroup,
normalizer, indexing, duality and standard Weyl premises. This file proves
none of those closed representation-theoretic or geometric inputs and does
not prove `RationalContragredientCommutationStatement`.

The construction is derived entirely from the named published declarations
above and introduces no literature assertion. The use of
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` is the general
invariant-subspace argument at the start of `Classification.FiniteLengthProof`;
it uses `FiniteLengthAssembly.length_comp_surjective` and
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`. The latter is
the actual order equivalence between invariant-subspace lattices under a
surjective acting-monoid map; its proof uses only surjectivity. These
declarations do not use the GL finite-length or cuspidal-support theorems
appearing elsewhere in their modules. The new proof bodies invoke no
Langlands classification, character independence, geometric lemma,
adjointness, or cuspidal-support theorem.
Dependencies of future proofs of the explicit duality and standard Weyl
premises remain separate obligations.
