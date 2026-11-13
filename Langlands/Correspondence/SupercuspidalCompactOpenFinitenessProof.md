# Compact-open finiteness of supercuspidal classes over every local field

Authors: Worker 254 and Worker 261.

Module: `Langlands.Correspondence.SupercuspidalCompactOpenFinitenessProof`.
The final declaration is
`Langlands.Henniart.supercuspidalCompactOpenFiniteness.{uF, uV}`.
Its type is the unchanged published proposition
`Langlands.Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uV}`.
The helper declarations are in
`Langlands.Henniart.AllFieldCompactOpenFiniteness`.

For every field `F : Type uF` with the supplied `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances, every `n : ℕ`,
every character `χ : Z(GL_(n+1)(F)) →* ℂˣ`, and every compact open subgroup `N`
of `GL_(n+1)(F)`, the set of supercuspidal isomorphism classes with central
character `χ` and a nonzero `N`-fixed vector is finite. The representation
carriers lie in the independent universe `Type uV`. The character need not be
unitary, and no finite dimension, decomposition or admissibility hypothesis is
added to the target. Admissibility and actual Jacquet vanishing are part of the
existing supercuspidal condition.

## Source and provenance

The source is I. N. Bernstein and A. V. Zelevinsky, *Representations of the group
GL(n,F), where F is a non-Archimedean local field* (1976), Corollary 4.15,
printed p. 41; registered source
`bernstein-zelevinsky-1976-representations-gln`. The corollary is deduced there
from Theorem 4.14 and §§3.20(b), 3.21 and 3.29. Theorem 4.14 and its proof in
§4.16, p. 41, give fixed-level finiteness for irreducible representations
of the determinant-unit group with compact coefficients. Section 3.20, p. 34,
gives the finite index of `G°Z`; §3.21, pp. 34–35, is the compact-coefficient
criterion; §3.26, p. 36, gives finite irreducible restriction; and §3.29,
pp. 36–37, supplies the character-twist comparison. The cuspidality convention
is in §3.18, p. 34. Sections 2.39–2.40, p. 26, define the source's
“finite” representations by compact support of smooth-dual matrix coefficients;
this does not mean finite dimension of the carrier.

The source uses principal congruence subgroups. Section 3.1, p. 28, says these
form a compact open identity-neighborhood basis. An arbitrary compact open
`N` contains one, and an `N`-fixed vector is fixed by that smaller subgroup;
this yields the stated compact-open consequence. The implemented proof uses
the imported compact-open version of Theorem 4.14 directly.

The finite constituent and twist argument adapts the Library proof in
`Langlands.Correspondence.PadicSupercuspidalFinitenessProof`. Its group-generic
helpers are reused unchanged. The all-field inputs below replace the
p-adic inputs. In particular, the proof packages the actual ambient instances
as `LocalFieldData.ofInstances F`; it never replaces them by canonical p-adic
instances. The `LocalFieldData` structure contains only topology, valuative
relation and a nonarchimedean local-field certificate. Positive characteristic
therefore remains in scope.

## Imported results and comparisons

- `Langlands.AllField.Representation.CuspidalSupport.CompactCoefficientFinitenessProof`
  supplies
  `Langlands.AllField.CuspidalSupport.compactCoefficientFixedLevelFiniteness`.
  This is the product-Levi form of BZ76 Theorem 4.14, for every
  `LocalFieldData F` and compact open subgroup of its actual determinant-unit
  group. Its proof combines `determinantUnitCornerStructure` with
  `sandwichSimpleModuleDimensionBound` through
  `compactCoefficientFixedLevelFiniteness_of_cornerStructure`. We specialize
  it to the one-block Levi and the given carrier universe.
- `Langlands.AllField.Representation.CuspidalSupport.HarishChandraAssembly`
  supplies `Langlands.AllField.CuspidalSupport.leviHarishChandraTheorem`,
  the equivalence between `IsLeviQuasicuspidal` and compact smooth-dual
  coefficients on determinant-unit restriction. Only its forward implication
  is used.
- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnitStructureProof`
  supplies `determinantUnit_sup_center_finiteIndex`. Its determinant orders
  modulo the positive block sizes prove that the determinant-unit group joined
  with the center has finite index. This gives both finite restriction and the
  finite twist quotient.
- `Langlands.AllField.Representation.CuspidalSupport.LeviCompactPart` supplies
  `determinantUnitCompactOpenCofinal`. Together with the generic
  `hasCompactSmoothDualCoefficients_subrepresentation`, this passes compact
  smooth-dual coefficients to an invariant subspace. No decomposition theorem
  from this module is needed.
- The one-block comparisons in `Langlands.Group.GL.SingleBlock` identify the
  product Levi with the actual general linear group.
  `singleBlockLeviEquivContinuous` is a multiplicative homeomorphism whose
  homomorphism is the Levi embedding;
  `singleBlock_leviEmbedding_surjective` also permits descent of representation
  equivalences. `singleBlockRefinementEquiv`,
  `singleBlock_refinedUnipotent_map` and
  `singleBlock_refinedParabolic_ne_top_iff` identify refinements, their
  unipotent subgroups and proper parabolics with the standard block data.
- `Langlands.GeneralLinear.isSupercuspidal_iff_standard`, from
  `Langlands.Representation.Classification.SupercuspidalContragredientAux`,
  gives vanishing for the proper standard block parabolics.
  `Jacquet.coinvariantsMapEquiv` transports the actual coinvariant quotient of
  the pulled-back representation along the Levi embedding. The preceding
  subgroup equalities therefore prove `IsLeviQuasicuspidal` for the pullback.
  This comparison uses actual coinvariants and their subsingleton property.
- `Langlands.FiniteIndexRestriction.finite_irreducible_restriction` gives a
  semisimple restriction spanned by finitely many irreducible subrepresentations
  when the normal subgroup joined with the center has finite index and the
  center acts by scalars. Here the specified character `χ`, pulled back along
  the one-block embedding, supplies those scalars directly.
- The generic BZ76 §3.29 argument is
  `Langlands.CuspidalSupport.exists_twistIntertwiningMap_of_restrictedHom_nonzero`,
  in `NormKernelTwistAlgebra`, followed by
  `twistEquivOfNonzeroIntertwiner`, in `NormKernelTwistElementary`.
  The commutator lies in the determinant-unit group by
  `Abelianization.commutator_subset_ker`, applied to `leviDeterminantNorm`.
- The group-generic helpers imported from
  `PadicSupercuspidalFinitenessProof` are `IsConstituent`,
  `isSmooth_subrepresentation`, `isCompl_toSubmodule`,
  `exists_fixedVectors_ne_bot`, `exists_ne_zero_of_isConstituent` and
  `finite_monoidHom_units`, in `Langlands.Henniart.CompactOpenFiniteness`.
  They apply to arbitrary topological groups and complex representations;
  their statements impose no p-adic field structure.

## Implemented argument

Write `B = fullBlock n` for the one-block shape of rank `n + 1`.
`leviRep` pulls a representation back along `B.leviEmbedding F`.
`unitGroup F n` is the kernel of the block determinant normalized-absolute-value
homomorphism, and `unitRep` is restriction to that group. In this one-block
case it is BZ76's `G° = {g : |det g| = 1}`.
`twistKernel = G° ⊔ Z` and `twistQuotient` is its finite quotient.

`unitLevel F n N` is the inverse image of `N` in `G°`. It is open by
continuity. It is compact because the one-block embedding is a homeomorphism
and `G°` is closed. A nonzero `N`-fixed vector remains fixed by `unitLevel`.
Pullback preserves smoothness and, by surjectivity, irreducibility.
Surjectivity also proves `leviEmbedding_mem_center`, which transports the
specified central action.

For `exists_isConstituent`, let `A` be a supercuspidal representation with
central character `χ` and a nonzero vector fixed by a compact open subgroup
`L` of `G°`. The actual one-block coinvariant comparison proves that its Levi
pullback is quasi-cuspidal, so Harish-Chandra gives compact coefficients on
`G°`. Finite irreducible restriction gives finitely many irreducible invariant
subspaces spanning the carrier and semisimplicity. Averaging over `L`
(`exists_fixedVectors_ne_bot`) shows that one of these subspaces has a
nonzero `L`-fixed vector. Semisimplicity gives it an invariant complement;
compact coefficients pass to it by compact-open cofinality. Its class is
therefore an `IsConstituent` in `CompactCoefficientClass.fixedStratum L`.

For `exists_twist_equiv`, suppose two such representations have a nonzero
intertwiner on `G°`. The generic twist argument gives a character `χ'` of the
Levi trivial on `G°` and a nonzero intertwiner from the `χ'`-twist of the
first representation to the second. Irreducibility makes it an equivalence.
The two original representations have the same central character.
Evaluating the intertwining identity at a central element and a nonzero
vector shows `χ'(z) = 1`: the vector's image is nonzero and the prescribed
central scalar is invertible. Thus `χ'` factors through `twistQuotient`.

Finally, in `centralFixedStratum_finite`, choose a representative of each
class in the desired stratum and a constituent class `cl a` in the finite
`unitLevel`-fixed stratum. For each constituent value choose a reference
representation using `Function.invFun cl`. The common constituent gives a
nonzero intertwiner, so the representation differs from that reference by
a character `tw a` of `twistQuotient`. The map `a ↦ (cl a, tw a)` is
injective: equal pairs give equivalences with the same twisted reference,
and surjectivity of the one-block embedding descends their composite to
the original general linear group. Its codomain is finite by Theorem 4.14
and `finite_monoidHom_units`, which places the values of characters of a
finite group among finitely many roots of unity.

The final theorem applies this construction to every quantified field,
rank, character and compact open subgroup of the published proposition.
Its proof uses only the standard Lean axioms `propext`, `Classical.choice`
and `Quot.sound`.
