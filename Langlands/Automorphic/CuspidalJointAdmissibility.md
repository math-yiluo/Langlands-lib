# Joint admissibility of every actual cuspidal realization

Module `Langlands.Automorphic.CuspidalJointAdmissibility`. Worker 174 wrote it as a step towards
`Langlands.Automorphic.CuspidalArchimedeanIrreducibleAdmissibleComponentStatement` (G1, Task 5992,
`8a7f44bc-c7bc-4ceb-96aa-6eff19b38f97`). Provenance: internal. It removes the central-character
hypothesis from the Library's joint admissibility theorem by a determinant twist, in the same
way the Library's `CuspidalContragredientExistenceProof` removes it for contragredients.

The Library's `OperatorRealization.IsJointlyAdmissible S` asks, for every open subgroup `L` of the
finite adelic group and every representation `σ` of the standard compact `K_∞` on `ℂ^m`, that the
space `jointMultiplicitySpace` of `K_∞`-intertwiners `ℂ^m → S` with `L`-fixed values be
finite-dimensional.

- `OperatorRealization.compactDeterminantTwistRep χ σ`: the representation
  `k ↦ χ(det k) σ(k)` of `K_∞`, with the Library's `HeckeCharacter.compactAdelicDeterminant`.
  A definition for this proof.
- `OperatorRealization.isJointlyAdmissible_of_heckeDeterminantTwist`: if the twist of `S` by
  `χ ∘ det` (Library `heckeDeterminantTwist`) is jointly admissible, so is `S`. Proof:
  1. Let `L₀ = L ∩ ker(χ ∘ det)`. The kernel is open
     (`HeckeCharacter.finiteAdelicHeckeDeterminant_isOpen_ker`).
  2. Let `e` be the twisting isomorphism `heckeDeterminantTwistEquiv`. Composition with `e`
     maps the multiplicity space of `S` for `(L, σ)` linearly and injectively into that of the
     twist for `(L₀, χ(det)·σ)`.
  3. `L₀`-fixedness holds because `χ(det d) = 1` there (`heckeDeterminantTwistEquiv_finite`).
     Equivariance comes from `heckeDeterminantTwistEquiv_compact`.
  4. Finite dimension passes back along the injection (`Module.Finite.of_injective`).
- `CuspidalOperatorRealization.isJointlyAdmissible`: every actual cuspidal realization `T` is
  jointly admissible. Proof:
  1. `T` has a central character `ω` (Library `existsUnique_hasCentralCharacter`).
  2. Its twist by the Library's `unitarizingCharacter r ω` has a unitary central character
     (`hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter`).
  3. That twist is jointly admissible by the Library's
     `CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness` with the proved
     `PrimitiveAdelicHeight.siegelSetGLFiniteness`.
  4. Apply the previous lemma.
