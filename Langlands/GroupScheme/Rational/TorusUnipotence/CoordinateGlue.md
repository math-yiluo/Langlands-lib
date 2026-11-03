# Unipotence of split torus actions without a zero Lie weight

Module `Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGlue`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module assembles the proof. It applies the abstract results of `TopWeight`,
`MatrixCoefficients`, `Regrading`, `BigCell` and `Rigidity` to the coordinate algebra
`A = CharacterUnits.Coord H` of an affine group `H` over a field `k`. The algebra `A` carries the
character grading `W χ = CoordinateWeights.weightSpace b χ` coming from an action `b` of a split
torus `S` on `H`.

## Statements

*Cotangent space of an augmented algebra.* Let `ε : A →ₐ[k] k` be an augmentation of a
commutative `k`-algebra `A`.

* `cotangentMap_mul_of_mem`: for `x ∈ ker ε`,
  `cotangentMap ε (a * x) = ε a • cotangentMap ε x`.
* `finite_cotangent`: if `A` is Noetherian, then `(ker ε) / (ker ε)²` is finite-dimensional over
  `k`.

*The group case.* Let `H` be a group scheme over `Spec k` with affine structure morphism, `S` a
commutative group scheme over `Spec k`, and `b : AutomorphicAction S.toGrp H`.

* `augmentationIdeal_eq_ker`: the Library's `augmentationIdeal H` is `ker (coordCounit H)`
  (`rfl`).
* `finite_cotangentSupport hS b`. If `H` is locally of finite type and `S` is a split torus, then
  the set `cotangentSupport b` of characters occurring in the augmentation cotangent space is
  finite.
* `cotangentWeightSpace_eq_bot`: the cotangent weight space of a character outside
  `cotangentSupport b` is `0`.
* `mem_sq_of_not_mem_cotangentSupport hS b hχ hf hfε`. Let `S` be a split torus and
  `χ ∉ cotangentSupport b`. If `f ∈ W χ` and `coordCounit H f = 0`, then `f` lies in
  `(ker coordCounit) ^ 2`.
* `formallySmooth_coord`: if `H` is smooth, then `A` is formally smooth over `k`.
* `isUnipotent_of_zero_not_mem_cotangentSupport hS b hsupp h1 hε`. Let `H` be smooth with
  connected underlying space and `S` a split torus. Assume `0 ∉ cotangentSupport b` (`hsupp`),
  `1 ∈ W 0` (`h1`), and that `coordCounit H` vanishes on `W χ` for `χ ≠ 0` (`hε`). Then `H` is
  unipotent (`IsUnipotent H`).
* `isUnipotent_of_actionWeightSpace_zero_eq_bot hS b h0`. Let `H` be smooth with connected
  underlying space and `S` a split torus. If the Lie eigenspace
  `RelativeRoot.actionWeightSpace b 0` is `⊥`, then `IsUnipotent H`.

## Proof

*Finiteness.* Choose finitely many generators `s` of `ker ε` (Noetherianity). Their classes span
`(ker ε) / (ker ε)²`: by span induction over `x = ∑ aᵢ sᵢ`, `cotangentMap_mul_of_mem` turns
`aᵢ sᵢ` into `ε aᵢ • [sᵢ]`. For `H`, `A` is Noetherian (`isNoetherianRing_coord`). The cotangent
weight spaces are independent by `CoordinateWeights.coordinateWeightDecomposition`. In a
finite-dimensional space, only finitely many members of an independent family are nonzero
(`WellFoundedGT.finite_ne_bot_of_iSupIndep`).

*Second-order vanishing.* For `f ∈ W χ` with `coordCounit H f = 0`, `f` lies in the augmentation
weight space of `χ`. By the last part of `coordinateWeightDecomposition`, its class lies in the
cotangent weight space of `χ`, which is `0` for `χ ∉ cotangentSupport b`. So `f ∈ (ker ε)²` by
`Ideal.toCotangent_eq_zero`.

*Formal smoothness.* `Lie.coordinateIso H` identifies `H.X` with `Spec A` over `Spec k`, so
`Spec A → Spec k` is smooth. `DynamicSmooth.smooth_algSpec_iff` turns this into
`Algebra.Smooth k A`, which implies formal smoothness.

*Unipotence.* `A` is a domain (`CharacterLatticeProof.isDomain_coord`), Noetherian and formally
smooth. By `coordinateWeightDecomposition`, `W` is an internal direct sum, and
`mul_mem_weightSpace` makes it multiplicative. The support `cotangentSupport b` is finite and does
not contain `0`. So `IsSplitTorus.exists_pairings_ne_zero` gives a cocharacter `ν` that pairs
nontrivially with every character in it. Let `w = ⟨·, ν⟩ : X(S) →+ ℤ`. If `w χ = 0`, then
`χ ∉ cotangentSupport b`, and second-order vanishing gives the hypothesis `hsq` of `Regrading`.
Apply `isUnipotent_of_graded` (from `MatrixCoefficients`) to the `ℤ`-grading `regrade W w`:

* it is internal by `isInternal_regrade`;
* the comultiplication is compatible with it by `regrade_comul` and `coordComul_mem_iSup` (from
  `CoordinateGrading`);
* `1` lies in degree `0` by `le_regrade` and `h1`;
* the rigidity hypothesis is `exists_eq_smul_one_of_regrade`, with the counit laws
  `lid_comp_coordCounit` and `rid_comp_coordCounit` from `MatrixCoefficients`.

*Lie weights.* The Library's `CoordinateWeights.cotangentLieSupport` identifies
`cotangentSupport b` with `RelativeRoot.actionWeightSupport b ⊤`. A character `χ` in the latter
has a nonzero Lie vector in `actionWeightSpace b χ`. For `χ = 0` this space is `⊥` by `h0`, so
`0 ∉ cotangentSupport b`. The remaining hypotheses of
`isUnipotent_of_zero_not_mem_cotangentSupport` are `one_mem_weightSpace_zero b` and
`coordCounit_eq_zero b hS` from `CoordinateGrading`.

## Provenance

This is the proof of the general observation in the proof of Proposition 2.3.11 of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (p. 82): a smooth connected affine
group with a split torus action having no zero weight on the Lie algebra is unipotent. The route
differs from CGP's. CGP argue with a maximal torus of the semidirect product: a nonunipotent
group would give a nontrivial torus centralized by the acting torus, hence a nonzero fixed Lie
vector. Here the argument is purely Hopf-algebraic: big-cell injectivity
(`gradedBigCellInjectivity`) gives top-weight rigidity, and `isUnipotent_of_graded` turns that
into fixed vectors of matrix corepresentations.
