# Trigonalizable groups and unipotent quotients (Milne 16.2, (c) ⇒ (d) ⇒ (a))

This helper module proves the implications (c) ⇒ (d) and (d) ⇒ (a) of
`Langlands.GroupScheme.TrigonalizableCharacterizationStatement` (see
[`CharacterizationStatement`](CharacterizationStatement.md)). Throughout, `k`
is a field, `T_N` is the upper triangular group
`GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
(fun i => -(i.val : ℤ))`, `D_N` is the block Levi subgroup
`GeneralLinear.blockLeviScheme` for the same weights (the diagonal torus),
and `d = GeneralLinear.blockLimitHom ...` is the projection `T_N ⟶ D_N` onto
the diagonal. All declarations are in the namespace
`Langlands.GroupScheme.Trigonalizable`. Nothing new is defined.

## (c) ⇒ (d)

- `isUnipotent_kernel_diagonal`: let `j : G ⟶ T_N` be a closed immersion and
  `f = j ≫ d`. If the kernel inclusion `kernelι f` is a closed immersion,
  then `kernel f` is unipotent.
  *Proof.* The same argument as the Library's
  `TriangularTorusQuotientData.isUnipotent_kernel` (in
  [`Absolute.SolvableTorusQuotientReduction`](../Absolute/SolvableTorusQuotientReduction.md)),
  with the unconditional published theorems in place of its hypotheses. The
  pullback property gives `a : kernel f ⟶ kernel d` with
  `a ≫ kernelι d = kernelι f ≫ j`. That composite is a closed immersion, so
  `a` is one (`IsClosedImmersion.of_comp`). Composing with the inverse of
  `GeneralLinear.blockUnipotentIsoKernel` gives a closed immersion `w` of
  `kernel f` into the unitriangular group scheme
  `GeneralLinear.blockUnipotentScheme`. That group is affine and locally of
  finite type over `k`, because its inclusion into `GL_N` is a closed
  immersion (`isClosedSubgroup_blockUnipotentHom`) and `GL_N` is affine
  (`isAffineHom_groupScheme`) and smooth (`GeneralLinear.smoothStatement`).
  The published `unitriangularUnipotent` says that it is unipotent, and the
  published `unipotentClosedSubgroup` passes unipotence to the closed
  subgroup `kernel f`.

- `exists_unipotent_diagonalizable_quotient_of_closed_triangular`
  (Milne 16.2, (c) ⇒ (d); assuming `[LocallyOfFiniteType G.X.hom]`,
  `[IsAffineHom G.X.hom]`): a closed immersion `j : G ⟶ T_N` gives `U`, `i`,
  `Λ` (with `AddGroup.FG Λ`) and `q : G ⟶ D(Λ)` satisfying the four clauses
  of (d).
  *Proof.* The Library theorem
  `DiagonalImageReduction.exists_triangular_diagonalizable_factorization`,
  applied with the published `affineHomImage` and
  `Diagonalizable.closedSubgroupPresentation`, gives a finitely generated
  `Λ`, a closed `D(Λ) ⟶ D_N` and `q : G ⟶ D(Λ)` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q`. Take
  `U = kernel f` and `i = kernelι f`. Since the weights `-(i.val)` are
  injective, `GeneralLinear.diagonalTorusIso` shows that `D_N` is a split
  torus, hence affine, and so `kernelι f` (a base change of the unit section
  of `D_N`) is a closed immersion. Unipotence is
  `isUnipotent_kernel_diagonal`, and normality of the range is the Library's
  `HopfPrimitive.isNormal_range_kernelι`.

## (d) ⇒ (a)

- `isStableSubspace_span_of_mem_characterSpace` (assuming
  `[IsAffineHom G.X.hom]`): if `v` lies in the character space
  `ρ.characterSpace χ` of a rational character `χ`, then `k ∙ v` is a stable
  subspace.
  *Proof.* The Library's `characterSpace_affine` gives `ρ(x) v = c • v` at
  every affine point `x`, with `c` the value of `χ` at `x`. The rest is the
  same computation as `IsStableLine.isStableSubspace` (module
  [`StableLines`](StableLines.md)).

- `exists_stableLine_diagonalizable`: every representation `τ` of
  `D(Λ)` on a nonzero space `kⁿ` has a nonzero `v` spanning a stable line.
  *Proof.* The character spaces span `kⁿ`
  (`iSup_characterSpace_eq_top_diagonalizable`), so one of them is nonzero.
  A nonzero vector in it spans a stable subspace by the previous lemma, hence
  a stable line by `isStableLine_of_isStableSubspace` (`D(Λ)` is affine).

- `isTrigonalizable_of_unipotent_diagonalizable_quotient` (Milne 16.2,
  (d) ⇒ (a); assuming `[IsAffineHom G.X.hom]`): given `i : U ⟶ G` and
  `q : G ⟶ D(Λ)` with `IsClosedSubgroup i`, `IsUnipotent U`, normal range
  and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, the group
  `G` is trigonalizable. Finite generation of `Λ` is not used.
  *Proof.* Let `ρ` be a representation on a nonzero `kⁿ`. `U` is affine,
  being closed in the affine `G`. Let `D` be the Library's
  `normalFixedSubrepresentation ρ i hN`: a representation of `G` on
  `k^{D.dimension}`, with matrices `inclusion` and `retraction`
  (`retraction * inclusion = 1`), whose image is the space of vectors fixed
  by `U`, which intertwines `ρ` and `D.representation`, and on which points
  of `U` act trivially (`kills_subgroup`).
  1. `D.dimension ≠ 0`: since `U` is unipotent, `ρ.restrict i` has a nonzero
     fixed vector `v₀`, and `D.projection` gives
     `v₀ = inclusion (retraction v₀)`, which would be `0` if the dimension
     were `0`.
  2. `kernelι q ≫ D.representation = 0`: by the kernel clause of
     `IsFppfQuotient`, the universal point of `kernel q` factors through `i`,
     so `kills_subgroup` makes its point matrix `1`.
  3. `q` is flat and surjective (from `IsFppfQuotient`) and quasi-compact
     (because `D(Λ)` is affine over `k` and `G` is quasi-compact over `k`).
     So the Library's `FpqcHomDescent.hom` descends `D.representation` to a
     representation `τ` of `D(Λ)` with `q ≫ τ = D.representation`
     (`FpqcHomDescent.fac`).
  4. `exists_stableLine_diagonalizable` gives a nonzero stable line `w` of
     `τ`. By `IsStableLine.restrict` along `q` and `fac`, `w` spans a stable
     line of `D.representation`. By `IsStableLine.of_intertwines` with
     `D.intertwines`, `inclusion w` spans a stable line of `ρ`. It is nonzero
     because `retraction (inclusion w) = w ≠ 0`.

## Provenance

The implications are Milne, *Algebraic Groups* (2017), Proposition 16.2,
(c) ⇒ (d) and (d) ⇒ (a), pp.324–325 (source ID
`milne-2017-algebraic-groups`). For (c) ⇒ (d), Milne takes `U = U_n ∩ G`,
which is unipotent (14.5), and embeds `G/U` into `T_n/U_n`, so that it is
diagonalizable (12.9). The Lean proof takes `U` to be the kernel of
`G ⟶ D_N`, which is `U_N ∩ G`, and obtains the diagonalizable quotient from
the Library's image factorization. For (d) ⇒ (a), Milne uses the nonzero
subspace `V^U`, stable under `G` (5.15), on which `G` acts through `G/U`;
it is then a sum of one-dimensional representations (12.12). The Lean proof
follows this route, with `normalFixedSubrepresentation` for `V^U`,
`FpqcHomDescent.hom` for the action through `G/U`, and character spaces for
the decomposition (only one stable line is needed).
