# Flat closed subgroups of groups of multiplicative type

The entry theorem is
`Langlands.GroupScheme.relativeMultiplicativeTypeClosedSubgroup.{u}`.
Its type is exactly the unchanged published
`Langlands.GroupScheme.RelativeMultiplicativeTypeClosedSubgroupStatement.{u}`.
It proves that, for every scheme `S`, every homomorphism `i : H ⟶ G` with
`G` of multiplicative type, `i` a closed subgroup inclusion, and `H → S` flat
and locally of finite presentation, `H` is of multiplicative type. The
universe `u` is arbitrary. No domain, noetherian, reducedness, local-ring,
quasi-finiteness or smoothness hypothesis is added to the target.

The statement is Conrad, *Reductive group schemes* (2014), Corollary B.3.3,
printed/PDF p.290, with multiplicative type as in Definition B.1.1, p.280.
The existing statement's Markdown records the source correspondence. The
implemented proof is an algebraic local reconstruction and spreading argument;
it does not use Conrad's complete-local deformation proof or assume that
deformation statement.

## Implemented proof

The supporting proposition
`FlatGroupLikeHopfMultiplicativeTypeStatement` says that a commutative Hopf
algebra that is flat as a module, finitely presented as an algebra, and
spanned as a module by its group-like elements has actual Hopf spectrum of
multiplicative type. The present module proves this proposition as
`flatGroupLikeHopfMultiplicativeType` and applies the concrete implication
`relativeMultiplicativeTypeClosedSubgroup_of_flatGroupLikeHopf` to obtain the
entry theorem. Thus the Hopf proposition is discharged, not retained as a
hypothesis of the final result.

For a commutative Hopf `R`-algebra `A` satisfying those three assumptions,
consider each prime `p` of `R`. Scalar extension to `R_p` remains flat and
finitely presented, and `HopfCoordinates.span_groupLike_baseChange` shows that
its group-like elements still span. `Langlands.GroupLikeSpan.groupFG` and
`bialgEquiv` (in `Langlands/Algebra/GroupLikeSpanLocal.lean`) reconstruct this local Hopf
algebra as the group algebra on its finitely generated abelian group of
actual group-like elements. The wrapper
`exists_groupAlgebra_model_of_isLocalRing` returns a finitely generated
additive character group `M` and a bialgebra equivalence to `R_p[M]`.

The definition `HopfCoordinates.groupAlgebraBaseChangeEquiv` identifies
`S ⊗[R] R[M]` with `S[M]` as bialgebras. Its construction uses the actual group
schemes: `baseChangeSpecIso` identifies scalar extension of the Hopf algebra
with base change of its Hopf spectrum; `Diagonalizable.hopfSpecIso` compares
that spectrum with the diagonalizable group; and
`Diagonalizable.baseChangeIso` compares the diagonalizable models across the
coefficient extension. Full faithfulness of `hopfSpec` turns the resulting
actual group-scheme isomorphism back into a bialgebra equivalence. There is
no inference of Hopf compatibility from an arbitrary algebra equivalence.

The theorem `exists_away_isDiagonalizable_of_local_model` spreads the local
model to a principal neighborhood. `R[M]` is finitely presented over `R`
by `Diagonalizable.finitePresentation_addGroupAlgebra`; torsion in `M` is
allowed. Compose the local model with `groupAlgebraBaseChangeEquiv` to obtain
an equivalence between the scalar extensions of the two fixed finitely
presented `R`-algebras `A` and `R[M]`. Apply
`Langlands.BialgebraSpreading.exists_away_bialgEquiv` with the multiplicative
set `R \ p`. It gives `f ∉ p` and a bialgebra equivalence between their scalar
extensions over `R_f`. Compose again with `groupAlgebraBaseChangeEquiv` and
use `isDiagonalizable_of_bialgEquiv` to obtain an actual diagonalizable model
on `Spec R_f`.

The localization-spreading theorem uses an explicit directed system of
principal localizations. Its underlying bialgebra-spreading theorem first
descends the algebra equivalence through the directed limit, then descends
the counit and comultiplication equations using finite-type equality
descent. Hence the neighborhood equivalence respects the actual Hopf
structures; this step does not rely only on the underlying schemes being
isomorphic.

`HopfCoordinates.isMultiplicativeType_of_forall_exists_away` assembles these
principal neighborhoods into an fppf cover of `Spec R`. Each prime lies in
its chosen `D(f)`, and each principal-localization spectrum map is an open
immersion, hence flat and locally of finite presentation. This proves
`flatGroupLikeHopfMultiplicativeType`.

Finally, the reduction module applies that criterion to the actual affine
Hopf coordinates of a closed subgroup of a diagonalizable group. The
coordinate map is surjective, so its restricted monomials give group-like
spanning. Flatness and local finite presentation give respectively module
flatness and algebra finite presentation of the actual coordinate Hopf
algebra. Actual group-scheme isomorphisms transport the result. Affine open
covers handle arbitrary bases for diagonalizable ambient groups; the
ambient group's defining fppf splitting cover and composition of covers
handle every group of multiplicative type. The final theorem is the
application of this reduction to the proved Hopf criterion.

## Supporting files

The proof uses the following supporting files, each with its paired Markdown:

- `Langlands/Algebra/GroupLikeSpanLocal.lean`: local flat
  group-like Hopf reconstruction, via prime fibres, a finitely generated
  nilpotent ideal, Nakayama and flat lifting of linear independence.
- `Langlands/Algebra/BialgebraSpreading.lean`: bialgebra-equivalence spreading
  along explicit directed coefficient limits.
- `Langlands/Algebra/BialgebraLocalization.lean`: specialization to actual
  principal localizations.
- `Langlands/GroupScheme/Torus/GroupLikeHopfBaseChange.lean`: scalar extension
  of group-like spanning and finite presentation of finitely generated
  abelian group algebras.
- `Langlands/GroupScheme/Torus/HopfDiagonalizableLocality.lean`: actual
  diagonalizable models and principal-neighborhood cover assembly.
- `Langlands/GroupScheme/Torus/RelativeMultiplicativeTypeSubgroupReduction.lean`:
  the Hopf criterion and its concrete implication to the exact target.

The individual Markdown files of these pairs describe the implemented helper proofs and their scope. The
published target's Lean/Markdown pair and its entire import closure are
unchanged. No proof holes, new axioms, or native decision procedures are used.
