# Relative roots as restrictions of absolute roots: proof

Worker 3483 (author of the proof draft); submitted by Worker 5087.

`Langlands.GroupScheme.relativeRootAbsoluteRestriction.{u}` proves the published
proposition `Langlands.GroupScheme.RelativeRootAbsoluteRestrictionStatement.{u}`
(module `Langlands.GroupScheme.Rational.RelativeRootAbsoluteRestrictionStatement`).
The theorem's type is exactly that proposition, with no added hypotheses.

## The statement

Let `k ⊆ K` be fields, `G` a connected reductive group over `k`, `i : S ⟶ G` a
maximal split torus, and `j : T ⟶ G` a maximal torus with `f : S ⟶ T` and
`groupHom f ≫ j = i`. Suppose `T` splits over `K`. Then a character `α` of `S`
lies in `relativeRoots i` if and only if `α ≠ 0` and the base change of `α` to
`K` equals `f_K ≫ β` for some root `β` of `(G_K, T_K)`. This is Milne,
*Algebraic Groups* (2017), 25.19 with footnote 2 to 25.13 (source ID
`milne-2017-algebraic-groups`); the statement's own Markdown gives the
quotations.

## The proof

The proof introduces the hypotheses and turns the two fields of
`IsConnectedReductive G`, `isAffineHom` and `smooth`, into local instances.
Smoothness supplies the `LocallyOfFiniteType` instance on the structure map.
It then substitutes `i = groupHom f ≫ j`. By definition, `relativeRoots i` is
`roots i`, so the goal is the published lemma

- `Langlands.GroupScheme.mem_roots_iff_exists_splittingField_restriction`
  (module `Langlands.GroupScheme.Rational.AbsoluteRootRestriction`),

applied to `hi.1.1 : IsSplitTorus S.toGrp` (the first component of
`IsMaximalSplitTorus i`, then of `IsSplitSubtorus i`), the splitting
hypothesis `hTK`, `f`, `j` and `α`. That lemma states for a split torus `S`
and a torus `T` split over `K` that `α ∈ roots (groupHom f ≫ j)` if and only if
`α ≠ 0` and the base change of `α` is `f_K ≫ β` for a root `β` of `j_K`.
The maximality of `j` is not used, so it is left unnamed in the proof.

The option `backward.isDefEq.respectTransparency false` is set for this theorem
only, as in the module of the lemma it applies. That module sets it for its
whole body.

## Published inputs

- `Langlands.GroupScheme.RelativeRootAbsoluteRestrictionStatement`
  (`Langlands.GroupScheme.Rational.RelativeRootAbsoluteRestrictionStatement`),
  the target.
- `Langlands.GroupScheme.mem_roots_iff_exists_splittingField_restriction`
  (`Langlands.GroupScheme.Rational.AbsoluteRootRestriction`).
- The fields `IsConnectedReductive.isAffineHom` and
  `IsConnectedReductive.smooth` (`Langlands.GroupScheme.Reductive.Basic`), and
  the definitions `IsMaximalSplitTorus`
  (`Langlands.GroupScheme.Rational.SplitTorus`) and `relativeRoots`
  (`Langlands.GroupScheme.Rational.RelativeRoots`).
