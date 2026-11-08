# Renard VI.7.5, Theorem, from explicit inputs

Module `Langlands.Representation.Exponents.LeviInductionFiniteTypeReduction`.

## Purpose and scope

The target `LeviInductionFiniteTypeStatement` (Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 version, VI.7.5, Theorem, printed p.187 / PDF p.193)
says: for every actual rational parabolic `P = MU` of a connected reductive `G` over a
nonarchimedean local field, normalized induction `i_P^G` sends smooth representations of
`M(F)` that are finitely generated over `ℂ[M(F)]` to representations finitely generated
over `ℂ[G(F)]`.

This module proves the theorem `leviInductionFiniteType_of_inputs`, which derives the
target from five inputs, each an explicit premise:

1. `hProp : SmoothRepNoetherianCategoryStatement.{u, max u v}`: the VI.7.5 Proposition,
   at carrier universe `max u v`;
2. `hGeom : RepresentedGeometricLemmaStatement.{u, v}`: the represented geometric lemma
   (VI.5.1);
3. `h1 : LeviJacquetFiniteTypeStatement.{u, v}`: Renard VI.1.3, Jacquet modules of
   finite-type representations are of finite type;
4. `h2 : RepresentedCuspidalRemainderSplittingStatement.{u, max u v}`: the objectwise
   splitting of every smooth representation into a supercuspidal part and a part with no
   nonzero supercuspidal subquotient (from VI.3.5);
5. `h4 : FiniteProperParabolicSupercuspidalTestStatement.{u, max u v}`: for every `G`,
   finitely many proper actual rational parabolics test supercuspidality. This statement
   is defined in `Exponents/SmoothRepNoetherianReduction.lean`.

None of the five is proved here, so this is a conditional reduction: it does not discharge
the target. With the reduction `smoothRepNoetherianCategory_of_inputs` of the
Proposition (module `Exponents/SmoothRepNoetherianReduction`), applied at universe
`max u v`, both VI.7.5 targets reduce to Renard VI.1.3,
the splitting, the supercuspidality test, `SupercuspidalFiniteTypeNoetherianStatement` and
the geometric lemma.

The route differs from Renard's proof. Renard reduces to standard parabolics and uses the
VI.7.2 embedding into inductions of supercuspidals, the faithful functor `R` and VI.5.3.
Here the proof runs by strong induction on the Lie dimension of `G`. It uses the finite
family of functors of `smoothRepNoetherianCategory_of_inputs`: the supercuspidal part, and
the normalized Jacquet functors along finitely many proper parabolics. Neither standard
parabolics nor the VI.7.2 embedding appear.

## Proof outline

Let `ρ` be finitely generated on `M(F)`, and write `X = i_P^G(ρ)`.

- If `p` is an isomorphism (`P = G`), the published equivalence
  `fullParabolicLeviInductionEquiv` identifies `X` with `ρ` pulled back along
  `M(F) ≃ G(F)`. Pullback along a surjection preserves finite generation.
- Otherwise `P` is proper. The finite family consists of the supercuspidal-part functor
  and the Jacquet functors `r_{Q_j}` along the proper parabolics `Q_j = L_j U_j` supplied
  by `h4`. It jointly reflects isomorphisms between monomorphisms
  (`familyFunctor_jointlyReflectsMonoIsos`), so `X` is a Noetherian object once every
  member applied to `X` is one (`noetherianObject_of_finite_family`).
  - Supercuspidal part. VI.5.2 (`LeviInductionNoSupercuspidalSubquotientStatement`) is
    derived from `h2` by the published
    `leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting`. It says that
    no irreducible subquotient of `X` is supercuspidal. If the supercuspidal part of `X`
    were nonzero, it would have an irreducible subquotient, and that subquotient would be
    supercuspidal and a subquotient of `X`. So the supercuspidal part is zero, hence
    Noetherian.
  - Jacquet members. By the geometric lemma, `r_{Q_j}(X)` is glued from finitely many
    pieces `i^{L_j}_{Q'}(ι(r^M_{P'} ρ))`. Each piece is finitely generated: by VI.1.3 for
    `r^M_{P'}`, by pullback along the conjugation `ι`, and by the induction hypothesis for
    `L_j`. The Levi of a proper parabolic has smaller Lie dimension (`lieDimension_levi_lt`).
    By the Proposition for `L_j`, each piece is Noetherian, and hence so is `r_{Q_j}(X)`.
- Hence `X` is Noetherian, so `X` is finitely generated.

## Declarations

### Generic (namespace `Langlands.NoetherianRepresentation`)

- `of_repFunctorFiltration`: let `s` be a published `RepFunctorFiltration F n` of a functor
  `F : C ⥤ Rep k G`, and `X` an object. If every graded piece `(s.graded i).obj X` is
  Noetherian over `k[G]`, then `(F.obj X)` is Noetherian. Proof: evaluate the steps at `X`
  to get an `ObjectRepFiltration` (`ofSubrepresentations`), whose graded pieces are the
  same, and apply `of_objectRepFiltration` (module `Category/NoetherianClosure`).
- `of_isGluedFrom`: the same conclusion when `F` is glued (`IsGluedFrom`) from finitely
  many functors `pieces` and every `(pieces i).obj X` is Noetherian. Proof: the graded
  pieces are naturally isomorphic to the permuted pieces, and the component at `X` gives
  an equivalence of representations (`Representation.equivOfIso`).
- `finite_comp_surjective_iff`: for a surjective monoid homomorphism `f : H →* G`,
  `ρ.asModule` is finitely generated over `k[G]` if and only if `(ρ.comp f).asModule` is
  finitely generated over `k[H]`. Proof: the order isomorphism `compSubmoduleOrderIso` of
  submodule lattices sends the `k[G]`-span of a set of vectors to its `k[H]`-span and sends
  `⊤` to `⊤`.

### Represented parabolics (namespace `Langlands.Aubert.General.RepresentedParabolic`)

- `LeviInductionFiniteTypeAt k G hG` (definition): the body of
  `LeviInductionFiniteTypeStatement` with the field `k` and the connected reductive group
  `G` fixed, retaining all remaining quantifiers and instances.
  `leviInductionFiniteTypeStatement_iff` (by `Iff.rfl`): the statement is this predicate
  for all `k` and `G`.
- `leviInduction_finite_of_isIso`: if `p` is an isomorphism, `i_P^G(σ)` is finitely
  generated whenever `σ` is. This is the `P = G` case above.
- `GeometricLemmaIntersectionDatum.finite_pieceFunctor_obj`: for a geometric-lemma datum
  `D` at a point `z`, VI.1.3 (`hJ`) and the Theorem for `L` (`hL`) together make
  `D.pieceFunctor.obj ρ` finitely generated over `ℂ[L(F)]` whenever `ρ` is finitely
  generated. This is the piece computation above, with the arguments `D.P'`, …, `D.e`.
- `leviJacquet_leviInduction_isNoetherian_of_geometricLemma`: for actual rational
  parabolics `P = MN` and `Q = LU` and a finitely generated `ρ`, `r_Q^G(i_P^G ρ)` is
  Noetherian over `ℂ[L(F)]`. Premises: the geometric lemma, VI.1.3, the Theorem for `L`,
  and `hNoethL`, which says that finitely generated smooth representations of `L(F)` in
  carrier universe `max u v` are Noetherian. Proof: `of_isGluedFrom` with the previous
  lemma.
- `isZero_cuspidalPartFunctor_obj_leviInduction`: assume VI.5.2, a splitting `hs` for
  every smooth representation of `G(F)` in universe `max u v`, and `¬ IsIso p`. Then the
  supercuspidal part `(cuspidalPartFunctor hs).obj (i_P^G ρ)` is a zero object. Proof:
  as in the outline, using `exists_isIrreducible_isSubquotient_of_nontrivial`,
  `IsSupercuspidal.of_isSubquotient`, and the monomorphism `cuspidalPartι`.
- `leviInductionFiniteTypeAt_of_levis`: the inductive step. Given the five inputs and
  the Theorem for the Levi of every proper parabolic of `G`, the Theorem holds for `G`.
- `leviInductionFiniteType_of_inputs`: the reduction stated above, by strong induction
  on `Lie.dimension` with `lieDimension_levi_lt`, following
  `smoothRepNoetherianCategory_of_inputs`.

## Provenance

The reduction is derived. The mathematical steps are Renard's VI.1.3, VI.5.1, VI.5.2 and
VI.7.5 Proposition, combined in the order described above. Renard's own proof of the
VI.7.5 Theorem goes through VI.7.2 instead. The finite family, its joint reflection of
isomorphisms, the supercuspidality-test statement and the dimension induction are reused
from `Exponents/SmoothRepNoetherianReduction.lean` (Worker 1582). For this reuse, the
declarations `PointGroup`, `pointGroups`, `familyFunctor`,
`familyFunctor_preservesMonomorphisms` and `familyFunctor_jointlyReflectsMonoIsos` of that
module are made public; their statements and proofs are unchanged.
