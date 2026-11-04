# Semisimple split groups have roots spanning a subgroup of finite index

Worker 1391. This module proves the "only if" half of Milne Proposition 21.48
for the Library's actual-scheme conventions. It also states the "if" half as
an explicit proposition, `SplitSemisimpleOfFiniteRootIndexStatement`, and
proves that this proposition implies the published
`SplitSemisimpleRootDatumStatement` (module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`). It does not
prove the "if" half, so it does not prove `SplitSemisimpleRootDatumStatement`.

## The lattice lemma

`Submodule.exists_dual_ne_zero_of_infinite_quotient`: let `X` be a finitely
generated `ℤ`-module and `R` a submodule with `X ⧸ R` infinite. Then some
nonzero linear form `f : Module.Dual ℤ X` vanishes on `R`.

The Lean proof:

1. Let `t` be the torsion submodule of `Q = X ⧸ R`. If every element of `Q`
   were torsion, `Q` would be a finitely generated torsion abelian group,
   hence finite (`Module.finite_of_fg_torsion`). So some `q` lies outside `t`.
2. `Q ⧸ t` is finitely generated and torsion-free
   (`Submodule.QuotientTorsion.instIsTorsionFree`), hence free
   (`Module.free_of_finite_type_torsion_free'`).
3. The image of `q` in `Q ⧸ t` is nonzero. A free module is projective, so
   some linear form `g` on `Q ⧸ t` is nonzero on it
   (`Module.Projective.exists_dual_ne_zero`).
4. Take `f = g ∘ t.mkQ ∘ R.mkQ`. It vanishes on `R` and is nonzero at a lift
   of `q`.

## The "only if" theorem

`IsSemisimple.finite_quotient_rootSpan` assumes:

- `G` is semisimple over a field `k` (`IsSemisimple G`: connected reductive
  with a finite scheme-theoretic centre);
- `T` is a split torus and `i : T ⟶ G` is a closed subgroup
  (`IsClosedSubgroup i`);
- `P : RootDatum J (characterLattice T) (cocharacterLattice T)` satisfies
  `IsRootDatumOf i P`.

It concludes `Finite (characterLattice T ⧸ P.rootSpan ℤ)`. Maximality of `i`
is not needed, and neither is finiteness of `J`.

The Lean proof argues by contradiction:

1. The character lattice of a split torus is finitely generated
   (`IsSplitTorus.finite_characterLattice`). If the quotient is infinite, the
   lattice lemma gives a nonzero `f` vanishing on `P.rootSpan ℤ`.
2. The flipped pairing of `P` is perfect, so `f` is the pairing with a unique
   cocharacter `ν`, and `ν ≠ 0`. By `IsRootDatumOf` the pairing of `P` is
   `latticePairing T` and `Set.range P.root = roots i`, which equals
   `relativeRoots i` (`relativeRoots_eq_roots`). So `ν` pairs to zero with
   every relative root.
3. The Library theorem `rootAnnihilatorCentrality` (module
   `Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof`) then makes
   `groupHom ν ≫ i` central. The same theorem applied to the cocharacter `0`
   makes `groupHom 0 ≫ i` central. It needs `G` smooth, affine and connected,
   which follow from `IsConnectedReductive`.
4. Let `z : Z ⟶ G` be the finite centre representative from
   `hG.hasFiniteCenter`. Each central map has range in `center G`
   (`isCentral_iff_range_le_center`), so it factors through `z`
   (`SubgroupFunctor.IsRepresentedBy.liftOfLE` and `liftOfLE_comp`).
5. The map `q` from `Z` to the trivial group scheme is finite, because its
   underlying morphism is the structure morphism of `Z` (`Over.w`). `𝔾_m` is
   smooth, affine and connected (`isSplitTorus_gm`), and any two maps into the
   trivial group agree. Hence `finiteHom_cancel` (module
   `Langlands.GroupScheme.CentralIsogeny.Uniqueness`) shows that the two lifts
   to `Z` are equal. So `groupHom ν ≫ i = groupHom 0 ≫ i`.
6. `i` is a closed immersion, hence a monomorphism of schemes, so
   `groupHom ν = groupHom 0` (`cancel_mono`, `Grp.hom_ext`). Then `ν = 0`,
   which contradicts step 2.

## The "if" statement

`SplitSemisimpleOfFiniteRootIndexStatement.{u}` has the quantifiers and
hypotheses of the published `SplitSemisimpleRootDatumStatement.{u}`: a field
`k : Type u`, a connected reductive group `G` over `Spec k`, a split torus `T`
with a maximal torus `i : T ⟶ G`, and a root datum `P` with
`IsRootDatumOf i P`. It assumes in addition
`Finite (characterLattice T ⧸ P.rootSpan ℤ)` and concludes `IsSemisimple G`.

This is the "if" half of Milne Proposition 21.48, with Definition C.34 ("a
root datum (X, Φ, Φ^∨) is semisimple if ZΦ is of finite index in X"). The
definition is an internal packaging step. It adds no hypothesis that the
published statement lacks.

## The reduction theorems

- `splitSemisimpleRootSpan_of_finiteRootIndex`: the "if" statement implies
  `SplitSemisimpleRootSpanStatement.{u}`, the root form of the criterion
  (module `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanReduction`).
  The forward direction is `IsSemisimple.finite_quotient_rootSpan`, using the
  closed-subgroup clause `hi.2.1` of `IsMaximalTorus i`. The reverse
  direction is the hypothesis.
- `splitSemisimpleRootDatum_of_finiteRootIndex`: the "if" statement implies
  `SplitSemisimpleRootDatumStatement.{u}`. It composes the previous theorem
  with `splitSemisimpleRootDatum_of_rootSpan`, which derives the coroot form.

Every theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The universe `u` is arbitrary. Nothing restricts the field:
imperfect fields and positive characteristic are allowed. The centre is the
Library's full scheme-theoretic centre, nilpotents included.

## Provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Proposition 21.48 (printed p.439, PDF p.455): "A split reductive group is
  semisimple if and only if its root datum is semisimple." Milne's proof: "A
  reductive group is semisimple if and only if its centre is finite (19.10),
  and so this follows from Proposition 21.8."
- Proposition 21.8 (printed p.427, PDF p.443): the centre `Z(G)` is the
  intersection of the kernels of the roots, the diagonalizable subgroup of
  `T` with character group `X^*(T)/ZΦ`.

The Library's `IsSemisimple` is defined as connected reductive with finite
centre, which is the criterion Milne quotes from 19.10. The Lean proof of the
"only if" half differs from Milne's route. It does not identify the centre
with the intersection of the root kernels. It uses only one consequence of
21.8: a cocharacter that pairs to zero with every root is central (the
Library's `rootAnnihilatorCentrality`). It then shows that a nonzero
cocharacter cannot factor through a finite centre. The "if" half would need
the inclusion of the centre in `T`, which comes from the centralizer of a
maximal torus (the Library's `MaximalTorusCentralizerStatement`, which has
no Library proof). That half is left as the explicit hypothesis above.

The errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for
Proposition 21.8 or 21.48.
