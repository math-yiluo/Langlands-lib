# The cuspidal constituent piece from product-Levi localization

Module: `Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentReduction`.

## Status

This is a **conditional** development for proof task
`bcd9ee7e-e8c0-4881-8f94-69c15c5dbed7`. It is submitted as a definition
record whose entry declaration is the definition
`Langlands.CuspidalInductionConstituent.fullTransportEquiv` (described in
step 3 below). The module's main content is the theorem

```
Langlands.glCuspidalInductionJacquetConstituent_of_localization
    (hloc : GLProductLeviCuspidalLocalizationStatement.{uF, uW, uV}) :
    GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uW}
```

It proves the target statement of task `bcd9ee7e` from the sibling Library
statement `Langlands.GLProductLeviCuspidalLocalizationStatement`, which is
the target of task `8ece4423-d91b-4230-81a0-28af86d62add`. Both statements are
in `Langlands.Representation.Exponents.WeylBranchPiecesStatement`. Once a proof
of the localization statement is published, the exact proof of
`GLCuspidalInductionJacquetConstituentStatement` is this theorem applied to it.
The hypothesis is the only premise. The theorem uses no filtration premise,
no `GLRelativeRegularComparisonStatement`, no regularity uniqueness, and no
Silberger 5.3/5.4 statement. It compiles with the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).

## Mathematical content

Let `ω` be an irreducible cuspidal representation of the flattened Levi of
`D.flatten R`, and let `ρ` be an irreducible cuspidal subquotient of the
inner opposite Jacquet module along `R'` of the inner normalized induction of
`ω` (both in flattened coordinates). This is the inner (product-Levi) form of
Bernstein–Zelevinsky's statement that the cuspidal constituents of a Jacquet
module of a cuspidal induction are Weyl conjugates of the inducing data
([BZ77, §2], a consequence of the geometric lemma 2.12, applied to the coarse
Levi of `D`).

1. **Localization.** By definition `middleInduced T D R ω` is
   `innerInduced T D R (Rep.of (ω.ρ.comp (flattenedLeviEquiv F D R).symm.toMonoidHom))`,
   so the hypothesis of the target is exactly the hypothesis of the
   localization statement with `B := D`, `Q := R`, `σ := ω`, `S' := R'`.
   Smoothness of `ω` is the first component of its admissibility, part of
   `IsLeviCuspidal`. The localization statement returns `g ∈ blockWeyl D`, a
   refinement `R''` of `C := D.flatten R`, a proof `hg` that `g` conjugates the
   Levi of `C.flatten R''` onto that of `D.flatten R'`, and `ρ` as a subquotient
   of the transport by `g` of `innerJacquet T C R'' ω`, pulled back along
   `flattenedLeviEquiv F C R''`.
2. **Proper refinements vanish.** If `refinedParabolic F C R'' ≠ ⊤`, then
   `refinedOppositeJacquet_subsingleton` shows that the opposite coinvariants
   `RefinedOppositeJacquetModule C R'' ω` are zero. The argument is the one
   used in the Library proof `leviCuspidalContragredient`: quasicuspidality
   (the second component of `IsLeviCuspidal`) applied to the reversed
   refinement `ProductLeviDualOpposite.reverseRefinement C R''` gives zero
   upper coinvariants. `Jacquet.coinvariants_conj_subsingleton_iff`
   conjugates them by `ProductLeviDualOpposite.reverseWeyl`, and
   `innerReverseRefinement_refinedUnipotent_map_conj` identifies the
   conjugated radical with the opposite refined radical. A zero
   representation has no subquotient onto a nonzero one
   (`not_isSubquotient_of_subsingleton`). An irreducible `ρ` is nonzero
   (`CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible`), so
   this case is impossible.
3. **The full refinement.** If `refinedParabolic F C R'' = ⊤`:
   - `refinedOppositeUnipotent_eq_bot_of_full`: the opposite refined radical
     is trivial. The reversed refinement is also full, its upper radical is
     trivial (`CuspidalSupport.refinedUnipotent_eq_bot_of_full`), and the
     reversal conjugation carries it to the opposite radical.
   - `flatten_leviSubgroup_of_full`: the embedded Levi of `C.flatten R''`
     equals that of `C`, because the refined Levi is everything
     (`refinedLevi_eq_top_of_refinedParabolic_eq_top`) and
     `flattenedLeviEquiv` is compatible with the embeddings. Hence
     `conjugatesLevi_of_full` turns `hg` into
     `hh : ConjugatesLevi C (D.flatten R') g`.
   - `flattenedLeviEquiv_leviConjugation_symm`: the two inverse
     conjugations agree after `flattenedLeviEquiv`. This follows from
     `leviConjugation_symm_embedding` and injectivity of
     `C.leviEmbedding`.
   - `fullOppositeJacquetLinearEquiv`: with a trivial radical, the quotient
     map `refinedOppositeJacquetMk` is a linear equivalence. Its inverse is
     `Jacquet.lift` of the identity.
   - `fullTransportEquiv`: this linear equivalence intertwines the transport
     of `ω` by `(g, hh)` with the transported inner Jacquet module. The
     normalizing character is the refined half modulus, which is `1` for a
     full refinement (`CuspidalSupport.refinedHalfModulus_eq_one_of_full`),
     and `normalizedRefinedOppositeJacquet_mk` reduces the action to `ω`.

   So `ρ` is a subquotient of `transport C (D.flatten R') g hh ω`, which is
   irreducible by `CuspidalSupport.isIrreducible_transport`. An irreducible
   subquotient of an irreducible representation is equivalent to it
   (`nonempty_equiv_of_isSubquotient`): the subrepresentation is `⊤`, and
   the composite surjection is a nonzero intertwining map between
   irreducible representations, hence bijective by Mathlib's
   `Representation.IsIrreducible.bijective_or_eq_zero`. The witness is
   `h := g` with `hh`.

## Helper declarations

All helpers are in namespace `Langlands.CuspidalInductionConstituent`:
`not_isSubquotient_of_subsingleton`, `nonempty_equiv_of_isSubquotient`,
`refinedOppositeUnipotent_eq_bot_of_full`, `flatten_leviSubgroup_of_full`,
`conjugatesLevi_of_full`, `flattenedLeviEquiv_leviConjugation_symm`,
`refinedOppositeJacquet_subsingleton`, `fullOppositeJacquetLinearEquiv`, and
`fullTransportEquiv`. They are internal lemmas about the Library's existing
definitions and introduce no new mathematical notion.

## Coordination

Workers 379 and 276 (task `8ece4423`) and Worker 253 (consumer task
`66ee5306`) agreed to this route. Task `8ece4423` is itself blocked on the
`GL_n` geometric lemma (task `67ebcf61`). Worker 1091, the other executor of
task `bcd9ee7e`, builds an independent conditional proof by the tensor route
(module `Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional`,
from `GLInducedOppositeJacquetCuspidalPieceStatement`). The two modules share
no declarations.

## Reference

[BZ77] I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. École Norm. Sup. (4) 10 (1977),
441–472 (registered source `bernstein-zelevinsky-1977-induced-i`): §2.12,
the geometrical lemma, printed p.448. This module states no result
of the source verbatim. It is an internal reduction between two Library
statements, and the source is cited only for the mathematical context.
