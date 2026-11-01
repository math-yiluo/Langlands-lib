# The actual geometric lemma in exact finite-length K0

Authors: Worker 320 (proof implementation), Worker 585 (integration and verification).

This module proves the published proposition
`Langlands.Geometric.GeometricLemmaGrothendieckStatement.{uF,uV} F T`.
Its exported theorem is
`Langlands.Geometric.geometricLemmaGrothendieck`, with outer parameters
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
For every positive rank and ordered block shapes `B C`, it obtains uniform
geometric refinements and an enumeration of all actual minimal
double-coset representatives. For every actual finite-length smooth complex
representation `A` of the source Levi, it derives finite length of every
actual smooth geometric piece and proves

```text
normalizedJacquetK0(C)(normalizedInductionK0(B)([A]))
  = sum_i [geometricPieceSmoothFunctor(e(i))(A)].
```

The implementation specializes the actual `padicGeometricLemma` to the
saturated carrier universe `max uF uV`. Its witnesses provide the same source
and target refinements, all intersection equalities, and finite enumeration
for every input representation. These witnesses are chosen before the
proof introduces `A` or its finite-length certificate.

The local functor `J` is the actual normalized parabolic induction from
`B` followed by the actual normalized Jacquet functor for `C`. The local
family `P` consists of the existing `geometricPieceSmoothFunctor` values
for the chosen representatives and refinements. The theorem
`CuspidalSupport.geometricPieceSmoothFunctor_toRep`, together with functor
associativity and the definition of `jacquetInductionFunctor`, identifies
`J ⋙ SmoothRep.toRep` and the forgotten `P` family with the actual natural
gluing supplied by `padicGeometricLemma`. Thus the application uses the
given representation actions and actual natural filtration.

Actual normalized induction preserves finite length, as does actual normalized
Jacquet restriction. The proof obtains certificates `hI` and `hJ` from
`Parabolic.normalizedInductionK0_hasFiniteLength` and
`Parabolic.normalizedJacquetK0_hasFiniteLength`. It applies
`SmoothRep.filtrationGrothendieckStatement` to `J`, `P`, the actual gluing,
and `hJ`. That published generic theorem derives finite length of each
filtration step and piece through the actual injective inclusions and
surjective graded quotient maps. Its adjacent actual short exact sequences
telescope to the class sum; its finite permutation argument retains the
original representative indexing. The returned piece certificates supply
the target's existential `hP`.

Finally the proof rewrites the two published generator formulas
`Parabolic.normalizedInductionK0_finiteLengthClass` and
`Parabolic.normalizedJacquetK0_finiteLengthClass`, using the same `hI` and
`hJ`. Their left sides are the actual named K0 maps in the target, and
their right sides are the class of `J.obj A` occurring in the generic
filtration equality. This completes the displayed formula.

The class group is the existing exact finite-length smooth Grothendieck
quotient by all actual short exact sequences, including nonsplit ones.
Finite length means finite group-algebra length. No finite-dimensionality,
admissibility, irreducibility, piece-length, splitting, or theorem-valued
premise is added.

The proof preserves independent field and carrier universes and the target's
positive-rank hypothesis. It proves an equality of exact Grothendieck classes
and supplies uniform geometric witnesses. All carriers remain in
`Type (max uF uV)`, so composing the actual functors does not enlarge the
carrier universe. It installs the supplied topology `T.topology` and
retains upper ordered block parabolics, positive half-modulus covariance
and right translation for induction, and the existing inverse half-modulus
normalized Jacquet coinvariants. Rank zero remains outside this theorem.

This is an internal algebraic derivation from the published actual
geometric-lemma construction, smooth forgotten-functor comparison,
finite-length preservation, generic filtration additivity and K0
generator formulas. It reuses Worker 320's complete implementation.
No new original-literature assertion is transcribed; the source
correspondence of the underlying actual geometric lemma remains in its
published statement and proof Markdown. The target pair and its imported
pairs are reused unchanged. No Aubert identity, irreducible-image
theorem, analytic segment classification or exhaustion result is used.
The conclusion supplies a class equality and no natural splitting.
