# Assembly of rational containment in pseudo-parabolic subgroups

Worker 1392 implemented this conditional reduction for the proof task of
`SplitTorusIntoPseudoParabolicStatement`.

`SplitTorusIntoPseudoParabolicReductionStatement` is the conditional
proposition

```text
SmoothSubgroupQuotientExistenceStatement →
  PseudoParabolicSubgroupStructureStatement →
    PseudoParabolicQuotientPseudoCompleteStatement →
      SplitSolvablePseudoCompleteFixedPointStatement →
        PseudoParabolicQuotientRationalLiftingStatement →
          SplitTorusIntoPseudoParabolicStatement.
```

Each proposition occurs at the same arbitrary universe `u`. All six are
unchanged published propositions, imported from their own modules. This
implication records precisely which five component proofs the split-torus
target needs. The module also proves the implication, in
`splitTorusIntoPseudoParabolicReduction`. It does not prove any of the five
prerequisite propositions, nor the unconditional target.

## Route

The route is the proof of CGP Lemma C.2.2 (Conrad, Gabber and Prasad,
*Pseudo-reductive groups*, second edition, Section C.2, p. 593, PDF page 619):
let `H` act on `G/P` by left translation; by Propositions C.1.6 and C.1.5
there is a rational point `x` of `G/P` fixed by `H`; by Lemma C.2.1 it lifts
to some `g ∈ G(k)`; then `HgP ⊆ gP`, that is `g⁻¹Hg ⊆ P`. In the Library these
steps are the five explicit prerequisite propositions, and this module only
assembles them.

## Declarations

`fixedCoset_of_isFixed` is a general lemma over an arbitrary base scheme `S`.
Let `q : G.X ⟶ Q` identify two points `a, b : T ⟶ G.X` on every test exactly
when `a⁻¹ * b` lies in a subgroup functor `A`, with `q.left` quasi-compact,
flat and surjective, and let
`Dynamic.flagQuotientSchemeAction` be the left translation action of `G` on
`Q`. If the composite `g ≫ q` of a rational point `g` of `G` is fixed, on all
tests, by the restriction of this action along `j : H ⟶ G`, then for every
test `T` and every `h : T ⟶ H.X`, the points `j(h) · g` and `g` (pulled back
to `T`) have the same image under `q`.
This is exactly the fixed-coset hypothesis of the published
`factorOfFixedCoset`. The proof evaluates the fixed-point condition at the
point `h` over `T` and rewrites with `flagQuotientSchemeAction_act_lift`, which
computes the action of `j(h)` on `g ≫ q` as `(j(h) · g) ≫ q`.

`splitSolvableIntoPseudoParabolic_of_components` derives the published
general `SplitSolvableIntoPseudoParabolicStatement` (CGP Lemma C.2.2) from the
five prerequisites. For a field `k`, a smooth connected affine `G`, a
pseudo-parabolic inclusion `i : P ⟶ G` and a split-solvable closed subgroup
`j : H ⟶ G`:

1. The structure proposition gives smoothness of `P`.
2. Quotient existence, applied to the closed subgroup `i`, supplies an actual
   separated, locally finite type and quasi-compact `Q` and a smooth,
   surjective, quasi-compact `q : G.X ⟶ Q` that identifies `a` and `b` on
   every test exactly when `a⁻¹ * b` lies in the range of `i`.
3. The pseudo-completeness proposition applies to this same `Q` and `q`.
4. The fixed-point proposition, applied to `H`, to `Q`, to the rational point
   `quotientIdentityPoint q` (which shows `Q` has a rational point) and to the
   left translation action restricted along `j`, gives a rational point `x`
   of `Q` fixed on all tests.
5. Rational lifting writes `x = g ≫ q` for a rational point `g` of `G`.
6. `fixedCoset_of_isFixed` turns the fixed point into the fixed-coset
   hypothesis. Both `i` and `j` are closed immersions, hence monomorphisms,
   so `factorOfFixedCoset` gives an actual homomorphism `f : H ⟶ P`, and
   `factorOfFixedCoset_comp` gives `f ≫ i = j ≫ (G.innerIso g⁻¹).hom`.

The conjugator returned is therefore `g⁻¹`, not `g`. Since `innerIso c` acts
by `x ↦ c x c⁻¹`, `innerIso g⁻¹` acts by `x ↦ g⁻¹ x g`, which matches CGP's
`g⁻¹Hg ⊆ P`.

`splitTorusIntoPseudoParabolic_of_splitSolvableIntoPseudoParabolic` specializes
the general statement to the source `S.toGrp` of a split subtorus
`j : S.toGrp ⟶ G`. The predicate `IsSplitSubtorus j` supplies a closed
subgroup and a split torus `S`. The published
`IsSplitTorus.isSplitSolvableGroupScheme` shows that a split torus is split
solvable. The rational conjugator and the actual factorization through the
same `i` are passed through unchanged.

`splitTorusIntoPseudoParabolic_of_components` composes the two preceding
theorems. `splitTorusIntoPseudoParabolicReduction` states that this
composite proves `SplitTorusIntoPseudoParabolicReductionStatement`.

## Scope

This is derived content. CGP states Lemma C.2.2 but no conditional form of
it: the implication follows the four steps of its proof, and the split-torus
specialization follows the use of Lemma C.2.2 for a `k`-split torus in the
proof of CGP Theorem C.2.3 (p. 594, PDF page 620). The only new arguments are the
fixed-coset translation and the assembly of existing interfaces. The source
provenance of each prerequisite is recorded in its own statement module, and
the geometric, pseudo-completeness, fixed-point and lifting proof obligations
remain unchanged. Pseudo-completeness of `G/P` is assumed as stated, not
replaced by properness. Rational points of the quotient are lifted only
through the explicit lifting hypothesis, not deduced from the quotient map.
No field restriction, maximality assumption or universe change is
introduced, and no imported Lean or Markdown file is changed.
