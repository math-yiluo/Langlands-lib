# Involutivity on the actual rational-point family from its named inputs

Author: Worker 1180, task `2f01b264-fb0e-4029-901c-009044feaa97`.

This module specializes the general reduction of `InvolutivityReduction` to
the actual standard family `parabolic i ν`, `levi i ν`, `unipotent i ν` of
`RationalPoint k G.X` with its canonical point topology. It proves the
published `RationalInvolutivityStatement` from five named inputs: the
intersection statement `StandardLeviIntersectionStatement`, finite length
inside the standard Levis, the published
`RationalInductionCompatibilityStatement` (Theorem 1.7(2)), term
transitivity and the top term `i_S ∘ r_S = id`. It proves none of these five
inputs. It does not prove `RationalInvolutivityStatement` itself.

Three of the Levi-level premises of `RationalInductionCompatibilityStatement`
are derived here from the premises of `RationalInvolutivityStatement`: the
standard Levis are closed, the projections of the restricted decompositions
inside a Levi are continuous, and the restricted radicals are limits of
compact subgroups.

## Source and provenance

Aubert 1995 (registered source `aubert-1995-duality`, SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`),
proof of Theorem 1.7(3), printed p.2183 / PDF p.5. Aubert computes
`D_G² = ∑_{I⊆S} (-1)^{|I|} i_I ∘ D_{L_I} ∘ r_I` by Theorem 1.7(2), expands
`D_{L_I}`, uses transitivity of normalized induction and Jacquet restriction,
and concludes `D_G² = i_S ∘ r_S = id` because `∑_{K⊆I⊆S} (-1)^{|I|} = 0`
unless `K = S`. This module only routes the actual family through the
published general computation `involutivityStatement_of_inductionCompatibility`.

The three new propositions `RationalLeviFiniteLengthStatement`,
`RationalTermTransitivityStatement` and `RationalTopTermStatement` are
internal formulations (derived content). Each one names an input of Aubert's
computation for the actual family, with the premises of the published
rational targets. The point-set lemmas of the first section are elementary
topology. They are not in Aubert's text, where these properties of the Levi
subgroups are taken for granted.

## Levi premises

The compact-limit restriction and continuous-projection lemmas are reused from
`RestrictedLeviTopology`, preserving their published argument order. This module
adds Levi closedness and derives the remaining rational premises from them.

For a group `H` with a topology and a decomposition `h : P = M ⋉ U` of
subgroups of `H`:

- `IsSemidirectDecomposition.isClosed_levi`: if `H` is Hausdorff, `P` is
  closed and `h.projection : P →* M` is continuous, then `M` is closed. The
  proof writes `M` as the image in `H` of the set of points of `P` fixed by the
  projection. That set is closed in `P`, and the inclusion of the closed
  subgroup `P` is a closed map.
- `IsSemidirectDecomposition.coe_projection_subgroupOf`: if `hL` is a
  decomposition of `P.subgroupOf L` as `M.subgroupOf L ⋉ U.subgroupOf L` for a
  subgroup `L`, then its projection, read in `H`, is the ambient projection
  `h.projection`. The proof uses the uniqueness characterization
  `h.projection_eq_iff`.
- `IsSemidirectDecomposition.continuous_projection_subgroupOf`: the imported
  theorem transfers continuity through `subgroupOfToAmbient` using its embedding
  and the equality `projection_subgroupOf`.
- `isLimitOfCompactSubgroups_subgroupOf`: if `L` is closed and `U` is a limit
  of compact subgroups (every compact subset of `U` lies in a compact subgroup
  of `U`), then so is `U.subgroupOf L`. A compact subset `C` maps to a compact
  subset of `U`, which lies in a compact subgroup `K`. The preimage of `K`
  under the inclusion `U.subgroupOf L →* U` is a compact subgroup containing
  `C`, because that inclusion is inducing with closed range `U ∩ L`.

For the actual family, with the decompositions
`isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν`
and the premises `hP` (parabolics closed), `hproj` (projections continuous)
and `hUc` (radicals limits of compact subgroups) of
`RationalInvolutivityStatement`:

- `levi_isClosed`: every `levi i ν J` is closed, given
  `T2Space (RationalPoint k G.X)`.
- `continuous_standardLeviProjection`: for every
  `StandardLeviIntersectionStatement` proof `hInter`, every
  `standardLeviProjection i ν hInter hG hi hν J I` is continuous. This is the
  premise `hLproj` of `RationalInductionCompatibilityStatement`.
- `isLimitOfCompactSubgroups_leviUnipotent`: every
  `(unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)` is a limit of
  compact subgroups. This is the premise `hLUc`.

## Pointwise reduction

The section `Reduction` fixes the premises of `RationalInvolutivityStatement`
for one `k`, `G`, `T`, `i`, `ν`, together with `hInter` and the two
finite-length families `hiLFl`, `hrLFl` inside the Levis. These families are
stated on `levi i ν J` with the locally compact structure coming from
`levi_isClosed`.

- `standardLeviParabolicFiniteLength_of_premises J`: the published
  `standardLeviParabolicFiniteLength` with its premises `hM`, `hLproj` and
  `hLUc` supplied by the three lemmas above.
- `inductionCompatibilityStatement_of_rational hcompat`: a proof `hcompat` of
  the published `RationalInductionCompatibilityStatement`, applied with the
  derived Levi premises, is the general `InductionCompatibilityStatement` of
  the actual family. The `Fintype` instance on `SimpleRoot i ν` is
  `simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν`, the one used by
  `rationalAlternatingOperator`.
- `rationalAlternatingOperator_comp_self hcompat htrans htop`: if `htrans` is
  the published `TermTransitivityStatement` of the actual family with these
  Levi data and `htop` states `alternatingTerm … Finset.univ = LinearMap.id`,
  then `D.comp D = LinearMap.id` for
  `D = rationalAlternatingOperator i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots`.
  The proof is `involutivityStatement_of_inductionCompatibility` applied to
  `inductionCompatibilityStatement_of_rational hcompat`, `htrans` and `htop`.

## Named inputs

Each of the following is a `Prop`. It declares a target and proves no
instance. The quantifier block is that of `RationalInvolutivityStatement`
(the field `k`, `G`, `hG`, `T`, `i`, `hi`, the instances on the point topology,
`ν`, `hν`, `hStandard`, `hU`, `hP`, `hproj`, `hUc`, `hiFl`, `hrFl`), with the
changes listed.

- `RationalLeviFiniteLengthStatement`: the root-system hypothesis `hRoots` is
  dropped. The binders `hInter` and `hM : ∀ J, IsClosed (levi i ν J)` are
  added. The conclusion is that for every `J` and `I : Finset J`, on
  `levi i ν J` with the locally compact structure from `hM J`, the normalized
  induction functor and the normalized Jacquet functor of
  `isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I` (with radical
  closedness `(hU (leviIndex J I)).preimage continuous_subtype_val`) preserve
  finite length. These are the premises `hiLFl` and `hrLFl` of
  `RationalInductionCompatibilityStatement`. The premises `hP`, `hproj`,
  `hUc`, `hiFl` and `hrFl` do not occur in the conclusion, so their binder
  names start with an underscore. They are kept because the expected proof
  uses them: finite length inside a Levi should follow from finite length of
  the ambient functors through induction and Jacquet restriction in stages,
  and the stage isomorphisms need the topological premises. Keeping them
  makes the statement weaker, never stronger.
- `RationalTermTransitivityStatement`: the binders are those of
  `RationalInductionCompatibilityStatement`, except that `hRoots` is replaced
  by an arbitrary instance `[Fintype (SimpleRoot i ν)]`, placed last. The
  conclusion is the published general `TermTransitivityStatement` of the
  actual family with the Levi data
  `fun J => standardLeviParabolicFiniteLength i ν hInter hG hi hν hU hP J (hM J) (hLproj J) (hLUc J) (hiLFl J) (hrLFl J)`,
  that is, `i_J ∘ i^{L_J}_I ∘ r^{L_J}_I ∘ r_J = i_{leviIndex J I} ∘ r_{leviIndex J I}`
  as endomorphisms of the exact finite-length Grothendieck group of
  `RationalPoint k G.X`.
- `RationalTopTermStatement`: the binders are those of
  `RationalInvolutivityStatement`, except that `hRoots` is replaced by an
  arbitrary instance `[Fintype (SimpleRoot i ν)]`, placed last. The conclusion
  is `alternatingTerm … Finset.univ = LinearMap.id` for the actual family,
  that is, `i_S ∘ r_S = id`.

The last two take a `Fintype` instance instead of `hRoots` because the
root-system hypothesis enters only through the finiteness of the simple
roots. `Fintype` is a subsingleton, so stating them for every instance is
equivalent to stating them for the instance from `hRoots`. The closing
theorem instantiates them with that instance.

## Closing reduction

`rationalInvolutivityStatement_of_reductions hInter hLeviFl hcompat htrans htop`
proves `RationalInvolutivityStatement.{u, v}` from

- `hInter : StandardLeviIntersectionStatement.{u}`,
- `hLeviFl : RationalLeviFiniteLengthStatement.{u, v}`,
- `hcompat : RationalInductionCompatibilityStatement.{u, v}`,
- `htrans : RationalTermTransitivityStatement.{u, v}`,
- `htop : RationalTopTermStatement.{u, v}`.

The proof introduces the premises of `RationalInvolutivityStatement`. It sets
the `Fintype` instance from `hRoots` and obtains `hiLFl`, `hrLFl` from
`hLeviFl` with `hM := levi_isClosed …`. It instantiates `htrans` with the
derived `hLproj`, `hLUc` and these finite-length families, instantiates
`htop`, and applies `rationalAlternatingOperator_comp_self`.

All proofs are complete. They use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

No premise about involutivity, the geometric lemma, Weyl conjugacy, or
composition of the alternating operators is assumed. The five inputs of the
closing theorem are separate obligations:

- `StandardLeviIntersectionStatement` follows from `hStandard` and
  `StandardParabolicOrderStatement` by the published
  `standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder`.
- `RationalInductionCompatibilityStatement` is Theorem 1.7(2).
- Term transitivity needs transitivity of normalized induction and
  normalized Jacquet restriction for the actual nested standard parabolics.
- The top term needs `parabolic i ν univ = ⊤` and `unipotent i ν univ = ⊥`.
- Finite length inside the Levis is described above.
