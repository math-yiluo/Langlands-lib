# Proof of nonzero compact standard maps into actual mirabolic subrepresentations

Author: Worker 237.

This module proves `Langlands.Whittaker.mirabolicNonzeroCompactMap`, of type
`MirabolicNonzeroCompactMapStatement.{uF}` from
`Langlands.Representation.Whittaker.MirabolicCompactCopyStatement`. The statement
is the existential compact-copy input in the proof of Bernstein–Zelevinsky
(1976), Proposition 5.15(c), printed pp.49–50. Take every prime `p`, every
`F : PadicField.{uF} p` with its canonical topology, every `n : ℕ` (matrix rank
`n + 1`, so rank one is included), every bundled unitary additive character `ψ`,
and every actual subrepresentation `W` of `mirabolicSmoothInduced ψ n` with
`W ≠ ⊥`. Then some intertwiner
`A : (mirabolicCompactInduced ψ n).IntertwiningMap W.toRepresentation` has
`A ≠ 0`.

The theorem has exactly the target type. It adds no hypothesis, and its axioms
are `propext`, `Classical.choice` and `Quot.sound`.

## Conventions

All objects are the ones the target uses, from
`Langlands.Representation.Whittaker.MirabolicModels`:

- `mirabolic n F` is the last-row mirabolic group in `GL_(n+1)`.
- `Mirabolic.upperUnipotent n F` is its full upper unitriangular subgroup `U`.
- `mirabolicCharacter ψ n` is the positive adjacent-entry character
  `u ↦ ∏ ψ(u_(i,i+1))`.
- The smooth induction `mirabolicSmoothInduced ψ n` has the unnormalized
  covariance `f(u g) = Θ(u) f(g)` and right translation `(s · f)(g) = f(g s)`
  (BZ76 §§2.21–2.22, printed pp.21–22).
- `mirabolicCompactSubrepresentation ψ n` is the subrepresentation of members
  whose projected nonzero support in `U \ P` is compact.
- `mirabolicCompactInduced ψ n` is, by definition, that subrepresentation's own
  representation.
- `mirabolicCompactInclusion ψ n` is the subtype inclusion.

The proof works inside these models throughout. There is no normalization,
modular character, change of character, change of rank or change of support
condition to compare. The compact model, the compact subrepresentation and the
inclusion all use the same character `Θ`, the same group `U` and the same notion
of compact projected support.

## Route

**Source route.** On printed p.50, BZ76 proves 5.15(c) as follows. A nonzero
`π ⊆ τ_P = Ind(P, U, Θ)` is nondegenerate, so its completely nondegenerate part
`π^nd` is nonzero (§5.15, pp.48–49). That part is a direct sum of copies of
`τ_P⁰ = ind(P, U, Θ)`, which gives a nonzero map `τ_P⁰ → π`. The source reaches
this through the derivative theory of §§5.11–5.14.

**Implemented route.** The Lean proof uses no derivatives. It deduces the target
from the already-published compact-minimality theorem
`Langlands.Whittaker.mirabolicCompactMinimality` (module
`Langlands.Representation.Whittaker.MirabolicMinimalityProof`, Worker 806). That
theorem proves `MirabolicCompactMinimalityStatement.{uF}`: every nonzero `W`
contains `mirabolicCompactSubrepresentation ψ n`. Its proof is a direct induction
on rank with explicit functions, and it does not use the present target (see the
dependency audit below). Task revision 2 of
`da9ca5b2-6b4d-4df3-ae19-1c7aa4b5c0d7` explicitly allows this input.

## Lean proof

Section `Generic` works over a field `K` with a topological ring structure.

1. `MirabolicCompactCopy.compactInclusionInto ψ n W hW` takes `W` and a proof
   `hW` of `mirabolicCompactSubrepresentation ψ n ≤ W`. It is the linear map
   `LinearMap.codRestrict` of `mirabolicCompactInclusion ψ n` into
   `W.toSubmodule`. A compact member `f` lies in the compact subrepresentation by
   its own `f.property`, so `hW` sends it into `W`. Both actions are right
   translation of the same underlying function, so the intertwining identity
   holds by `rfl` after extensionality. `compactInclusionInto_apply` records that
   the underlying smooth function of the image of `f` is `f.val`.
2. `MirabolicCompactCopy.characterRepresentation_smooth` assumes
   `NonarchimedeanGroup (mirabolic n K)`. It proves that the scalar
   representation `mirabolicCharacterRepresentation ψ n` of `U` is smooth. The
   kernel of the continuous character `mirabolicCharacterContinuous ψ n` is open
   by `Langlands.isOpen_ker_of_continuous_complex_character`. Here `U` inherits
   the nonarchimedean property through `Langlands.subgroupNonarchimedean`. This
   kernel fixes every scalar.
3. `MirabolicCompactCopy.exists_compactEval_one_ne_zero` additionally assumes
   `WeaklyLocallyCompactSpace (mirabolic n K)`. It applies
   `Induction.compactLocalSection` at the identity, with value `1 : ℂ` and the
   open set `Set.univ` of `U \ P`. This gives a compactly induced function. By
   `Induction.compactLocalSection_apply`, its value at `1` is `1 ≠ 0`.
4. `MirabolicCompactCopy.compactInclusionInto_ne_zero`: suppose the corestricted
   map is zero. Then the underlying smooth function `f.val` of the section from
   step 3 is zero, so its value at `1` is zero, which is a contradiction.

Steps 2 and 3 repeat a short argument that also appears in
`MirabolicFunctionalMultiplicityProof`. They are proved again here because the
task excludes importing that downstream functional-multiplicity module.

The final theorem `mirabolicNonzeroCompactMap` introduces `p`, the prime
certificate and `F`. It installs the canonical topology, valuative relation,
local-field structure and Hausdorff property from `F.canonicalTopologicalData`.
The binder telescope then matches the target, whose `IsTopologicalRing`
certificate is a proposition. After introducing `n`, `ψ`, `W` and `hW : W ≠ ⊥`,
it supplies three instances:

- `NonarchimedeanGroup (GeneralLinear (n + 1) F.Carrier)` from
  `Langlands.valuativeGeneralLinearNonarchimedean`;
- local compactness of `GeneralLinear (n + 1) F.Carrier` from
  `F.canonicalTopologicalData.generalLinearLocallyCompactSpace`;
- local compactness of the closed subgroup `mirabolic n F.Carrier` from
  `GeneralLinear.Mirabolic.locallyCompactSpace`.

The mirabolic group inherits the nonarchimedean property as a subgroup, and
weak local compactness follows from local compactness. The theorem then takes
`hmin := mirabolicCompactMinimality p hp F n ψ W hW` and returns
`⟨compactInclusionInto ψ n W hmin, compactInclusionInto_ne_zero ψ n W hmin⟩`.

## Dependency audit

The module imports these Library modules:

- the target statement module;
- `Whittaker.MirabolicMinimalityProof`;
- `Induction.CompactLocalSection`;
- `Twist.ContinuousCharacterProof`;
- `Topology.Nonarchimedean.Subgroup`;
- `Group.GL.Nonarchimedean`;
- `Group.GL.Padic`.

Its transitive `Langlands` import closure has 68 modules. The import closure of
`MirabolicMinimalityProof` has 66 modules. Neither closure contains:

- any module named `MirabolicFunctionalMultiplicity*`, which holds the
  downstream irreducible functional multiplicity;
- `MirabolicCompactHomStatement`, the scalar-Hom uniqueness target;
- any proof of this target.

The only module in this module's own closure whose name matches these patterns
is the target statement module itself, which contains only the proposition. The
minimality proof's own dependency on
`Whittaker.MirabolicCompactWhittakerUniqueness` is that proof's input. It is not
scalar-Hom uniqueness or functional multiplicity.

The parent's canonical-image conclusion and the scalar-Hom statement are not
used.

## Source

Bernstein, I. N.; Zelevinsky, A. V. *Representations of the group GL(n, F)
where F is a non-archimedean local field.* Russian Math. Surveys 31:3 (1976),
1–68. Registered as `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

- §5.15 and Proposition 5.15(b),(c), printed pp.48–49.
- The proof of 5.15(c), printed p.50.
- Unnormalized induction, §§2.21–2.22, printed pp.21–22.
