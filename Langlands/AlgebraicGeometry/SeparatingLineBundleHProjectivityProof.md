# Proof of the very-ampleness criterion

Module `Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityProof`.

The theorem `Langlands.AlgebraicGeometry.separatingLineBundleHProjectivity`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityStatement.{u}`
of module `Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityStatement`.
The target and every imported Lean/Markdown pair are unchanged.

## Statement and scope

For every `K : Type u` with `[Field K]` and `[IsAlgClosed K]`, every
`X : Scheme.{u}`, every `p : X ⟶ Spec (CommRingCat.of K)` and every line
bundle `L : Picard.LineBundle X`, if `p` is proper and
`Picard.SeparatesPointsAndTangents p L` holds, then `IsHProjective p`: there
are `n : ℕ` and a closed immersion `i : X ⟶ ProjectiveSpace K n` with
`i ≫ projectiveSpaceToSpec K n = p`.

The theorem has no outer hypotheses, and the universe `u` is arbitrary. It
covers every characteristic of `K`, the empty scheme, schemes of dimension
zero, and non-reduced, reducible or disconnected `X`. It does not use
finite-dimensionality of `Γ(X, L)`, ampleness, or any ample-existence or
downstream projectivity result.

## Published inputs

The helper `separatingLineBundleHProjectivity_of` takes three published
statements as hypotheses `hA`, `hB` and `hC`. The final theorem instantiates
them with these published proofs, each at universe `u`:

| Input | Theorem | Module |
| --- | --- | --- |
| `hA : FiniteSeparatingSectionsStatement` | `Langlands.AlgebraicGeometry.finiteSeparatingSections` | `Langlands.AlgebraicGeometry.FiniteSeparatingSectionsProof` |
| `hB : LinearSystemMorphismStatement` | `Langlands.AlgebraicGeometry.linearSystemMorphism` | `Langlands.AlgebraicGeometry.LinearSystemMorphismProof` |
| `hC : ProperRationalImmersionClosedImmersionStatement` | `Langlands.AlgebraicGeometry.properRationalImmersion_isClosedImmersion` | `Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionProof` |

- `hA`: on a proper scheme over an algebraically closed field, a line bundle
  satisfying `SeparatesPointsAndTangents` has finitely many global sections
  `s 0, …, s n` without common zero at any point of `X`, whose `K`-linear
  combinations `σ c = ∑ i, c i • s i` separate distinct rational points and
  nonzero rational tangent vectors. Scalars act through
  `Scheme.Modules.scalarsFromBase p`, and vanishing means
  `Picard.VanishesAlong`.
- `hB`: finitely many sections without common zero define a morphism
  `φ : X ⟶ ProjectiveSpace K n` over `Spec K`, with a vanishing dictionary:
  for rational points `x` and `y`, `x ≫ φ = y ≫ φ` holds exactly when every
  `σ c` vanishing along `x` vanishes along `y`; for a rational tangent vector
  `t` at `x`, `t ≫ φ = (dualNumberProjection K ≫ x) ≫ φ` holds exactly when
  every `σ c` vanishing along `x` vanishes along `t`.
- `hC`: a proper morphism between schemes locally of finite type over an
  algebraically closed field that is injective on rational points and on
  rational tangent vectors is a closed immersion.

The companions of these modules explain their proofs.

## Implemented proof

Fix `K`, `X`, `p`, `L` with `IsProper p` and `SeparatesPointsAndTangents p L`.

1. `hA` gives `n`, `s`, base-point freeness `hbpf`, point separation `hpts`
   and tangent separation `htan` by the span.
2. `hB`, applied to `s` and `hbpf`, gives `φ` with
   `φ ≫ projectiveSpaceToSpec K n = p` and the two dictionary clauses `h1`
   and `h2`.
3. `φ` is proper. The composite `φ ≫ projectiveSpaceToSpec K n = p` is
   proper, and `projectiveSpaceToSpec K n` is proper (Library instance in
   `Langlands.AlgebraicGeometry.ProjectiveSpace.Structure`), hence separated,
   so Mathlib's `IsProper.of_comp` applies. Both `p` and
   `projectiveSpaceToSpec K n` are locally of finite type because they are
   proper.
4. `hC`, with `Y = ProjectiveSpace K n`, `q = projectiveSpaceToSpec K n` and
   `f = φ`, makes `φ` a closed immersion. Together with
   `φ ≫ projectiveSpaceToSpec K n = p` this is `IsHProjective p`. The two
   hypotheses of `hC` are checked by contradiction.
   - If rational points `x ≠ y` had `x ≫ φ = y ≫ φ`, then `hpts` gives `c`
     with `σ c` vanishing along `x` but not along `y`, while `h1` says every
     `σ c` vanishing along `x` vanishes along `y`.
   - If a rational tangent vector `t` at `x` had
     `t ≫ φ = (dualNumberProjection K ≫ x) ≫ φ` but
     `t ≠ dualNumberProjection K ≫ x`, then `t` is a nonzero tangent vector,
     and `htan` gives `c` with `σ c` vanishing along `x` but not along `t`,
     while `h2` says every `σ c` vanishing along `x` vanishes along `t`.
5. The final theorem `separatingLineBundleHProjectivity` applies the helper
   to `finiteSeparatingSections`, `linearSystemMorphism` and
   `properRationalImmersion_isClosedImmersion`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are
used.

## Provenance and authorship

This is the assembly step of the very-ampleness criterion that Milne recalls
from Hartshorne in the proof of Theorem 7.1 (*Abelian Varieties*, author
revision of 2022, pp.10–11, registered as
`milne-abelian-varieties-1986-author-2022`). Hartshorne's book is not
registered in the project literature and is cited only through Milne. The
split into the three inputs is internal to this project (derived
provenance). The finite separating family replaces the finite-dimensionality
of `Γ(X, L)` used in the expected proof recorded in the target's companion.
The closed-immersion criterion collects its finiteness and Nakayama steps.

Worker 898 wrote this module and its explanation. Worker 487 coordinated the
local and global closed-immersion criteria behind `hC`. The authors of the
imported proofs are recorded in their own companions.
