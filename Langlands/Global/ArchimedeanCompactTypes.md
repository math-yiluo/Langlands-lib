# Compact-type subspaces of the actual derivative smooth functions

Author: Worker 815.

The module `Langlands.Global.ArchimedeanCompactTypes` builds the right regular
representation of the actual archimedean general linear group on
`DerivativeSmoothFunctions K n`, with the derivative compact-open topology. It
restricts that action to the actual standard compact subgroup and defines
algebraic isotypic spans of finite-dimensional continuous compact
representations inside it. It works for every `K : Type u` with
`[Field K] [NumberField K]` and every natural rank `n`, including zero. It
imports `ArchimedeanSmoothTopology`, `ArchimedeanSmoothActionContinuityProof`,
`ArchimedeanCompact`, the published
`Representation.CompactCoefficient.AdmissibleComplement`, and Mathlib's
`RepresentationTheory.Irreducible`. Unless stated otherwise, every
declaration below is in `Langlands.Global.ArchimedeanGL.DerivativeSmoothFunctions`.

Write `G = Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`,
`Kₙ = standardInfiniteCompact K n` (a subgroup of `G`), and `T = toSmooth K n`.
`T` is the published canonical complex linear equivalence
`DerivativeSmoothFunctions K n ≃ₗ[ℂ] SmoothFunctions K n`.

## The actual right action and its continuity

`rightAction K n : Representation ℂ G (DerivativeSmoothFunctions K n)` is the
published `smoothRightAction K n` moved across `T`: its operator at `g` is
`T.symm ∘ₗ smoothRightAction K n g ∘ₗ T`. Its unit and multiplication laws
follow from those of `smoothRightAction`. The following are proved:

- `rightAction_apply`: `rightAction K n g f = T.symm (smoothRightAction K n g (T f))`,
  by definition;
- `toSmooth_rightAction` (simp): `T (rightAction K n g f) = smoothRightAction K n g (T f)`;
- `toSmooth_rightAction_val`: `(T (rightAction K n g f)).val x = (T f).val (x * g)`,
  the published convention `(g • f)(x) = f(x * g)`;
- `evalCLM_rightAction` (simp):
  `evalCLM K n x (rightAction K n g f) = evalCLM K n (x * g) f`, for the published
  continuous point evaluation `evalCLM`.

`continuous_rightAction` proves joint continuity of `(g, f) ↦ rightAction K n g f`
from `G × DerivativeSmoothFunctions K n` with the derivative topology. It unfolds
the published `SmoothRightActionContinuityStatement`, which is exactly this map
written with `T`, and applies the published theorem `smoothRightActionContinuity`.
No other continuity argument is used. `continuous_rightAction_apply` specializes
this to a fixed `g`.

`rightActionCLM K n g` bundles the operator at `g` as a continuous complex linear
map `DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n`; its
continuity field is `continuous_rightAction_apply`. `rightRepresentationCLM K n`
is the monoid homomorphism `g ↦ rightActionCLM K n g` from `G`. The theorems
`rightActionCLM_apply` and `rightRepresentationCLM_apply` (both simp, by `rfl`)
say these operators act by `rightAction K n g`.

## The actual compact action

`compactAction K n : Representation ℂ Kₙ (DerivativeSmoothFunctions K n)` is
`(rightAction K n).comp Kₙ.subtype`. Its application lemma `compactAction_apply`
(simp, by `rfl`) is `compactAction K n k f = rightAction K n k.val f`.

`compactActionCLM K n` is `(rightRepresentationCLM K n).comp Kₙ.subtype`, the
monoid homomorphism to continuous complex linear operators. `compactActionCLM_apply`
(simp, by `rfl`) says it acts by the algebraic `compactAction K n`, so the
algebraic and continuous compact representations are the same action.
`continuous_compactAction` proves joint continuity of
`(k, f) ↦ compactAction K n k f` on `Kₙ × DerivativeSmoothFunctions K n`, with
the subspace topology on `Kₙ` that `ArchimedeanCompact` gives it, by composing
`continuous_rightAction` with the inclusion.

Relation with the published compact restriction on `SmoothFunctions K n`,
namely `(smoothRightAction K n).comp Kₙ.subtype`:

- `toSmooth_compactAction`: `T (compactAction K n k f)` is that restriction at `k`
  applied to `T f`;
- `compactActionEquiv K n : (compactAction K n).Equiv ((smoothRightAction K n).comp Kₙ.subtype)`
  is `T` as a Mathlib equivalence of representations (`Representation.Equiv.mk`),
  and `compactActionEquiv_apply` (simp) says it applies `T`;
- `transportedCompactAction K n` is `compactAction K n` conjugated by `T`, using
  `LinearEquiv.conjAlgEquiv`, so its value at `k` is
  `T ∘ compactAction K n k ∘ T.symm`;
- `transportedCompactAction_eq` proves
  `transportedCompactAction K n = (smoothRightAction K n).comp Kₙ.subtype`.

## Source representations and compact types

These declarations are in `Langlands.Global.ArchimedeanGL`.
`ContinuousCompactRep K n` is a structure for a finite-dimensional continuous
complex representation of `Kₙ` on the canonical model `Fin dim → ℂ`, with its
usual product (sup-norm) topology. Its fields are:

- `dim : ℕ`;
- `toRepresentation : Representation ℂ Kₙ (Fin dim → ℂ)`;
- `continuous_action`: joint continuity of `(k, v) ↦ toRepresentation k v` on
  `Kₙ × (Fin dim → ℂ)`.

Continuity is a field of the structure, not something derived. The source
carrier `Fin dim → ℂ` lies in `Type 0` whatever `u` is. The bundles
`ContinuousCompactRep K n` and `CompactType K n` themselves lie in `Type u`,
because their action is indexed by `standardInfiniteCompact K n`.
`ContinuousCompactRep.continuous_orbit` gives continuity of each orbit map
`k ↦ τ.toRepresentation k v`. `ContinuousCompactRep.continuous_toMatrix'` gives
continuity of the matrix coefficients `k ↦ LinearMap.toMatrix' (τ.toRepresentation k)`.

`CompactType K n` extends `ContinuousCompactRep K n` with one more field,
`isIrreducible : toRepresentation.IsIrreducible`, which is Mathlib's algebraic
irreducibility of representations. It is the type of genuine irreducible compact
types. No equivalence relation or quotient by isomorphism is introduced.

## Isotypic spans

These declarations are in the `DerivativeSmoothFunctions` namespace, and `τ`
ranges over `ContinuousCompactRep K n`.

`isotypicSpan τ : Submodule ℂ (DerivativeSmoothFunctions K n)` is by definition
the published `Langlands.CompactSplitting.isotypicPart τ.toRepresentation (compactAction K n)`.
This is the supremum, over all Mathlib intertwining maps
`τ.toRepresentation.IntertwiningMap (compactAction K n)`, of their ranges. It is
purely algebraic: the intertwiners are not required to be continuous, and the
span is not claimed to be closed. `isotypicSpan` is defined for any source
representation. For an irreducible type `σ : CompactType K n`, the abbreviation
`compactTypeSubmodule σ` is `isotypicSpan σ.toContinuousCompactRep`. All lemmas
about `isotypicSpan` apply to it.

`isotypicSubrep τ` is the same supremum of Mathlib's `IntertwiningMap.range`,
taken among Mathlib subrepresentations `Subrepresentation (compactAction K n)`
in the complete lattice from the published
`Langlands.Representation.SubrepresentationLattice`.
`toSubmodule_isotypicSubrep` shows that its underlying submodule is
`isotypicSpan τ`, using the published `Langlands.Subrepresentation.toSubmodule_iSup`.
Proved laws:

- `range_le_isotypicSpan`: every intertwiner range lies in `isotypicSpan τ`
  (the published `range_le_isotypicPart`);
- `isotypicSpan_le_iff`: `isotypicSpan τ ≤ S` exactly when every intertwiner
  range lies in `S`;
- `mem_isotypicSpan_iff`: `v ∈ isotypicSpan τ` exactly when, for some finite set
  `s` of intertwiners and some choice of vectors `x f : Fin τ.dim → ℂ`,
  `v = ∑ f ∈ s, f (x f)`;
- `compactAction_mem_isotypicSpan`: `isotypicSpan τ` is stable under every
  `compactAction K n k`. The proof goes through `isotypicSubrep`;
- `isotypicSpan_eq_of_equiv`: an equivalence `τ.toRepresentation.Equiv τ'.toRepresentation`
  gives `isotypicSpan τ = isotypicSpan τ'`, by composing intertwiners with the
  inverse equivalence (Mathlib's `Representation.Equiv.toIntertwiningMap`). Only
  the algebraic representations are compared; dimensions agree because of the
  equivalence, and continuity plays no role.

## Finite selected sums

Let `ι` be a type of any universe, `s : Finset ι`, and
`τ : ι → ContinuousCompactRep K n`. Multiplicities are not assumed finite.

- `selectedIsotypicSum s τ` is `⨆ i ∈ s, isotypicSpan (τ i)` in
  `Submodule ℂ (DerivativeSmoothFunctions K n)`;
- `selectedIsotypicSubrep s τ` is the same supremum of `isotypicSubrep (τ i)`
  among subrepresentations; `toSubmodule_selectedIsotypicSubrep` identifies its
  submodule with `selectedIsotypicSum s τ`;
- `isotypicSpan_le_selectedIsotypicSum`: each selected `isotypicSpan (τ i)`, for
  `i ∈ s`, lies in the sum;
- `range_le_selectedIsotypicSum`: so does the range of every intertwiner from a
  selected `τ i`;
- `mem_selectedIsotypicSum_iff`: `v` is in the sum exactly when
  `v = ∑ i ∈ s, w i` for some `w : ∀ i, isotypicSpan (τ i)`
  (Mathlib's `Submodule.mem_iSup_finset_iff_exists_sum`);
- `compactAction_mem_selectedIsotypicSum`: the sum is stable under every
  `compactAction K n k`.

`selectedTypeSum s σ`, for `σ : ι → CompactType K n`, is the abbreviation for the
selected sum of the underlying source representations, so the lemmas above
apply to it.

## Transfer to `SmoothFunctions`

- `smoothIsotypicSpan τ` is the image of `isotypicSpan τ` under `T`.
  `mem_smoothIsotypicSpan_iff` says `f` is in it exactly when `T.symm f ∈ isotypicSpan τ`;
- `smoothIsotypicSpan_eq` proves
  `smoothIsotypicSpan τ = CompactSplitting.isotypicPart τ.toRepresentation ((smoothRightAction K n).comp Kₙ.subtype)`.
  The proof composes intertwiners with `compactActionEquiv K n` and with its
  inverse;
- `smoothRightAction_mem_smoothIsotypicSpan`: the transferred span is stable
  under `smoothRightAction K n k.val` for every `k : Kₙ`;
- `smoothSelectedIsotypicSum s τ` is the image of `selectedIsotypicSum s τ`
  under `T`. `smoothSelectedIsotypicSum_eq` proves it equals
  `⨆ i ∈ s, CompactSplitting.isotypicPart (τ i).toRepresentation ((smoothRightAction K n).comp Kₙ.subtype)`.

## Provenance and scope

The construction is internal. It specializes the published actual right
action, its published joint continuity theorem, the actual compact subgroup and
the published generic algebraic isotypic part
`Langlands.CompactSplitting.isotypicPart`. It adds no generic isotypic-span
definition of its own. The only Mathlib inputs are representation, intertwining-map,
subrepresentation and submodule-lattice API at the pinned Mathlib, together
with the published subrepresentation lattice. No
literature theorem is formalized here, and no hypothesis is added to the
archimedean action: there is no local constancy and no open stabilizer.

The module claims no Haar or other projection operator onto these subspaces,
and no Peter–Weyl decomposition. It does not claim semisimplicity, directness
or density of the sums, closedness or finite-dimensionality of isotypic spans,
admissibility, analytic regularity of their elements, or reproduction formulas.
The automorphic differential-growth theorem is not addressed. Those remain
separate obligations.
