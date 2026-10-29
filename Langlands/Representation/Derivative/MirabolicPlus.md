# Mirabolic plus induction functors

Author: Worker 723.

This module constructs the unnormalized Bernstein–Zelevinsky plus functors
`Ψ⁺` and `Φ⁺` on actual smooth complex representations of the actual
general linear and mirabolic groups. It also constructs the positive
extended character `thetaPlus` on the actual plus subgroup and the twisted
representation `τ'`. It proves only elementary construction laws: character,
continuity, open-kernel, action, covariance, support, smoothness, morphism and
functor laws. It contains no normalization character, Haar modulus,
exactness, adjunction, Fourier recognition, iteration, completely
nondegenerate decomposition or derivative result.

## Source

The registered original is Bernstein and Zelevinsky, *Representations of the
group GL(n,F) where F is a non-Archimedean local field*, Russian Math.
Surveys 31:3 (1976), `bernstein-zelevinsky-1976-representations-gln`,
SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
In this PDF the printed page number equals the PDF page number.

- §5.1, p.44: `P = P_n` is the mirabolic subgroup of `G_n = GL(n,F)` (last
  row `(0,…,0,1)`), and `M = M_n ⊂ P` is the last-column subgroup.
- §5.2, p.44: `G' = G_(n-1)` is embedded in `P` in the standard way,
  `P' = P_(n-1) ⊂ G'`, `M` is normal in `P`, and `P = G'·M` is a semidirect
  product.
- §5.3–5.4, pp.44–45: for a fixed nontrivial additive character `ψ` of `F`,
  `Θ(m) = ψ(m_(n-1,n))` on `M`. Its normalizer in `P` is `P'·M`.
- §5.11, Definition, p.46:
  - b) for `(τ, P', V)`, `Φ⁺(τ) = ind(P, P'M, τ')`, where `τ'` is the
    representation of `P'M` on the same space `V` given by
    `τ'(pm)ξ = Θ(m)τ(p)ξ` for `m ∈ M`, `p ∈ P'`, `ξ ∈ V`;
  - d) for `(ρ, G', V)`, `Ψ⁺(ρ)` is the representation of `P` on the same
    space given by `Ψ⁺(ρ)(gm) = ρ(g)` for `g ∈ G'`, `m ∈ M`.
- §2.21–2.22, pp.21–22: `Ind(G,H,ρ)` consists of functions with
  `f(hg) = ρ(h)f(g)` and one open compact subgroup `N_f` of right
  stabilizers, with action `(π(g₀)f)(g) = f(gg₀)`. `ind(G,H,ρ)` is the
  subspace of functions finite modulo `H` (§1.20). The Remark on p.22
  mentions a variant covariance with a modulus factor. The definitions in
  2.21–2.22, to which 5.11 b) refers, use the unmodified covariance 1), and
  so does this module.

The minus functors of §5.11 a), c), the properties in §5.12 (exactness,
adjunctions, vanishing of composites) and the normalized variant are not
constructed or stated here. No errata entry for these pages is registered in
the literature index, and none was found among the public notes.

The compact induction used is the published
`Langlands.Induction.compactInduced`. It is the actual space of covariant
functions with one open subgroup of right stabilizers whose projected nonzero
support in `Q \ P_(n+2)` is compact, acted on by right translation. Its
paired Markdown, `Langlands/Representation/Induction/Definitions.md`,
explains this support convention and its source.

### Rank shift

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)`, and
`GeneralLinear.Mirabolic.radical (n + 1) F.Carrier` is the source's `M_(n+2)`.
Hence:

- `psiPlusUnnormalized T n` is the source's `Ψ⁺ : Alg G_n → Alg P_(n+1)`;
  that is, the source's `n` is our `n + 1`;
- `phiPlusUnnormalized T ψ n` is the source's
  `Φ⁺ : Alg P_(n+1) → Alg P_(n+2)`; that is, the source's `n` is our
  `n + 2`;
- the published `GeneralLinear.Mirabolic.plusSubgroup n F.Carrier`, the
  subgroup of `mirabolic (n + 1) F.Carrier` whose upper-left `(n+1)`-block
  lies in `mirabolic n F.Carrier`, is the source's `P'·M = P_(n+1)·M_(n+2)`.

The source's entry `m_(n-1,n)` (1-based, for `P_n`) is the 0-based entry
`(n, n + 1)` of an `(n+2) × (n+2)` matrix, namely
`lastColumn q.val (Fin.last n)`.

Every `n : ℕ` is allowed, with no special case. At `n = 0`, `Ψ⁺` goes from
`GL_0` to the trivial group `P_1`. `Φ⁺` goes from `P_1` to `P_2`, and
`plusSubgroup 0 F.Carrier` is the radical `V_2`
(published `plusSubgroup_zero`).

### What the source supplies and what is derived

The source supplies the groups `P`, `P'`, `G'`, `M`, the character `Θ`, the
formula for `τ'` in the Levi-first coordinates `pm`, the inflation formula
for `Ψ⁺`, and the induction `ind` by right translation. The following are
derived implementation choices:

- `thetaPlus` is defined on all of `Q` by one matrix entry,
  `thetaPlus(q) = ψ(lastColumn q.val (Fin.last n))`. No coordinate
  decomposition is used. Its multiplicativity comes from the published
  additivity `lastColumn_mul_last` of that entry on `Q`.
- `τ'` is defined as the published character twist
  `Langlands.twist (thetaPlus ψ n) (τ.comp plusProjection)`. The
  source's formula `τ'(pm) = Θ(m)τ(p)` is then a theorem.
- Continuity, open kernels, smoothness, and the morphism and functor laws
  are derived.

### Coordinate convention

The source writes elements of `P'M` Levi-first, as `pm` with `p ∈ P'` and
`m ∈ M`. The published decomposition
`plus_eq_plusRadical_mul_plusSuccessor` writes them radical-first, as
`plusRadical u * plusSuccessor g`. Both orders give the same value of
`thetaPlus`, because the smaller mirabolic fixes the final coordinate:

- `lastColumn_successor`: `lastColumn (successor g) = 0`;
- `lastColumn_successor_mul_radical_last`:
  `lastColumn (successor g * u.val) (Fin.last n) = radicalCoordinates u (Fin.last n)`.
  The proof uses the published `lastColumn_mul`, so the final column of the
  product is `projection(successor g) · v_u + 0 = g · v_u`. It also uses the
  published `mulVec_last`: the last row of `g ∈ mirabolic n` is
  `(0, …, 0, 1)`, so `(g · v)_last = v_last`;
- `lastColumn_radical_mul_successor_last`: in the other order, the final
  column is `v_u + u · 0`, with the same last entry.

Consequently `thetaPlus_plusSuccessor_mul_plusRadical` (Levi-first),
`thetaPlus_plusRadical_mul_plusSuccessor` (radical-first) and
`thetaPlus_plusSuccessor_mul_plusRadical_eq` (equality of the two) hold.

## Parameters

The character section is generic: `F : Type uF` is a commutative ring, and
from `thetaPlus` on it also carries any topology. For the functors, `p : ℕ`
is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`, and
`T : F.TopologicalData` is supplied. Every functor statement installs
`letI := T.topology`; no canonical topology is substituted. Where compact
induction needs a topological group structure on `mirabolic (n + 1)`, the
statements also install `letI := T.generalLinearTopologicalGroup (n + 1 + 1)`.
The additive character is
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, which bundles
continuity and nontriviality.

Universes: the coefficient universe of `SmoothRep` is `0` (complex
coefficients). The group universe is `uF`, and the carrier universe `uV` is
independent of `uF`.

- `psiPlusUnnormalized T n : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤ SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)`;
- `plusTwistFunctor T ψ n : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤ SmoothRep.{0, uF, uV} ℂ (plusSubgroup n F.Carrier)`;
- `phiPlusUnnormalized T ψ n : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤ SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier)`.

The output carrier universe `max uF uV` of `Φ⁺` is the universe of the actual
function space `Induction.CompactFunctions`. There is no universe resize or
supplied replacement carrier.

## The positive character on the plus subgroup

In the generic section (`F` a commutative ring):

- `plusLastCoordinate n : plusSubgroup n F →* Multiplicative F` sends `q` to
  its entry `lastColumn q.val (Fin.last n)`. `plusLastCoordinate_apply`
  states this. `plusLastCoordinate_plusRadical` says that on the radical it is
  the published `lastCoordinate n`. `plusLastCoordinate_plusSuccessor` says
  that it is `1` on `plusSuccessor g`.
- `thetaPlus ψ n : plusSubgroup n F →* ℂˣ` is
  `Circle.toUnits ∘ ψ ∘ plusLastCoordinate n`, the same composite as the
  published `theta ψ n` on the radical. It is positive: no inverse is
  inserted. Its laws are:
  - `thetaPlus_apply`: `(thetaPlus ψ n q : ℂ) = ψ.complex (lastColumn q.val (Fin.last n))`;
  - `thetaPlus_one`, `thetaPlus_mul` and `norm_thetaPlus` (values of norm `1`);
  - `thetaPlus_plusRadical`: `thetaPlus ψ n (plusRadical u) = theta ψ n u`
    (`rfl`), and `thetaPlus_comp_plusRadical`, the same equation as
    homomorphisms;
  - `thetaPlus_plusSuccessor`: `thetaPlus ψ n (plusSuccessor g) = 1`;
  - the three coordinate-convention theorems above.
- `thetaPlusContinuous ψ n` is `thetaPlus ψ n` bundled as a
  `ContinuousMonoidHom`, and `continuous_thetaPlus` states its continuity.
  The proof composes `ψ`'s continuity with the continuous extraction of one
  entry (`continuous_lastColumn`).
- `thetaPlus_isOpen_ker`: if `plusSubgroup n F` is a nonarchimedean group,
  the kernel is open. This is the published criterion
  `isOpen_ker_of_continuous_complex_character`.
- `isOpen_ker_thetaPlus T ψ n`: for the p-adic field with the supplied
  topology, the kernel is open. The nonarchimedean structure on `GL_(n+2)`
  comes from the published `valuativeGeneralLinearNonarchimedean`, and the
  plus subgroup inherits it.

## The representation `τ'`

For `τ : Representation ℂ (mirabolic n F) V`:

- `plusTwistRepresentation ψ n τ : Representation ℂ (plusSubgroup n F) V` is
  `Langlands.twist (thetaPlus ψ n) (τ.comp plusProjection)`, on the same
  carrier `V`;
- `plusTwistRepresentation_apply`:
  `τ'(q) v = (thetaPlus ψ n q : ℂ) • τ (plusProjection q) v`;
- `plusTwistRepresentation_plusSuccessor_mul_plusRadical`: the source
  formula `τ'(p m) v = Θ(m) • τ(p) v` in Levi-first coordinates;
- `plusTwistRepresentation_plusRadical_mul_plusSuccessor`: the same value
  in radical-first coordinates.

`plusTwistFunctor T ψ n` is
`continuousPullbackFunctor plusProjection continuous_plusProjection ⋙ SmoothRep.twistFunctor (thetaPlus ψ n) (isOpen_ker_thetaPlus T ψ n)`.
It reuses the published `continuousPullbackFunctor` from `MirabolicMinus`
and the published open-kernel twist functor. It keeps carriers and linear
maps. `plusTwistFunctor_obj_representation` states that its object action
is `plusTwistRepresentation ψ n τ.representation` (`rfl`).
`plusTwistRepresentation_isSmooth` proves that `τ'` is smooth: a continuous
pullback (`isSmooth_comp`) followed by an open-kernel twist
(`isSmooth_twist_iff`).

## Unnormalized Ψ⁺

`psiPlusUnnormalized T n` is
`continuousPullbackFunctor projection continuous_projection`. It inflates
along the published continuous projection `projection : mirabolic n F →* GeneralLinear n F`,
whose kernel is the radical (published `ker_projection`). The proved laws are:

- `psiPlusUnnormalized_obj_carrier`: the object carrier is the input
  carrier (`rfl`);
- `psiPlusUnnormalized_obj_representation`: the object action is
  `A.representation.comp projection` (`rfl`);
- `psiPlusUnnormalized_action`: `Ψ⁺(ρ)(g) v = ρ(projection g) v`;
- `psiPlusUnnormalized_radical`: elements of `radical n F` act trivially;
- `psiPlusUnnormalized_levi`: `Ψ⁺(ρ)(levi a) = ρ(a)`, the source's formula
  for `g ∈ G'`;
- `psiPlusUnnormalized_radicalElement_mul_levi`: in the published
  radical-first coordinates, `Ψ⁺(ρ)((radicalElement v).val * levi a) = ρ(a)`.
  Since the radical acts trivially, this is the source formula
  `Ψ⁺(ρ)(gm) = ρ(g)` up to the order of factors;
- `psiPlusUnnormalized_isSmooth`: output objects are smooth (continuous
  pullback);
- `psiPlusUnnormalized_map_apply`: the image of `f` has the same underlying
  linear map (`rfl`);
- `psiPlusUnnormalized_map_equivariant`, `psiPlusUnnormalized_map_id` and
  `psiPlusUnnormalized_map_comp`.

## Unnormalized Φ⁺

`phiPlusUnnormalized T ψ n` is

```
plusTwistFunctor T ψ n ⋙ SmoothRep.toRep ⋙
  Induction.compactInductionFunctor (plusSubgroup n F.Carrier)
```

So `Φ⁺(τ)` is the published compact induction `ind(P_(n+2), Q, τ')` from the
actual plus subgroup. Its object and carrier laws are:

- `phiPlusUnnormalized_obj`: the object equals
  `SmoothRep.of (Induction.compactInduced Q τ') (Induction.compactInduced_smooth Q τ')`
  (`rfl`), where `τ' = plusTwistRepresentation ψ n τ.representation`;
- `phiPlusUnnormalized_obj_carrier`: the carrier is
  `Induction.CompactFunctions Q τ'`, in `Type (max uF uV)` (`rfl`);
- `phiPlusUnnormalized_obj_representation`: for each `g` and `φ`, the
  action `(Φ⁺ τ)(g) φ` equals `Induction.compactInduced Q τ' g φ` in
  `CompactFunctions Q τ'` (`rfl`). It is stated pointwise because the
  function-level equation forces the elaborator to unify two instance paths
  on the carrier, which exceeds the heartbeat limit. The object equation
  above already contains the function-level statement.

Evaluation and construction of vectors:

- `phiPlusEval T ψ n τ φ x` is `Induction.eval Q τ' φ x`, the value in `τ`
  of the underlying function at `x : mirabolic (n + 1) F.Carrier`;
- `phiPlusEval_injective`: vectors are determined by their values;
- `phiPlusEval_covariant`:
  `φ(q x) = (thetaPlus ψ n q : ℂ) • τ(plusProjection q)(φ x)` for `q ∈ Q`;
- `phiPlusEval_successor_mul_radical`: the source's covariance
  `φ(successor g * u * x) = Θ(u) • τ(g)(φ x)`, in Levi-first coordinates;
- `phiPlusEval_radical_mul`: `φ(u x) = Θ(u) • φ(x)` for
  `u ∈ radical (n + 1)`;
- `phiPlusEval_successor_mul`: `φ(successor g * x) = τ(g)(φ x)`;
- `phiPlusEval_isCompact_quotientSupport`: the projected nonzero support
  `Induction.quotientSupport Q (phiPlusEval T ψ n τ φ)` is compact in
  `Q \ P_(n+2)`;
- `phiPlusEval_exists_openSubgroup`: one open subgroup `K` of
  `mirabolic (n + 1)` with `φ(x k) = φ(x)` for all `k ∈ K` and all `x`;
- `phiPlusMk T ψ n τ f hcov K hK hc` builds a vector of `Φ⁺(τ)` from a
  function `f` with covariance `hcov`, one open subgroup `K` of right
  stabilizers (`hK`) and compact projected support (`hc`). It uses the
  published `Induction.compactFunctionOf`. `phiPlusEval_mk` says that its
  values are `f` (`rfl`).

Action, smoothness and functoriality:

- `phiPlusUnnormalized_action`: right translation,
  `phiPlusEval (g • φ) x = phiPlusEval φ (x * g)` (`rfl`);
- `phiPlusUnnormalized_isSmooth`: output objects are smooth
  (`Induction.compactInduced_smooth`);
- `phiPlusUnnormalized_map_hom`: the image of `f : τ ⟶ σ` is
  `Induction.compactInducedMap Q` of the underlying intertwiner of
  `(plusTwistFunctor T ψ n).map f`, whose linear map is that of `f` (`rfl`);
- `phiPlusUnnormalized_map_eval`: on values the image is postcomposition,
  `(Φ⁺ f)(φ)(x) = f(φ x)` (`rfl`);
- `phiPlusUnnormalized_map_equivariant`, `phiPlusUnnormalized_map_id` and
  `phiPlusUnnormalized_map_comp`.

## Imports and reuse

The module imports `Langlands.Representation.Derivative.MirabolicMinus` (for
`continuousPullbackFunctor`, and transitively `MirabolicCharacter`,
`Category.Twist` and `Smooth.Transfer.PullbackProof`),
`Langlands.Group.GL.MirabolicProjection` and
`Langlands.Representation.Induction.Definitions`. It reuses the published
`projection`, `plusSubgroup`, `plusProjection`, `plusSuccessor`,
`plusRadical`, `lastColumn` and its laws, `theta`, `mulVec_last`, the
continuous pullback functor, `Langlands.twist`, `SmoothRep.twistFunctor`, and
`Induction.compactInductionFunctor` with its evaluation and constructor API.
The only new constructions are `plusLastCoordinate`, `thetaPlus`,
`thetaPlusContinuous`, `plusTwistRepresentation`, `plusTwistFunctor`,
`psiPlusUnnormalized`, `phiPlusUnnormalized`, `phiPlusEval` and
`phiPlusMk`. Everything else is a theorem about them. No existing Library
file is changed.
