# Proof of scalar uniqueness for compact-to-smooth mirabolic intertwiners

Author: Worker 804. The compact-model uniqueness core used here,
`Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness`, is
Worker 805's published module. It is imported by Lean name, and no part of it
is copied here.

This module proves the published proposition
`Langlands.Whittaker.MirabolicCompactHomScalarStatement.{uF}` from
`Langlands.Representation.Whittaker.MirabolicCompactHomStatement`:

```lean
theorem Langlands.Whittaker.mirabolicCompactHomScalar :
    MirabolicCompactHomScalarStatement.{uF}
```

This is the p-adic case of Bernstein–Zelevinsky (1976), Proposition 5.15(b),
printed p.49, with proof on printed p.50: "Any P-homomorphism `τ_P⁰ → τ_P` is
proportional to the standard embedding."

## What is proved

The theorem has exactly the statement's type. Every prime `p` enters through
`(p : ℕ) (_hp : Fact p.Prime)`. The theorem then holds for every
`F : PadicField.{uF} p` with its canonical topology
`F.canonicalTopologicalData.topology`, for an arbitrary field universe `uF`,
and for every `n : ℕ`, including `n = 0`. It also holds for every bundled
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, which is
continuous, unitary and nontrivial, and for every intertwiner

```lean
A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)
```

For each such `A` there is `c : ℂ` with `A = c • mirabolicCompactInclusion ψ n`.

The theorem adds no hypothesis. It assumes no irreducibility, admissibility,
finite generation, minimality, scalar uniqueness or functional equivalence.
`A` may be zero, in which case `c = 0`. `lean_check` reports that the theorem
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Objects and conventions

The proof works with the published models from `MirabolicModels`, without
any normalization. Here `P = mirabolic n F` is the actual last-row mirabolic
group inside `GL(n + 1)`. `U = Mirabolic.upperUnipotent n F` is its upper
unitriangular subgroup, and `Θ = mirabolicCharacter ψ n` is the positive
adjacent-entry character `u ↦ ∏ ψ(u_{i,i+1})`. These match BZ76 §§5.1, 5.5
and 5.6, printed pp.44–45.

- The smooth model `mirabolicSmoothInduced ψ n` acts by right translation on
  smooth functions `φ : P → ℂ` with unnormalized covariance
  `φ(u * g) = Θ(u) * φ(g)`. The relevant laws are `mirabolicEval_translate`,
  `(ρ(s) φ)(g) = φ(g * s)`, and `mirabolicEval_covariance`. This is BZ76's
  `τ_P = Ind(P, U, Θ)` (§§2.21, 5.7, pp.21 and 45).
- The compact model `mirabolicCompactInduced ψ n` is the subrepresentation
  of functions whose projected nonzero support in `U \ P` is compact. This is
  `τ_P⁰ = ind(P, U, Θ)` (§2.22, p.22). Its evaluation
  `mirabolicCompactEval` satisfies the same translation law,
  `mirabolicCompactEval_translate`.
- The canonical inclusion `mirabolicCompactInclusion ψ n` sends a compact
  function to the same function. Hence
  `mirabolicEval ψ n (mirabolicCompactInclusion ψ n f) g =
  mirabolicCompactEval ψ n f g` holds by definition.
- A Whittaker functional on the compact model is an element of
  `MirabolicWhittaker.compactFunctionals ψ n`. This set is the published
  `Whittaker.functionals U Θ (mirabolicCompactInduced ψ n)`: the linear
  functionals `ℓ` with `ℓ(ρ(u) f) = Θ(u) * ℓ(f)` for all `u ∈ U`.

## The imported uniqueness core

Worker 805's published theorem, with the instance arguments it needs, is

```lean
MirabolicWhittaker.exists_testVector (hψ : IsOpen {t | ψ.complex t = 1}) :
  ∀ n, ∃ f₀ : MirabolicCompactFunctions ψ n,
    ∀ ℓ ∈ compactFunctionals ψ n, ℓ f₀ = 0 → ℓ = 0
```

So a single compact function `f₀` detects every Whittaker functional on the
compact model. Equivalently, `ℓ ↦ ℓ f₀` is injective, and the functional
space has dimension at most one. The theorem needs the instances
`[IsTopologicalDivisionRing F] [T2Space F]`,
`[∀ m, NonarchimedeanGroup (GL m F)]` and
`[∀ m, LocallyCompactSpace (GL m F)]`. Its hypothesis `hψ` is discharged
by the published `MirabolicWhittaker.isOpen_complex_eq_one ψ` once `F` is a
nonarchimedean additive group. The core's own Markdown explains its proof,
which is a direct induction on the rank over the actual unnormalized models.

## The proof (section `Generic`)

In this section `F` is any topological field that is a topological ring.

1. **Evaluation after an intertwiner** (`evalOne`, `evalOne_mem`). For an
   intertwiner `A`, set `ℓ_A(f) = (A f)(1)`. This is linear because `A` is.
   It is a Whittaker functional: for `u ∈ U`, intertwining gives
   `A(ρ(u) f) = ρ(u)(A f)`. The translation law gives
   `(ρ(u)(A f))(1) = (A f)(1 * u) = (A f)(u * 1)`, and covariance turns this
   into `Θ(u) * (A f)(1)`. In Lean, intertwining is used through
   `LinearMap.congr_fun (A.isIntertwining' u) f`.
2. **The canonical functional** (`evalOne_inclusion_apply`). For
   `A = mirabolicCompactInclusion ψ n`, `ℓ₀ = ℓ_A` is just evaluation at the
   identity, `ℓ₀(f) = f(1)`. By step 1 it is also a Whittaker functional.
   This is the Frobenius evaluation map of BZ76 Theorem 2.28, printed p.23,
   restricted to the compact model.
3. **Propagation by right translation** (`eq_smul_inclusion_of_evalOne`).
   Suppose `(A f)(1) = c * f(1)` for every compact `f`. Fix `g ∈ P` and apply
   the hypothesis to `ρ(g) f`. On the left, intertwining and the translation
   law give `(A(ρ(g) f))(1) = (ρ(g)(A f))(1) = (A f)(g)`. On the right, the
   compact translation law gives `(ρ(g) f)(1) = f(g)`. So
   `(A f)(g) = c * f(g)` for every `g`. The smooth model is a subtype of
   covariant functions, which is in turn a subtype of all functions `P → ℂ`,
   so two applications of `Subtype.ext` and `funext` give
   `A f = (c • mirabolicCompactInclusion ψ n) f`. Extensionality of
   intertwining maps then gives `A = c • mirabolicCompactInclusion ψ n`.
4. **Comparison of functionals** (`exists_eq_smul_inclusion`). Assume a test
   vector `f₀` as in the core, and a compact `f` with `f(1) ≠ 0`. Then
   `ℓ₀ ≠ 0`, so the test-vector property gives `ℓ₀(f₀) ≠ 0`. Put
   `c = ℓ_A(f₀) / ℓ₀(f₀)`. Whittaker functionals form a submodule, so
   `ℓ_A − c • ℓ₀` is a Whittaker functional, and it vanishes at `f₀`. The
   test-vector property makes it zero. Hence `(A f)(1) = c * f(1)` for every
   `f`, and step 3 finishes the proof.

### The nonzero evaluation argument

`exists_compactEval_one_ne_zero` produces a compact function with value `1`
at the identity. It needs `P` to be nonarchimedean and weakly locally compact.

- `characterRepresentation_smooth` shows that the one-dimensional
  representation `mirabolicCharacterRepresentation ψ n` of `U`, which is
  scalar multiplication by `Θ`, is smooth. The kernel of `Θ` is an open
  subgroup by `Langlands.isOpen_ker_of_continuous_complex_character`, applied
  to the continuous character `mirabolicCharacterContinuous ψ n`. That lemma
  needs `U` to be nonarchimedean, which follows from `P` through
  `Langlands.Topology.Nonarchimedean.Subgroup`. Every element of the kernel
  fixes every scalar.
- The published `Induction.compactLocalSection` from
  `Langlands.Representation.Induction.CompactLocalSection` takes the subgroup
  `U ≤ P`, this smooth representation, the point `x = 1`, the value `v = 1`
  and the open set `Set.univ` of `U \ P`. It returns a compactly induced
  function. `Induction.compactLocalSection_apply` shows that this function
  takes the value `1` at the identity. The compact model's evaluation is
  definitionally the framework's `Induction.eval`, so the function has
  `f(1) = 1 ≠ 0`.

The source leaves this step implicit: on p.50 it notes that the standard
embedding is nonzero in a one-dimensional space. Here it is proved with the
actual compact support condition.

## The p-adic instances (section `Padic`)

`compactHomScalar_canonical` fixes `F : PadicField.{uF} p` and installs the
canonical topology, valuative relation and local-field certificate, exactly as
the statement's internal `letI`s do. It then supplies the following instances.

- `T2Space F.Carrier` comes from `F.canonicalTopologicalData.fieldT2`. The
  division-ring instance is found by typeclass inference.
- `NonarchimedeanAddGroup F.Carrier` comes from the published lemma
  `HarmonicAnalysis.rowFourierCutoff_nonarchimedean`. In a valuative topology the open submodules
  over the valuation integer form a neighborhood basis of zero
  (`IsLinearTopology.hasBasis_open_submodule`). The existing lemma supplies
  this instance directly.
- `NonarchimedeanGroup (GL m F)` comes from
  `Langlands.valuativeGeneralLinearNonarchimedean`, and
  `LocallyCompactSpace (GL m F)` from
  `F.canonicalTopologicalData.generalLinearLocallyCompactSpace`, for every
  `m`.
- For the mirabolic group itself, `MirabolicWhittaker.mirabolic_nonarchimedean`
  gives the nonarchimedean instance and `Mirabolic.locallyCompactSpace` gives
  local compactness.

Then `exists_eq_smul_inclusion` applies, with the test vector
`exists_testVector ψ (isOpen_complex_eq_one ψ) n` and the nonzero compact
function `exists_compactEval_one_ne_zero ψ n`. The final theorem
`mirabolicCompactHomScalar` introduces `p`, the primality instance and `F`,
and applies `compactHomScalar_canonical F`.

## Rank one

For `n = 0` the group `P` is trivial and `Θ` is the trivial character. The
argument above covers this case unchanged: the core supplies a test vector in
every rank, and the local section still has value `1` at the identity. No
case split is needed.

## Relation to the source proof

BZ76's proof on p.50 identifies `Hom_P(τ_P⁰, τ_P)` with `(E_{U,Θ})*` using
Frobenius duality (Theorem 2.28, p.23, and §2.30, p.24). It then computes
`dim E_{U,Θ} = dim (Φ⁻)^{n}(τ_P⁰) = 1` from Proposition 5.12(g), p.47. This
module follows the same route, with two changes.

- Only one direction of Frobenius duality is needed: evaluation at the
  identity sends an intertwiner to a Whittaker functional (steps 1 and 3).
  Step 3 is the injectivity half of Theorem 2.28, proved directly with the
  model's translation and covariance laws.
- The bound `dim (E_{U,Θ})* ≤ 1` is taken from Worker 805's core. The core
  proves it by induction on the rank over the actual unnormalized models,
  not with BZ76's derivative functors `Φ⁻` and `Φ⁺`. No normalized
  derivative appears anywhere, so no normalization bridge is required.

## Dependency independence

The imports are:

- `MirabolicCompactHomStatement`, the target;
- `MirabolicCompactWhittakerUniqueness`, the core;
- `Induction.CompactLocalSection`, for the nonzero compact function;
- `Twist.ContinuousCharacterProof`, for the open kernel of `Θ`;
- `Topology.Nonarchimedean.Subgroup`, so that `U` inherits the
  nonarchimedean property from `P`;
- `Group.GL.Nonarchimedean` and `Group.GL.Padic`, for the p-adic instances
  of `GL`;
- `HarmonicAnalysis.PadicRowFourierCutoffStatement`, for the generic
  valuation-topology lemma `rowFourierCutoff_nonarchimedean`.

The transitive closure of these imports in the integrated Library over commit
`4021bb1d1ec99e65990e08addda3ade7caa73058` has 46 project modules, and
none of them is a compact-minimality, functional-multiplicity, derivative,
Kirillov or rigidity module. So the required direction holds:
compact-model functional uniqueness → this scalar-Hom uniqueness → compact
minimality → irreducible functional multiplicity. The target pair and every
module it imports are unchanged.

## Source

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1–68. Registered source
  `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  I read Proposition 5.15 and its proof on printed pp.49–50. The model
  conventions and the Frobenius duality step on pp.21–24 and 44–47 are
  cited through the target's Markdown.
