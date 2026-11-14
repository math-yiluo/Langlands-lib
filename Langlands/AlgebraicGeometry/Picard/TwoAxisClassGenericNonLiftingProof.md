# Murre's condition (F8) for the two-axis class presheaf

Worker 387 wrote this module for Task 6297. It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassGenericNonLiftingStatement` by the
theorem

```
theorem noetherianTwoAxisClassGenericNonLifting :
    NoetherianTwoAxisClassGenericNonLiftingStatement.{u}
```

in namespace `Langlands.AlgebraicGeometry.Picard`, at arbitrary universe `u`.

## What is proved

Let `A` be an abelian scheme over a scheme `S`. The proof shows that the published presheaf
`TwoAxisRigidifiedLineBundle.classPresheaf A` satisfies `UnramifiedFunctor.GenericNonLifting`,
Murre's condition (F8). Its value at a test object `T : Over S` is the set of isomorphism
classes of line bundles on the self-product `A_T ×_T A_T`, with compatible trivializations
along both unit axes. The statement:

- Let `Λ` be a noetherian ring and `t` a generic point of `Spec Λ` (`IsGenericPoint t univ`).
  Write `p = t.asIdeal`.
- Let `I` be a nilpotent ideal with `I · N = 0`, where `N` is the nilradical, and
  `f : Spec Λ ⟶ S`.
- Let `ξ'` be a class over `Spec (Λ/I)`. Suppose its restriction to `Spec (Λ_p/IΛ_p)` lifts to
  no `Spec (Λ_p/J)` with `J < IΛ_p` (`UnramifiedFunctor.NoLargerLift`).
- Then there is `g₀ ∈ Λ` with `D(g₀)` nonempty such that for every `g` with `D(g) ⊆ D(g₀)`
  the restriction of `ξ'` to `Spec (Λ_g/IΛ_g)` lifts to no `Spec (Λ_g/J)` with `J < IΛ_g`.

The general theorem is `TwoAxisRigidifiedLineBundle.classPresheaf_genericNonLifting A`. It
holds over every base `S`. The required theorem specializes it to `S = Spec R` with `R`
noetherian; the noetherian hypothesis on `R` is not used. The noetherian hypothesis on `Λ` is
used (finiteness of `I`, and the spreading theorem).

## Proof outline

Lifts of classes along a square-zero extension correspond to solutions of a cocycle equation
in the Čech complex of the self-product, with an obstruction cochain `z` and an obstruction
map `φ`. The module `TwoAxisClassObstruction` provides this correspondence. Then:

1. **Generic step.** The hypothesis at `Λ_p` gives `InjVanishes` with coefficients in the
   residue field `κ(p)`: a nonzero `ψ : I → κ(p)` with `ψ_* z` a coboundary would give a lift
   to `Λ_p / J` for the hyperplane `J = ker Ψ < IΛ_p` of an extension `Ψ` of `ψ`.
2. **Change of base ring.** All coefficient modules involved are killed by `p`, and `p` is the
   nilradical. The condition is moved from `Λ/I` to the domain `Λ/p` with
   `injVanishes_baseChange_iff` (module `ObstructionInjectivitySpread`).
3. **Spreading.** Over the noetherian domain `Λ/p` with flat field `κ(p)`, the theorem
   `exists_injVanishes_spread` gives `g₀` with `g₀ ∉ p` such that the condition holds for
   every module killed by `p` on which `g₀` acts bijectively.
4. **Open step.** If `D(g) ⊆ D(g₀)`, then `g₀` is a unit in `Λ_g`. A lift to `Λ_g / J` with
   `J < IΛ_g` gives a cocycle solution with coefficients in `M = IΛ_g / J`, a module killed by
   `p` on which `g₀` acts bijectively. So the obstruction map `φ : I → M` is zero, which means
   `IΛ_g ⊆ J`, a contradiction.

## Declarations

### Ring lemmas (namespace `GenericNonLifting`)

- `asIdeal_le_nilradical t ht`: a generic point `t` of `Spec Λ` specializes to every point,
  so `t.asIdeal` lies in every prime ideal, hence in the nilradical (`nilradical_eq_sInf`).
- `isTorsionBySet_ideal`: if `𝔞 * I = ⊥`, then `I` is killed by `𝔞`.
- `isTorsionBySet_ker`: for a `Λ`-algebra `B`, an ideal `J ≤ IB`, and `𝔞 * I = ⊥`, the
  kernel of `B/J → B/IB` (`Ideal.Quotient.factorₐ`) is killed by `𝔞`.
- `mul_eq_zero_of_mem_ker`: if `I * I = ⊥`, any two elements of that kernel multiply to zero.
- `exists_hyperplane p hII ψ hψ`: for a prime `p`, `I * I = ⊥` and a nonzero `Λ`-linear
  `ψ : I → κ(p)`, there are an ideal `J < IΛ_p` and an injective `Λ`-linear
  `jM : κ(p) → Λ_p/J` whose image is the kernel of `Λ_p/J → Λ_p/IΛ_p`, with
  `jM m * jM m' = 0` and `jM (ψ x) = x` in `Λ_p/J` for `x ∈ I`.
  Proof. `IΛ_p` is the base change of `I` to `Λ_p` (`IsLocalizedModule.isBaseChange` for
  `Algebra.idealMap`), so `ψ` extends to a `Λ_p`-linear `Ψ : IΛ_p → κ(p)`. `Ψ` is surjective,
  since `ψ x₀ ≠ 0` for some `x₀` and `κ(p)` is a quotient of `Λ_p`. Let `J` be the image of
  `ker Ψ` in `Λ_p`. Then `J ≠ IΛ_p` because `x₀ ∉ J`. `jM` is `Ψ.quotKerEquivOfSurjective`
  inverted, followed by the injective map `IΛ_p / ker Ψ → Λ_p / J` (`Submodule.mapQ`).

### The two steps (namespace `TwoAxisRigidifiedLineBundle`, section `Steps`)

The section fixes the data of `TwoAxisClassObstruction` with `A₀ = Λ/I` and `Q = I`
(`jQ = I.subtype`): an ordered affine cover `K` of the relative space of
`productStructure A f`, units `g` with `hg`, a rigidified bundle `L'` over `Λ/I`, and frames `e`
with transition functions the reductions of `g`. Write `z` for the published obstruction cochain
`zObs (productStructure A f) K I.subtype hjQ g hg`.

- `injVanishes_residueField hII p hNL`: let `κ(p)` carry a `Λ/I`-module structure compatible
  with `Λ`. If the class of `L'` has no larger lift at `Λ_p`, then
  `InjVanishes (cplx …) (dif …) z κ(p)`.
  Proof. Given `c` and `ψ ≠ 0` with `(dif 1 ⊗ κ(p))(c) + ψ_* z = 0`, apply
  `exists_hyperplane` to `ψ` viewed as `Λ`-linear. With `q = Λ_p/J → Λ_p/IΛ_p` and
  `χ = Λ/I → Λ_p/IΛ_p` (as in `restrictQuotient`), the published obstruction map `phiQ` equals
  `ψ`, by injectivity of `jM` and the published `jM_phiQ`. Then `exists_classLift_of_cocycle`
  gives a class over `Λ_p/J` restricting to the restriction of `ξ'`. This contradicts `hNL`.
- `noLargerLift_of_injVanishesRed hII p hpI B g₀ hu hP`: let `p * I = ⊥`, `B` a `Λ`-algebra in
  which `g₀` is a unit, and suppose `InjVanishesRed C d (red (Λ/I) _ I z) M` holds for every
  `Λ`-module `M` killed by `p` on which `g₀` acts bijectively. Here `C` and `d` are the Čech
  cochains and differentials over `Λ`. Then the class of `L'` has no larger lift at `B`.
  Proof. Let `J < IB` and `η` be a lift to `B/J`. Put `M = ker (B/J → B/IB)` with the
  `Λ/I`-module structure from `isTorsionBySet_ker`, `jM` the inclusion. The kernel has square
  zero, so `exists_cocycle_of_classLift` gives `c` with
  `(dif 1 ⊗ M)(c) + φ_* z = 0` for the obstruction map `φ`. `M` is killed by `p`
  (`isTorsionBySet_ker` with `hpI`), and `g₀` acts on `M` as the unit image of `g₀` in `B/J`,
  hence bijectively. By `hP` and `injVanishes_baseChange_iff`, `φ = 0`. By `jM_phiQ`, every
  `x ∈ I` maps to `0` in `B/J`, so `IB ≤ J`, contradicting `J < IB`.

### The main theorem

`classPresheaf_genericNonLifting A : UnramifiedFunctor.GenericNonLifting (classPresheaf A)`.
Proof, as implemented:

1. From nilpotency `I ≤ N`, so `I * I ≤ I * N = ⊥`. From `asIdeal_le_nilradical`,
   `p ≤ N`, so `p * I = ⊥`; and `I ≤ N ≤ p`.
2. Write `ξ' = ⟦L'⟧`. The relative space is compact (the published `isProper_relProj` and
   `QuasiCompact.compactSpace_of_compactSpace`). The published `exists_chartFrames`, applied to
   `toRel A f (Λ/I) (carrierBundle A L')` and the surjection `Λ → Λ/I` with nilpotent kernel
   `I`, gives `K`, `e`, `g` and the hypotheses of section `Steps`.
3. `I` and `κ(p)` become `Λ/I`-modules, and `I` a `Λ/p`-module, by `isTorsionBySet_ideal` and
   the fact that `I ≤ p` maps to `0` in `κ(p)`. Let `z₁ ∈ (Λ/p ⊗ C 2) ⊗[Λ/p] I` be the element
   with `red z₁ = red z` (via the inverse of `red`).
4. `injVanishes_residueField` gives `InjVanishes` over `Λ/I` at `κ(p)`. Two applications of
   `injVanishes_baseChange_iff` (for `Λ → Λ/I` and `Λ → Λ/p`) turn it into `InjVanishes` over
   `Λ/p` for `z₁` at `κ(p)`.
5. `z` is a cocycle by the published `dif_zObs` (with `I * I = ⊥`), so `z₁` is one by
   `rTensor_baseChange_eq_zero_of_red`.
6. `exists_injVanishes_spread` over the noetherian ring `Λ/p` applies. Its inputs: the Čech
   cochains over `Λ/p` are flat (published instance `flat_cochain`) and vanish above degree
   `card K.ι` (`subsingleton_cplx`); their cohomology is finite (`finiteCohomology_dif`); `I` is
   finite over `Λ/p` because `Λ` is noetherian; and `κ(p)` is flat over `Λ/p` because it is the
   fraction field of the domain `Λ/p` (`IsLocalization.flat`). It gives `g₀' ∈ Λ/p` with
   nonzero image in `κ(p)`. Choose a preimage `g₀ ∈ Λ`. Then `g₀ ∉ p`, so `t ∈ D(g₀)`.
7. For `D(g) ⊆ D(g₀)`, `g₀` is a unit in `Λ_g`
   (`PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit`). Apply
   `noLargerLift_of_injVanishesRed` with `B = Λ_g`. For a module `M` killed by `p` with `g₀`
   bijective, the spreading conclusion gives `InjVanishes` over `Λ/p` at `M`. Then
   `injVanishes_baseChange_iff` for `Λ → Λ/p` and `red z₁ = red z` give the required
   `InjVanishesRed`.

`noetherianTwoAxisClassGenericNonLifting` (namespace `Langlands.AlgebraicGeometry.Picard`)
applies `classPresheaf_genericNonLifting` to each noetherian `R` and abelian scheme `A` over
`Spec R`.

## Dependencies and scope

The proof uses only `propext`, `Classical.choice` and `Quot.sound`. Besides published Library
modules, the import closure contains two new supporting modules of this candidate:

- `Langlands.Cohomology.ModuleComplex.ObstructionInjectivitySpread`: `InjVanishes`,
  `InjVanishesRed`, `exists_injVanishes_spread` and the change of base ring lemmas (`red`,
  `injVanishes_baseChange_iff`, `rTensor_baseChange_eq_zero_of_red`).
- `Langlands.AlgebraicGeometry.Picard.TwoAxisClassObstruction`: `exists_cocycle_of_classLift`
  and `exists_classLift_of_cocycle`, built on the published openness-of-versality obstruction
  theory and the published (F4′) module `TwoAxisClassArtinianLiftingProof`.

None of the representability statements excluded by the task, or their proofs, are imported.

## Source

Condition (F8) is Murre's, from J. P. Murre, *Representation of unramified functors.
Applications (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp.
294, registered as `murre-1965-bourbaki-294-unramified-functors`. The Lean form is the
published `UnramifiedFunctor.GenericNonLifting`. Murre proves (F8) for the Picard-type functor
on printed p. 257 (PDF p. 16) with the obstruction in `H²` and generic base change of
cohomology. The proof here follows that idea at the level of Čech cochains. Lifting is
expressed by the cocycle equation `d c + φ_* z = 0`. Injectivity of `φ ↦ [φ_* z]` at the
generic point spreads to an open set by flatness and the finiteness of the cohomology of the
Čech complex. Derived `H²` is not used.
