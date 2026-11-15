# NYLL M166.002–M166.004: the abstract norm of a finite fixed field and its valuation (proofs)

This module proves the three published targets of
[`AbstractFixedFieldNorm.U002.Statements`](Statements.md) (NYLL source units
M166.002, M166.003 and M166.004). It declares three theorems in namespace
`Langlands.NYLL.LocalClassFieldTheory`, each under the adapted source name:

| Theorem (this module) | Target | Unit |
| --- | --- | --- |
| `normToBase_abstractFixedFieldUnit_val_of_isSeparable` | `normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement` | M166.002 |
| `localBaseValuation_normToBase_abstractFixedFieldUnit` | `localBaseValuation_normToBase_abstractFixedFieldUnitStatement` | M166.003 |
| `localBaseValuation_comp_normToBase_range_eq_residueFinrank` | `localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement` | M166.004 |

Each theorem has exactly the binders of its target: the same names
(including the named instance binder `hIntegralClosure` of M166.004), the
same kinds (explicit or instance) and the same order. Its type is the
target applied to those binders. No target or theorem has a level parameter.

```lean
theorem normToBase_abstractFixedFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (H : ClosedSubgroup (Gal(Ω/K)))
    [Finite ((baseField (Gal(Ω/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement K Ω H x

theorem localBaseValuation_normToBase_abstractFixedFieldUnit
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    localBaseValuation_normToBase_abstractFixedFieldUnitStatement K H x

theorem localBaseValuation_comp_normToBase_range_eq_residueFinrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] :
    localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement K H
```

## What the theorems say

Let `Ω / K` be Galois with `Ω` separably closed, `G = Gal(Ω / K)`, and `H` a
closed subgroup of finite index whose fixed field `E = Ω^H`
(`abstractFixedField K Ω H`) is finite-dimensional over `K`. The
class-formation norm `normToBase (galoisAmbientUnitsRep K Ω) H` sends an
`H`-fixed unit of `Ω` to the product of its conjugates `σ(y)` over left coset
representatives `σ` of `H` in `G` (written additively, as a sum).

- **M166.002.** If `E / K` is separable, then for `x ∈ Eˣ` the abstract norm
  of `x` (through `abstractFixedFieldUnitsEquivGaloisFixed K Ω H`), viewed in
  `Ω`, is `algebraMap K Ω (Algebra.norm K x)`, the image of the field norm
  `N_{E/K}(x)`.
- **M166.003.** Let `K` be a nonarchimedean local field and
  `Ω = SeparableClosure K`. For `x ∈ Eˣ`, the published base valuation
  `localBaseValuation K` of the abstract norm of `x` equals
  `valuationMap K (N_{E/K}(x))` cast into `ℤ̂ = ZHat`, where
  `normUnits K E x = N_{E/K}(x)` is the field norm on units.
- **M166.004.** In the setting of M166.003, give `E` its own nonarchimedean
  local field structure, with valuation extending that of `K`
  (`Valuation.HasExtension`) and `𝒪[E]` the integral closure of `𝒪[K]` in
  `E`. Let `f = Module.finrank 𝓀[K] 𝓀[E]` be the residue degree. Then the
  values of `localBaseValuation K` on the abstract norms of `H`-fixed units
  are exactly `nsmulImage (localBaseValuation K).range f`, that is, `f`
  times the values of `localBaseValuation K`: `v_K(N_{E/K}(Eˣ)) = f · v_K(Kˣ)`
  inside `ℤ̂`.

**Sign convention.** NYLL's `valuationMap` is the *negative* of the usual
normalized order `ord`: a prime element of `𝒪[K]` has value `-1`, so
`valuationMap K x = -ord(x)`. The same holds for NYLL's `v`, which
`valuationMap` evaluates to (`valuationMap_apply`). The word "normalized"
in the source docstrings refers to this map. M166.003 compares two values of
the same map. M166.004 is an equality of value sets, which negation maps onto
themselves. So neither statement depends on the sign. The proofs below never
use the sign either.

In M166.003 and M166.004 the field `E` lies in `SeparableClosure K`, so
`E / K` is separable; the targets have no separability binder, and Lean
finds the `Algebra.IsSeparable` instance needed by M166.002 and M162.019 by
instance search. It also finds `IsGalois K (SeparableClosure K)` and
`IsSepClosed (SeparableClosure K)`.

## Proofs

Each proof begins with `unfold` of its target, which replaces the goal (the
target applied to the binders) by its body, the type of the source theorem.
The remaining steps are the source steps, with the changes marked below.

### M166.002 (`normToBase_abstractFixedFieldUnit_val_of_isSeparable`)

1. `E := abstractFixedField K Ω H`. Let `y` be the `H`-fixed element
   `abstractFixedFieldUnitsEquivGaloisFixed K Ω H (Additive.ofMul x)`, and
   `yE` the element `intermediateFieldUnitsEquivGaloisFixed K Ω E
   (Additive.ofMul x)`, fixed by `closedFixingSubgroup K Ω E`.
2. `hy : yE.1 = y.1`: both are `x` viewed in `Additive Ωˣ`. The proof
   rewrites with the published `intermediateFieldUnitsEquivGaloisFixed_coe`
   (M088.007) and closes with the published
   `abstractFixedFieldUnitsEquivGaloisFixed_coe` (M101.002), reversed.
3. `hnorm` is the published M165.009 theorem
   `relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x`: the
   relative norm of `yE` from `closedFixingSubgroup K Ω E` to
   `closedFixingSubgroup K Ω ⊥`, viewed in `Ω`, is
   `algebraMap K Ω (Algebra.norm K x)`.
4. `htransport` is the published M166.001 theorem
   `relativeNorm_coe_eq_of_closedSubgroup_eq`, applied to the base subgroups
   `closedFixingSubgroup K Ω ⊥` and `baseField G`, the lower subgroups
   `closedFixingSubgroup K Ω E` and `H`, the inclusions
   `fixingSubgroupLeBase K Ω E` (M089.002) and `le_baseField H`, the
   equalities `closedFixingSubgroup_bot_eq_baseField K Ω` (M089.001) and
   `closedFixingSubgroup_abstractFixedField_eq K Ω H` (M099.002), and
   `yE`, `y`, `hy`. It says the two relative norms have the same underlying
   element of `Additive Ωˣ`. `htransport'` applies
   `z ↦ ((Additive.toMul z : Ωˣ) : Ω)` to both sides.
5. A `change` writes the goal with `y`, and
   `exact htransport'.symm.trans hnorm` closes it. `normToBase A H` is by
   definition `relativeNorm A (baseField G) H (le_baseField H)`.

The M165.009 theorem is applied as a term whose type is its Statement
definition; Lean unfolds the definition when it checks the term against the
expected equation. This proof is the source proof unchanged after the
`unfold`.

### M166.003 (`localBaseValuation_normToBase_abstractFixedFieldUnit`)

1. `E := abstractFixedField K (SeparableClosure K) H` and `a` is the
   abstract norm of `x`.
2. `ha : (baseFieldUnitsEquiv K).symm a = Additive.ofMul (normUnits K E x)`.
   The proof applies the injectivity of the published `baseFieldUnitsEquiv K`
   (M163.003), cancels with `apply_symm_apply`, reduces by `Subtype.ext`,
   `Additive.ext` and `Units.ext` to an equation in `SeparableClosure K`, and
   proves it by a three-step `calc`:
   - the abstract norm of `x`, in `SeparableClosure K`, is
     `algebraMap K _ (Algebra.norm K (x : E))` by M166.002 above;
   - this equals `algebraMap K _ ((normUnits K E x : Kˣ) : K)` by `rfl`.
     (Changed: the source writes `rw [LocalFieldTheory.normUnits_apply_coe]`,
     the M092.003 theorem. Its statement
     `normUnits_apply_coeStatement` is published in
     `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U003.Statements`,
     but its proof (Task 5951) is not. The published `normUnits K L` is
     `Units.map (Algebra.norm K)`, so both sides agree by definition; the
     source proof of M092.003 is also `rfl`. This discharges the M092.003
     fact in place; no M092.003 declaration is introduced.)
   - this equals the image of `Additive.ofMul (normUnits K E x)` under
     `baseFieldUnitsEquiv K`, viewed in `SeparableClosure K`, by the published
     `baseFieldUnitsEquiv_val K (normUnits K E x)` (M163.004), reversed.
3. `rw [show … = a from rfl]` names the abstract norm `a`. The published
   `localBaseValuation K` (M163.005) is the composite
   `Int.castRingHom ZHat ∘ valuationMap K ∘ (baseFieldUnitsEquiv K).symm`,
   so `change` restates the goal as
   `Int.castRingHom ZHat (valuationMap K ((baseFieldUnitsEquiv K).symm a)) = _`,
   and `rw [ha]` closes it.

### M166.004 (`localBaseValuation_comp_normToBase_range_eq_residueFinrank`)

After the `unfold`, a local fact is proved first:

```lean
have mem_nsmulImage_iff (Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat) :
    z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z := Iff.rfl
```

(Added: this is the M025.005 theorem `mem_nsmulImage_iff`, whose statement
`mem_nsmulImage_iffStatement` is published in
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.MemNsmulImageIffStatement`
but whose proof (Task 5948) is not. The local `have` has the same
proposition. It holds by definition, since the published `nsmulImage Z n` is
the image `Z.map (z ↦ n • z)`; the source proof is `rfl`. It is local to the
proof and introduces no declaration.)

Then `ext z` and `constructor` split the set equality into two inclusions.
Write `f` for `Module.finrank 𝓀[K] 𝓀[E]` as it appears in the target.

**Values of the norm are in `f · v_K(Kˣ)`.** `rintro ⟨a, rfl⟩` takes an
`H`-fixed element `a`. Let `x` be its preimage under
`abstractFixedFieldUnitsEquivGaloisFixed`; `rw [← hxa]` and a `change`
present the goal as `localBaseValuation K` of the abstract norm of
`Additive.toMul x`, which `rw [localBaseValuation_normToBase_abstractFixedFieldUnit]`
(M166.003 above) turns into
`Int.castRingHom ZHat (valuationMap K (Additive.ofMul (normUnits K E (Additive.toMul x))))`.

`hnorm` is the published M162.019 theorem
`v_normUnits_eq_residue_finrank_mul_of_isSeparable` for `K`, `E` and
`Additive.toMul x`, with its twelve other instance arguments found by
unification and instance search and with `hIntegralClosure` passed
explicitly, as in the source. Its statement is
`v K (Additive.ofMul (normUnits K E y)) = (f : ℤ) * v E (Additive.ofMul y)`.
`hnorm'` is a copy of `hnorm` in which the U019 Statement definition is
unfolded, and `rw [← IsNonarchimedeanLocalField.valuationMap_apply,
← IsNonarchimedeanLocalField.valuationMap_apply, ofMul_toMul] at hnorm'`
rewrites both values of `v` into values of `valuationMap`, by the published
M134.004 theorem `valuationMap_apply : valuationMap K x = v K x`, and
removes `Additive.ofMul (Additive.toMul x) = x`. So

```
hnorm' : valuationMap K (Additive.ofMul (normUnits K E (Additive.toMul x))) =
    (f : ℤ) * valuationMap E x
```

with the same `f` as the target. Then `rw [hnorm', mem_nsmulImage_iff]`
reduces the goal to finding `w` in `(localBaseValuation K).range` with
`f • w = Int.castRingHom ZHat ((f : ℤ) * valuationMap E x)`. The witness is
`w = Int.castRingHom ZHat (valuationMap E x)`, in the range by the published
`intToProCInteger_mem_localBaseValuation_range K _` (M163.008). The
remaining equation follows from `rw [← map_nsmul, nsmul_eq_mul]`, which moves
`f •` inside the ring homomorphism and writes `f • m` as `(f : ℤ) * m`.

**Every element of `f · v_K(Kˣ)` is a value of the norm.**
`rw [mem_nsmulImage_iff]` and `rintro ⟨w, hw, hwz⟩` give `w` in the range
and `hwz : f • w = z`. The published `localBaseValuation_range K` (M163.007)
says the range is the range of `(Int.castRingHom ZHat).toAddMonoidHom`, so
`w` is the cast of an integer `m`. The published `valuationMap_surjective` (M134.005) gives
`x ∈ Additive Eˣ` with `valuationMap E x = m`. The witness is the `H`-fixed
element `abstractFixedFieldUnitsEquivGaloisFixed K (SeparableClosure K) H x`.
As in the first inclusion, a `change`, M166.003 and `hnorm'` turn the goal
into `Int.castRingHom ZHat ((f : ℤ) * valuationMap E x) = z`. Then
`rw [hnorm', hx, ← hwz, ← map_nsmul, nsmul_eq_mul]` turns it into
`Int.castRingHom ZHat ((f : ℤ) * m) =
(Int.castRingHom ZHat).toAddMonoidHom ((f : ℤ) * m)`. The right side applies
the additive homomorphism underlying `Int.castRingHom ZHat`, in which
`localBaseValuation_range` is stated. The two sides are definitionally
equal, and `rfl` closes the goal.

**Changes from the source in M166.004.**

- The local `have mem_nsmulImage_iff … := Iff.rfl` is added, as above.
- The source begins with `let f := Module.finrank 𝓀[K] 𝓀[E]` and states
  `hnorm'` with `(f : Int)`, proved by `exact hnorm`. That `let` is dropped.
  In this import context, elaborating `Module.finrank 𝓀[K] 𝓀[E]` inside the
  proof picks a residue-field module instance built from
  `IsLocalRing.ResidueField.algebraOfIsIntegral`. The target and the U019
  statement use the instance `IsLocalRing.ResidueField.instModule`, and Lean
  does not accept the two as definitionally equal (Worker 85's probe
  recorded that `rfl` and `exact` fail). So `hnorm'` is obtained from
  `hnorm` by unfolding and rewriting, as described above, and keeps the
  finrank of the target and the U019 theorem.
- The source states `hnorm'` with `valuationMap`; the published U019 theorem
  is stated with `v`. The two rewrites by `valuationMap_apply` bridge this.
- The source closes the first inclusion with `rw [← map_nsmul]; congr 1`,
  and the second with `rw [hnorm', hx]` and a `calc` through
  `f • Int.castRingHom ZHat m` and `hwz`. Here the first ends with
  `rw [← map_nsmul, nsmul_eq_mul]`, and the second with
  `rw [hnorm', hx, ← hwz, ← map_nsmul, nsmul_eq_mul]` and `rfl`. These steps
  prove the same equations.

## Dependencies

The imports, all published in the Library, are:

| Module (`...` = `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.`) | Used for |
| --- | --- |
| `...AbstractFixedFieldNorm.U002.Statements` | the three targets; through it `normToBase`, `nsmulImage`, `le_baseField`, `baseField`, `extensionSubgroup`, `abstractFixedField`, `abstractFixedFieldUnitsEquivGaloisFixed`, `galoisAmbientUnitsRep`, `localBaseValuation`, `baseFieldUnitsEquiv`, `normUnits`, `valuationMap`, `ZHat` |
| `...AbstractFixedFieldNorm.U001.Proofs` | `relativeNorm_coe_eq_of_closedSubgroup_eq` (M166.001) |
| `...SeparableFixedFieldNorm.U009.Proofs` | `relativeNorm_intermediateFieldUnit_val_of_isSeparable` (M165.009) |
| `...AbsoluteUnitsFixedField.FixedUnitsEquiv.U007.Proofs` | `intermediateFieldUnitsEquivGaloisFixed_coe` (M088.007), and through it `intermediateFieldUnitsEquivGaloisFixed` (M088.006) |
| `...AbstractFixedFieldUnits.Initial.U002.Proofs` | `abstractFixedFieldUnitsEquivGaloisFixed_coe` (M101.002) |
| `...GaloisExtensionQuotient.Initial.U001.Proofs` | `closedFixingSubgroup_bot_eq_baseField` (M089.001) |
| `...FiniteAbstractFixedField.Initial.U002.Proofs` | `closedFixingSubgroup_abstractFixedField_eq` (M099.002) |
| `...HenselianValuationBase.U004.Proofs` | `baseFieldUnitsEquiv_val` (M163.004), `localBaseValuation_range` (M163.007), `intToProCInteger_mem_localBaseValuation_range` (M163.008) |
| `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U019.Proofs` | `v_normUnits_eq_residue_finrank_mul_of_isSeparable` (M162.019) and its Statement definition |
| `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs` | `IsNonarchimedeanLocalField.valuationMap_surjective` (M134.005) |
| `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs` | `IsNonarchimedeanLocalField.valuationMap_apply` (M134.004) |

`fixingSubgroupLeBase` (M089.002) and `closedFixingSubgroup` come through
these imports. The last two rows are in namespace
`Langlands.NYLL.LocalFieldTheory`. From Mathlib the proofs use
`Subtype.ext`, `Additive.ext`, `Units.ext`, `ofMul_toMul`, `map_nsmul`,
`nsmul_eq_mul` and the `Equiv`/`AddEquiv` lemmas `injective` and
`apply_symm_apply`.

The M166.002 proof uses the M165.009 theorem by name, from its published
proof module `...SeparableFixedFieldNorm.U009.Proofs` (artifact
`463c5c24-7e6b-492a-8922-30e3e762c635`, same task). The M165.009 proof
uses the published instance `Langlands.NYLL.PortInternal.M164.d001` with
`attribute [local instance]` in place of the source's private section
instance `finiteSeparableAlgHomFintype` (M165.007); its Markdown records
this. The present module neither uses nor publishes M165.007.

No helper declaration is introduced, and no published declaration is
modified. The module keeps the source opens
`RamificationTheory CyclicCohomology KummerTheory ClassFormation`,
`LocalFieldTheory` and scoped `ValuativeRel` (for the notation `𝒪[·]` and
`𝓀[·]`), inside a `noncomputable section`. The target module needs
`set_option linter.unusedVariables false in` before M166.004 because its
proposition does not mention `hIntegralClosure`. The theorem here needs no
such option: its proof passes `hIntegralClosure` to the M162.019 theorem, and
the module compiles without warnings.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over Library
commit `9ed11fc606807fab34c4852a4e88dbabebba69d1`, which contains the
M165.009 proof module above, compiled the module with zero errors and zero
warnings.
Inspection of each of the three theorems reported kind `theorem`, no level
parameters, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not acceptance.

## Source correspondence and modification record

The original declarations are in Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean)
(SHA-256 `f4529e6c10db2c36c8c1dd88506cb999bd030618c1800f1d1ab96ab604e5f4fd`).
The namespace and opens are at lines 21–30, the section variables at lines
31–32.

- M166.002: docstring lines 65–67, statement lines 68–80, proof lines
  81–106.
- M166.003: docstring lines 108–109, statement lines 110–128, proof lines
  129–170.
- M166.004: docstring lines 172–174, statement lines 175–199, proof lines
  200–277.

| Original declaration | Adapted declaration |
| --- | --- |
| `theorem LocalClassFieldTheory.normToBase_abstractFixedFieldUnit_val_of_isSeparable` (M166.002) | `theorem Langlands.NYLL.LocalClassFieldTheory.normToBase_abstractFixedFieldUnit_val_of_isSeparable` (this module) |
| `theorem LocalClassFieldTheory.localBaseValuation_normToBase_abstractFixedFieldUnit` (M166.003) | `theorem Langlands.NYLL.LocalClassFieldTheory.localBaseValuation_normToBase_abstractFixedFieldUnit` (this module) |
| `theorem LocalClassFieldTheory.localBaseValuation_comp_normToBase_range_eq_residueFinrank` (M166.004) | `theorem Langlands.NYLL.LocalClassFieldTheory.localBaseValuation_comp_normToBase_range_eq_residueFinrank` (this module) |
| `LocalFieldTheory.normUnits_apply_coe` (M092.003, used; source proof `rfl`) | not used; the step is closed by `rfl` (proof unpublished) |
| `ClassFormation.mem_nsmulImage_iff` (M025.005, used; source proof `rfl`) | local `have mem_nsmulImage_iff … := Iff.rfl` (proof unpublished) |
| `LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable` (M165.009, used) | same name under `Langlands.NYLL` (proof module `...SeparableFixedFieldNorm.U009.Proofs`) |
| `LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable` (M162.019, used) | same name under `Langlands.NYLL` (published proof) |
| other used source declarations listed under Dependencies | same names under `Langlands.NYLL` (published) |

Worker 731 made these changes on 15 November 2026:

- the namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`;
- for M166.002 the section variables `K`, `Ω` and their five instance
  binders (lines 31–32) are written as explicit leading binders, followed by
  the theorem's own binders, as in the target; M166.003 and M166.004 keep
  their own binders;
- each conclusion is written as its target applied to the binders, and each
  proof begins with `unfold` of its target;
- in M166.003 the step `rw [LocalFieldTheory.normUnits_apply_coe]` becomes
  `rfl`;
- in M166.004 the local `have mem_nsmulImage_iff … := Iff.rfl` is added, the
  `let f` is dropped, `hnorm'` is obtained by unfolding the U019 statement
  and rewriting with `valuationMap_apply` and `ofMul_toMul`, and the closing
  steps of the two inclusions use `nsmul_eq_mul` (and in the second `hwz`
  and `rfl`) instead of `congr 1` and the final `calc`;
- the source imports are replaced by the eleven published modules listed
  above;
- the docstrings and the remaining tactic steps are the source's, unchanged.

The registered source is `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are
unchanged in the Library. Worker 731 adapted these proofs from the pinned
original, following the route of Worker 85's private development probe
recorded in the task. These support proofs discharge no host
class-formation, cohomology or reciprocity target.
