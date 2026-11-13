# Openness of the norm subgroup of a finite Galois extension of a local field

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpenStatement`
with the theorem
`Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpen`. This is
unit M257.007 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m257).
Let `L/K` be a finite Galois extension of a nonarchimedean local field `K`.
The theorem says that the image of the field norm `Lˣ → Kˣ` is open in the
native topology of `Kˣ`.

## Target and theorem

The only NYLL import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements`,
which the task requires. The file does not change that statement or
anything it imports. The published target and the theorem are:

```lean
def localNormSubgroup_isOpenStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  IsOpen (localNormSubgroup K L : Set Kˣ)

theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : localNormSubgroup_isOpenStatement K L
```

The theorem keeps the target's eight binders in the source order:
explicit `K L : Type`, then the instance arguments `Field K`, `Field L`,
`Algebra K L`, `FiniteDimensional K L`, `IsGalois K L`, `ValuativeRel K`,
`TopologicalSpace K` and `IsNonarchimedeanLocalField K`. It adds no
hypotheses. `L` has no topology, valuation or normed structure, and `L/K` need
not be abelian. `localNormSubgroup K L` is the published
`(normUnits K L).range`, where `normUnits K L = Units.map (Algebra.norm K)`.
`Kˣ` has Mathlib's unit-group topology, induced from `K`.

The proof uses `IsGalois K L` only through Mathlib's derived instance
`Algebra.IsSeparable K L`, which gives an element of nonzero trace. The local
quotient instance `Langlands.NYLL.PortInternal.M257.d001` is not needed,
because the proof never uses the quotient topology.

## Implemented proof

The proof is elementary. It does not use the source's route.

1. **Element of nonzero trace** (lines 269–271). Since `L/K` is finite and
   separable, Mathlib's `Algebra.trace_ne_zero K L` says the trace map
   `Algebra.trace K L` is nonzero. So some `c : L` has
   `Algebra.trace K L c ≠ 0`.
2. **An integral matrix** (lines 272–278). Let `b := Module.finBasis K L` and
   `M := Algebra.leftMulMatrix b c`. The helper `exists_mul_mem_integer` gives
   a nonzero `β : K` with `β * M i j ∈ 𝒪[K]` for every entry. Let
   `A : Matrix _ _ 𝒪[K]` be the matrix with entries `β * M i j`.
3. **The polynomial** (lines 279–290). Let `g := Matrix.charpolyRev (-A)`.
   This is `det (1 + X • A)` in `𝒪[K][X]`. Mathlib's
   `Matrix.eval_charpolyRev` gives `g.eval 0 = 1`, and
   `Matrix.coeff_charpolyRev_eq_neg_trace` gives
   `g.coeff 1 = Matrix.trace A`. In `K`, `Matrix.trace A` equals
   `β * Algebra.trace K L c` by `Algebra.trace_eq_matrix_trace`, so it is
   nonzero.
4. **Values of `g` are norms** (lines 291–305). For `t : 𝒪[K]`, apply the
   ring hom `φ = 𝒪[K].subtype ∘ evalRingHom t` to `det (1 + X • A)` with
   `RingHom.map_det`. Entrywise, `φ.mapMatrix (1 + X • A)` equals
   `Algebra.leftMulMatrix b (1 + (t * β) • c)`, because `leftMulMatrix b` is
   an algebra hom. By `Algebra.norm_eq_matrix_det b`, this gives
   `(g.eval t : K) = Algebra.norm K (1 + (t * β) • c)`.
5. **Hensel step** (line 306). The helper `exists_eval_eq_one_add` applies to
   `g` over the DVR `𝒪[K]`. It gives `ϖ ≠ 0` in `𝒪[K]` such that every
   `1 + ϖ * z` with `z : 𝒪[K]` is a value `g.eval t`.
6. **A neighbourhood of `1` lies in the norm subgroup** (lines 307–325). Let
   `y : Kˣ` satisfy `valuation K (y - 1) < valuation K ϖ`. Then
   `z := (y - 1) / ϖ` lies in `𝒪[K]`, and `y = 1 + ϖ z = N(x)` with
   `x = 1 + (t * β) • c`. Since `y ≠ 0`, `Algebra.norm_ne_zero_iff` gives
   `x ≠ 0`, so `normUnits K L (Units.mk0 x _) = y`.
7. **Topology** (lines 326–331). The set
   `{x : K | valuation K (x - 1) < valuation K ϖ}` is a neighbourhood of `1`
   by `IsValuativeTopology.mem_nhds_iff'`, with radius the unit
   `Units.mk0 (valuation K ϖ) _`. Since `Units.val` is continuous, the
   preimage of this set is a neighbourhood of `1` in `Kˣ`, and it lies inside
   the norm subgroup. So `Subgroup.isOpen_of_mem_nhds` shows the subgroup is
   open.

Mathlib provides the needed structure on `𝒪[K]` from
`IsNonarchimedeanLocalField K`: the instances `IsDiscreteValuationRing 𝒪[K]`
and `IsAdicComplete 𝓂[K] 𝒪[K]` in `Mathlib/NumberTheory/LocalField/Basic.lean`.
The second instance needs a compatible uniform structure. As Mathlib does in
the same file for `IsDiscreteValuationRing 𝒪[K]`, the proof introduces
`IsTopologicalAddGroup.rightUniformSpace K` and
`isUniformAddGroup_of_addCommGroup` locally (lines 267–268). These are
proof-internal and do not change the theorem's type.

## Helper declarations

All helpers are in namespace `Langlands.NYLL.PortInternal.M257.D007`. They are
general lemmas, not source declarations.

- `exists_root_of_isAdicComplete` (lines 48–131) is Newton's method without a
  monicity hypothesis. Let `R` be `I`-adically complete, `f : R[X]` and
  `a₀ : R` with `f.eval a₀ ∈ I` and `f'.eval a₀` a unit modulo `I`. Then some
  root `a` of `f` satisfies `a - a₀ ∈ I`. The proof adapts the proof of
  Mathlib's instance `IsAdicComplete.henselianRing`
  (`Mathlib/RingTheory/Henselian.lean:170–262`), which never uses its
  monicity hypothesis. Mathlib's `HenselianRing` interface only covers monic
  polynomials, and the rescaled polynomial in the next helper need not be
  monic.
- `coeff_comp_C_mul_X` (lines 133–143): the coefficients of `g(aX)` are
  `a ^ j * g.coeff j`. The proof is by induction on `g`.
- `exists_eval_eq_one_add` (lines 145–220) is the DVR core. Let `R` be a
  complete DVR and `g : R[X]` with `g.eval 0 = 1` and `g.coeff 1 ≠ 0`. Then
  there is `ϖ ≠ 0` such that for every `z`, some `t` has
  `g.eval t = 1 + ϖ z`. Write `g.coeff 1 = u π^k` with `u` a unit and `π` a
  uniformizer, and set `ϖ = π^(2k+1)`. Then
  `Q(X) = g(π^(k+1) X) - (1 + ϖ z)` is divisible by `C ϖ`. Write `Q = ϖ h`.
  Then `h ≡ -z + u X` modulo the maximal ideal. `h` has the simple residual
  root `z u⁻¹`, so the Newton lemma gives a root `s`. Then `t = π^(k+1) s`
  works.
- `exists_mul_mem_integer` (lines 222–250): for any valuation `v` on a field
  and any finite family `f`, there is a nonzero `β ∈ v.integer` with every
  `β * f i ∈ v.integer`. The proof is by `Finset` induction. Each step
  multiplies by `1` or by `x⁻¹` when `v x > 1`.

## Dependencies

The proof uses the published `localNormSubgroup`, `normUnits` and target
from the U006 statements module and its imports. It also uses these Mathlib
modules: `RingTheory.Henselian`, `RingTheory.DiscreteValuationRing.Basic`,
`LinearAlgebra.Matrix.Charpoly.Coeff`, `RingTheory.Trace.Basic`,
`RingTheory.Norm.Basic` and `Topology.Algebra.OpenSubgroup`. It does not use
local reciprocity, M257.002–M257.006, spectral norms, valuations on `L`,
`Valuation.HasExtension` or `IsIntegralClosure`. The axioms are the standard
`propext`, `Classical.choice` and `Quot.sound`. The approved environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Source correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`.
The passage is lines 215–331: an `open … in` prefix at 215–217, the
docstring at 218–219, the theorem at 220–225, and the proof at 226–331. The
file read has SHA-256
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`. It is
retained in the registered source `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`.

| Original (`LocalClassFieldTheory`) | Here (`Langlands.NYLL.LocalClassFieldTheory`) |
| --- | --- |
| `localNormSubgroup_isOpen`, binders and conclusion at lines 220–225 | `localNormSubgroup_isOpen : localNormSubgroup_isOpenStatement K L`, same binders |
| Docstring at lines 218–219 | Retained verbatim |
| Proof at lines 226–331 | Replaced by the elementary proof above |

The source proof builds a normed-field structure on `L` from the spectral
norm. From it, the source derives the topology, a valuation, the local-field
structure, `Valuation.HasExtension` and `IsIntegralClosure 𝒪[L] 𝒪[K] L`. It
then applies the private M257.006 theorem
`localNormSubgroup_isOpen_of_compatibleLocalField`. The source proof of that
theorem uses the local reciprocity isomorphism, which is not yet published. This
implementation proves the same target directly and so does not depend on
M257.006. It neither assumes M257.006's conclusion nor adds structure to the
target. Per the task contract, the proof route may differ from the source.
Downstream, M257.008 (`normQuotient_discrete`) can apply this theorem as in
the source.

## Attribution and licences

The Lean file keeps the original NYLL header verbatim: copyright 2026
Naganori Yamaguchi, Apache-2.0, author Naganori Yamaguchi (assisted by OpenAI
Codex). It adds a dated modification record by Worker 65, 13 November 2026,
for the replaced proof and the helpers. The helper
`exists_root_of_isAdicComplete` adapts Mathlib code. That code is copyright
2021 Johan Commelin and released under Apache-2.0, the licence Mathlib uses.
The modification record credits it.

The inherited [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are already in the
Library and are unchanged. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 65
wrote this proof and this companion. No other worker's draft was reused.
