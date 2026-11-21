# Herbrand's theorem for quotients and the tower laws in any characteristic

Worker 988 authors this statement unit for Task 7421. It states, over the general
finite-level declarations of `Herbrand.GeneralFinite` (Task 7403), the six
quotient and tower properties whose p-adic forms are in
`Herbrand/ArithmeticStatement.lean`, and their conjunction. All seven are
Prop-valued definitions in `Langlands.Ramification.Local`. They are targets for
later proof tasks; nothing here proves them, and none of them is used as a
hypothesis of a construction. The module contains no hypothesis on any
characteristic.

## Fields, embeddings and realizations

The module has four fields in independent universes `u₀`, `uK`, `uE`, `uL`:

- the base `K₀`, implicit in the six components, with
  `[Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]`. This is exactly the
  structure that Task 7403's `LocalField.TopologicalData K₀ L` requires of its
  base. The intended bases are `K₀ = K` (with Task 7403's
  `localTopologicalData K L`) for a nonarchimedean local field `K` of either
  characteristic, and `K₀ = Padic p` for the published p-adic layer;
- `K`, with `[Field K] [Algebra K₀ K]`;
- `L`, with `[Field L] [Algebra K₀ L] [FiniteDimensional K₀ L] [Algebra K L]
  [IsScalarTower K₀ K L]`;
- for the three tower components, `E`, with `[Field E] [Algebra K₀ E]
  [FiniteDimensional K₀ E] [Algebra K E] [Algebra E L]` and the towers
  `K₀ → K → E`, `K₀ → E → L` and `K → E → L`.

Every component takes `[IsGalois K L]`. The tower components also assume
`[IsGalois K E]`: `E/K` need not be Galois just because `L/K` is Galois. This
assumption supplies the normality of `E/K` for `AlgEquiv.restrictNormalHom` in
`UpperRestrictionCompatibility` and corresponds to the normal-subgroup setting
of Serre IV §3 Propositions 14–15. In contrast, `[IsGalois E L]` follows from
`[IsGalois K L]` in the compatible tower by `IsGalois.tower_top_of_isGalois`.
It is kept explicit to match the p-adic interface.

`T : LocalField.TopologicalData K₀ L` is an arbitrary realization of `L`: a
topology, a valuative relation extending that of `K₀`, the `K₀`-module topology
and a certificate that `L` is a nonarchimedean local field. When needed,
`S : LocalField.TopologicalData K₀ E` realizes `E` in the same way. Task 7403
builds its lower groups, Herbrand functions and upper groups from the integer
ring `T.Integers` of the realization (respectively `S.Integers`). These components are stated
in the generality of Task 7403's finite-level declarations: every field and
realization argument that the p-adic statement fixes as a `PadicField` or quantifies
over is a parameter here, and the p-adic statements are the case `K₀ = Padic p`
(see the comparison below).

Serre's hypotheses hold in this generality. `T` makes `L` a nonarchimedean local
field: complete under a discrete valuation, with finite and hence perfect residue
field. `L` is finite over `K`, because it is finite over `K₀` and `K₀ → K → L` is
a tower. Hence every residue extension that occurs is separable.

## Supporting instances

Two instances make the actual fixed field usable as a carrier over `K₀`. For
`H : Subgroup (L ≃ₐ[K] L)`:

- `fixedFieldScalarTower K L H : IsScalarTower K₀ (fixedField H) L`, proved by
  `IsScalarTower.of_algebraMap_eq` with the algebra-map equality holding by `rfl`.
  This is the general form of the p-adic `fixedFieldPadicScalarTower`.
- `fixedField_finiteDimensional K L H : FiniteDimensional K₀ (fixedField H)`.
  The fixed field is a `K₀`-subspace of the finite-dimensional `L`
  (`FiniteDimensional.finiteDimensional_submodule` applied to its restriction of
  scalars).

The `K₀`-algebra structure on `fixedField H` is Mathlib's intermediate-field
structure. No replacement carrier is introduced: the statements use
`IntermediateField.fixedField H` itself, which the p-adic module packages as
`fixedPadicField K L H` with the same carrier. These two instances are internal
packaging, not arithmetic hypotheses.

## The statements

Write `G = Gal(L/K)`, `E_H = L^H` for the actual fixed field
`IntermediateField.fixedField H`, `G_u = lowerRamificationGroupReal T K u` (Serre's
`G_⌈u⌉`), `G^v = upperRamificationGroup T K v`, and `φ`, `ψ` for `herbrandPhi`
and `herbrandPsi`. Printed page numbers of Serre, *Local Fields*, are seven
less than the PDF page numbers.

- `LowerSubgroupCompatibility K L T`: for every subgroup `H` of `G`, with no
  normality hypothesis, and every real `u ≥ -1`, the image of the lower group of
  `L/E_H` under `AlgEquiv.restrictScalarsHom K` equals `G_u ⊓ H`. This is
  `H_i = G_i ∩ H` of Serre IV §1 Proposition 2 (p. 62), extended to real indices
  by the ceiling convention of IV §3 (p. 73). The map forgets that an
  automorphism fixes `E_H`; it does not restrict its domain.
- `HerbrandNormalSubgroup K L T`: for every normal subgroup `H`, every realization
  `S : LocalField.TopologicalData K₀ (fixedField H)` of the fixed field, and every
  real `u ≥ -1`, the image of `G_u` under the restriction
  `AlgEquiv.restrictNormalHom` to `E_H` is the lower group of `E_H/K` at
  `φ_(L/E_H)(u)`. This is Herbrand's theorem, Serre IV §3 Lemma 5 (p. 75), where
  the source writes the image as `G_u H/H`; restriction to the fixed field
  identifies `G/H` with `Gal(E_H/K)`. (Serre's 2019 corrections change the glyph
  `φ` to `ϕ` in Lemma 5 and at p. 74 line −7; the function is the same.)
- `UpperQuotientCompatibility K L T`: with the same quantifiers over `H`, its
  normality and `S`, and every real `v ≥ -1`, the image of `G^v` under the same
  restriction is the upper group of `E_H/K` at `v`. This is Serre IV §3
  Proposition 14 (stated p. 74, proved p. 75).
- `HerbrandPhiTower K L E T S`: for every real `u`,
  `φ_(L/K)(u) = φ_(E/K)(φ_(L/E)(u))`.
- `HerbrandPsiTower K L E T S`: for every real `v`,
  `ψ_(L/K)(v) = ψ_(L/E)(ψ_(E/K)(v))`.
  These are the two formulas of Serre IV §3 Proposition 15 (stated p. 74, proved
  p. 75). The compositions have opposite orders. Serre states them on his domain
  `[-1, ∞)`. Here they are stated for every real index, as the task requires. Below
  `0` all the functions are the identity in Task 7403's construction, and the
  published p-adic tower theorems of `Herbrand/TowerProof.lean` already hold for
  every real index.
- `UpperRestrictionCompatibility K L E T S`: for every real `v ≥ -1`, the image
  of `G^v` under the restriction `AlgEquiv.restrictNormalHom` to `E` is the upper
  group of `E/K` at `v`. This is Proposition 14 for an independently presented
  compatible carrier `E`. The algebra `E → L` identifies `E` with its image in
  `L`.
- `FiniteHerbrandQuotientTower K₀ K L E`: for every `T` and every `S`, the
  conjunction of the six components above. It adds no assertion beyond them.

The subgroup and quotient components keep the domain `-1 ≤ u` (or `-1 ≤ v`) of the
p-adic statements. The tower laws have no lower bound.

## Relation to the p-adic statements

The p-adic objects are the general ones at `K₀ = Padic p` with
`T.toLocalData : LocalField.TopologicalData (Padic p) L.Carrier` (Task 7403's
in-place scheme). A private check file compiled the following `example`s in this
environment, with `K L E : PadicField p` and the p-adic instance hypotheses of
`Herbrand/ArithmeticStatement.lean` (`Padic` and `Local` abbreviate
`Langlands.Ramification.Padic` and `Langlands.Ramification.Local`):

```lean
example [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) :
    Padic.LowerSubgroupCompatibility K L T ↔
      Local.LowerSubgroupCompatibility K.Carrier L.Carrier T.toLocalData :=
  Iff.rfl

example (T : L.TopologicalData) (S : E.TopologicalData) :
    Padic.UpperRestrictionCompatibility K L E T S ↔
      Local.UpperRestrictionCompatibility K.Carrier L.Carrier E.Carrier
        T.toLocalData S.toLocalData :=
  Iff.rfl

-- the tower laws: the p-adic statement is the general body with `-1 ≤ u` added
example (T : L.TopologicalData) (S : E.TopologicalData) :
    Padic.HerbrandPhiTower K L E T S ↔
      ∀ u : ℝ, -1 ≤ u →
        Local.herbrandPhi T.toLocalData K.Carrier u =
          Local.herbrandPhi S.toLocalData K.Carrier
            (Local.herbrandPhi T.toLocalData E.Carrier u) :=
  Iff.rfl

example (T : L.TopologicalData) (S : E.TopologicalData) :
    Local.HerbrandPhiTower K.Carrier L.Carrier E.Carrier T.toLocalData S.toLocalData ↔
      ∀ u : ℝ,
        Local.herbrandPhi T.toLocalData K.Carrier u =
          Local.herbrandPhi S.toLocalData K.Carrier
            (Local.herbrandPhi T.toLocalData E.Carrier u) :=
  Iff.rfl

example (T : L.TopologicalData) (S : E.TopologicalData) :
    Padic.HerbrandPsiTower K L E T S ↔
      ∀ v : ℝ, -1 ≤ v →
        Local.herbrandPsi T.toLocalData K.Carrier v =
          Local.herbrandPsi T.toLocalData E.Carrier
            (Local.herbrandPsi S.toLocalData K.Carrier v) :=
  Iff.rfl

example (T : L.TopologicalData) (S : E.TopologicalData) :
    Local.HerbrandPsiTower K.Carrier L.Carrier E.Carrier T.toLocalData S.toLocalData ↔
      ∀ v : ℝ,
        Local.herbrandPsi T.toLocalData K.Carrier v =
          Local.herbrandPsi T.toLocalData E.Carrier
            (Local.herbrandPsi S.toLocalData K.Carrier v) :=
  Iff.rfl
```

`HerbrandNormalSubgroup` and `UpperQuotientCompatibility` quantify over the
realization of the fixed field. The p-adic statement quantifies over
`(fixedPadicField K L H).TopologicalData` and the general one over
`LocalField.TopologicalData (Padic p) (fixedField H)`. These are different
structure types with the same fields, so the two statements are not literally
`Iff.rfl`. They are equivalent by instantiating the quantifier through the
published field-by-field repackagings `toLocalData` and `ofLocalData`, and each
body is then definitionally the other:

```lean
example [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) :
    Padic.HerbrandNormalSubgroup K L T ↔
      Local.HerbrandNormalSubgroup K.Carrier L.Carrier T.toLocalData :=
  ⟨fun h H _ S => h H (PadicField.TopologicalData.ofLocalData S),
    fun h H _ S => h H S.toLocalData⟩
```

The same two-line proof checks `UpperQuotientCompatibility`. The aggregate at the
p-adic base unfolds by `Iff.rfl` to the conjunction of the six general components
quantified over all `T : LocalField.TopologicalData (Padic p) L.Carrier` and
`S : LocalField.TopologicalData (Padic p) E.Carrier`. The p-adic aggregate
`FiniteHerbrandArithmetic` also contains `HerbrandPsiIntegral` and
`HasseArfIntegrality`, which this task leaves out.

| General statement (`Langlands.Ramification.Local`) | P-adic counterpart (`Langlands.Ramification.Padic`) | Relation at `K₀ = Padic p` |
| --- | --- | --- |
| `LowerSubgroupCompatibility K L T` | `LowerSubgroupCompatibility K L T` | `Iff.rfl` with `T.toLocalData` |
| `HerbrandNormalSubgroup K L T` | `HerbrandNormalSubgroup K L T` | equivalent by `ofLocalData`/`toLocalData` |
| `UpperQuotientCompatibility K L T` | `UpperQuotientCompatibility K L T` | equivalent by `ofLocalData`/`toLocalData` |
| `HerbrandPhiTower K L E T S` | `HerbrandPhiTower K L E T S` | p-adic = general body with `-1 ≤ u`, `Iff.rfl` |
| `HerbrandPsiTower K L E T S` | `HerbrandPsiTower K L E T S` | p-adic = general body with `-1 ≤ v`, `Iff.rfl` |
| `UpperRestrictionCompatibility K L E T S` | `UpperRestrictionCompatibility K L E T S` | `Iff.rfl` with `T.toLocalData`, `S.toLocalData` |
| `FiniteHerbrandQuotientTower K₀ K L E` | six of the eight clauses of `FiniteHerbrandArithmetic K L E` | conjunction of the above |
| `fixedFieldScalarTower`, `fixedField_finiteDimensional` | `fixedFieldPadicScalarTower`, finiteness inside `fixedPadicField` | supporting instances |

## Declaration audit

The complete unapplied types were printed with universes. `LowerSubgroupCompatibility`
takes `{K₀}` and its three instances, `K`, `[Field K]`, `[Algebra K₀ K]`, `L`,
`[Field L]`, `[Algebra K₀ L]`, `[Algebra K L]`, `[IsScalarTower K₀ K L]`,
`[IsGalois K L]` and `T`, and returns `Prop`. It does not take
`[FiniteDimensional K₀ L]`, because its body uses no Herbrand function.
`HerbrandNormalSubgroup` and `UpperQuotientCompatibility` take in addition
`[FiniteDimensional K₀ L]` after `[Algebra K₀ L]`. The two composition laws take
the parameters of `L`, then `E`, `[Field E]`, `[Algebra K₀ E]`,
`[FiniteDimensional K₀ E]`, `[Algebra K E]`, `[Algebra E L]`, the towers
`K₀ → K → E`, `K₀ → E → L`, `K → E → L`, the Galois hypotheses for `L/K`, `E/K`,
`L/E`, then `T` and `S`. `UpperRestrictionCompatibility` has the same parameters
except the unused tower `K₀ → E → L`, as in the p-adic module. The aggregate
`FiniteHerbrandQuotientTower` takes `K₀` explicitly with the same instance list as
the composition laws, quantifies `T` and `S` inside, and has type `Prop` with four
universe parameters.

## Source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979): Chapter IV, hypotheses p. 61 (PDF 68); §1 Proposition 2, p. 62
(PDF 69); §3 real-index conventions, Propositions 14–15 and Lemma 5, pp. 73–75
(PDF 80–82). Registered source `serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Serre's
Chapter IV assumes only a complete discretely valued field with separable residue
extensions, so the cited results apply in both characteristics. The registered
author corrections `serre-book-corrections-2019` (Local Fields, PDF pp. 2–3)
change only the glyph of φ at p. 74 line −7 and in Lemma 5.

This unit does not edit the published p-adic statement module, the proof modules,
or the definition modules of Tasks 7403 and 7404.
