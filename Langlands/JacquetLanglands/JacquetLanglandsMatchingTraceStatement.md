# Statement: the Jacquet–Langlands trace identity for matching test functions

The module `Langlands.JacquetLanglands.JacquetLanglandsMatchingTraceStatement` (namespace
`Langlands.JacquetLanglands`) states, as the proposition
`JacquetLanglandsMatchingTraceStatement.{u, uV, uW}`, that for a Jacquet–Langlands pair
`(ρ, ρ')` of representations of `GL_n(F)` and of the unit group of a central division algebra
`D` of dimension `n^2` over a `p`-adic field `F`, and for matching test functions `f` and `f'`
with regular supports, `Θ_ρ(f) = (-1)^(n-1) Θ_ρ'(f')`. The statement is **not proved** here.

## Sources

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*, in
  Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984; source ID `bdkv-1984-representations-local-field` (printed page =
  PDF page − 4). Cited as DKV.
  - Introduction, printed p. 33: the character of an admissible representation is the
    distribution `φ ↦ trace π(φ)` on the Hecke algebra, and on test functions supported in the
    regular set it is given by Harish-Chandra's locally constant character function;
    printed p. 34, c.: the main theorem, `(-1)^m χ_π' = (-1)^n χ_π` on the regular classes for
    `G' = GL(m, D)`, `G = GL(n, F)`.
  - B.2.a, printed p. 83: the bijection `π ↦ π'` is characterized by
    `(-1)^m trace π'(φ') = (-1)^n trace π(φ)` whenever the orbital integral of `φ ∈ H` is the
    orbital integral of `φ' ∈ H'` extended by `0`. For `m = 1` (so `d = n`), this reads
    `trace π(φ) = (-1)^(n-1) trace π'(φ')`.
- Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique non
  nulle*, Ann. Sci. ÉNS (4) 35 (2002), 695–747; source ID `badulescu-2002-jl-char-p`.
  - Théorème 1.1 (introduction, printed p. 696) and Théorème 5.1 (§5, printed p. 731): the
    character relation `χ_π(g) = (-1)^(n-r) χ_C(π)(g')` for corresponding `g`, `g'`; here
    `r = 1`.
  - §5, printed p. 733: corresponding test functions; §6 (Annexe), printed pp. 745–746: the
    scalar product of characters on the elliptic set (a sum over the elliptic maximal tori of
    `|W_T|⁻¹ ∫_{T^reg/Z} D(t) χ(t) χ'(t)‾ dt`), its comparison between `G` and `G'` through the
    isomorphisms of corresponding tori, which preserve the measures.

## Notation

`GL_n(F)` is the Library's `GeneralLinear n F = (Matrix (Fin n) (Fin n) F)ˣ`; `Dˣ` is Mathlib's
`Units D`. `SchwartzBruhat X` is `C^∞_c(X)` (module `Langlands.HarmonicAnalysis.Basic`). For an
admissible representation `ρ` of a locally profinite group `G`, a Haar measure `μ` and
`hρ : IsAdmissible ρ`, `Character.distribution μ ρ hρ f` (module
`Langlands.Representation.Character.Basic`) is the trace of the finite-rank operator
`ρ(f) v = ∫ f(g) ρ(g) v dμ(g)`: DKV's `trace π(φ)` for `φ = f dμ`. The predicates used are:

- `IsJacquetLanglandsPair F D n ρ ρ'` (module `Langlands.JacquetLanglands.Relation`): `D` has
  dimension `n^2`, `ρ` is irreducible, essentially square-integrable and admissible, `ρ'` is
  irreducible and admissible, and for every regular elliptic `g` and regular `g'` that
  correspond there is `c` such that the character of `ρ` has the local value `(-1)^(n-1) c` at
  `g` and that of `ρ'` the local value `c` at `g'` (`HasCharacterValue`). Its fields
  `h.isAdmissible` and `h.isAdmissible_right` are the admissibility proofs used to form the
  two distribution characters;
- `IsEllipticSupported f`, `IsDivisionRegularSupported F D f'` and `AreMatching μ μ' f f'` are
  as in `Langlands.JacquetLanglands.DivisionMatching` and
  `Langlands.BaseChange.EllipticSupport`: `f` vanishes off the regular elliptic elements, `f'`
  off the regular units, and `f` and `f'` have equal orbital integrals at corresponding
  elements (for associated measures on the centralizers and compatible quotient measures),
  the orbital integrals of `f` vanishing at the regular semisimple non-elliptic elements. No
  sign is built into the matching.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), let
`D : Type u` be a division ring with `[Algebra F D] [FiniteDimensional F D]
[Algebra.IsCentral F D]`, carrying its `F`-module topology (`[TopologicalSpace D]
[IsModuleTopology F D]`), and let `n : ℕ` with `Module.finrank F D = n ^ 2`. Give `GL_n(F)` and
`Dˣ` their Borel σ-algebras, make `D` a topological ring by
`Langlands.JacquetLanglands.isTopologicalRing F D`, and use the Hausdorff, locally compact and
totally disconnected structures of `GL_n(F)` and `Dˣ` from
`Langlands.JacquetLanglands.DivisionUnits` (`generalLinear_t2Space`,
`generalLinear_locallyCompactSpace`, `generalLinear_totallyDisconnectedSpace`, `units_t2Space`,
`units_locallyCompactSpace`, `units_totallyDisconnectedSpace`), as
`IsJacquetLanglandsPair` does. Then for all complex vector spaces `V : Type uV` and
`W : Type uW`, all representations `ρ` of `GL_n(F)` on `V` and `ρ'` of `Dˣ` on `W`, every
`h : IsJacquetLanglandsPair F D n ρ ρ'`, every Haar measure `μ` on `GL_n(F)` and `μ'` on `Dˣ`,
and all `f : SchwartzBruhat (GL_n(F))`, `f' : SchwartzBruhat Dˣ` with `IsEllipticSupported f`,
`IsDivisionRegularSupported F D f'` and `AreMatching μ μ' f f'`:

`Character.distribution μ ρ h.isAdmissible f = (-1) ^ (n - 1) * Character.distribution μ' ρ' h.isAdmissible_right f'`.

The hypothesis `Module.finrank F D = n ^ 2` is also a field of `h`
(`IsJacquetLanglandsPair.finrank_eq`); it is kept to state the common setting.

## Why it is true (proof sketch, not formalized)

1. **Character functions on the supports.** Every regular unit `g'` of `D` corresponds to a
   regular elliptic `g ∈ GL_n(F)` (`exists_corresponds`, with `n` the reduced degree of `D`),
   and every regular elliptic `g` corresponds to some `g'` (every extension of `F` of degree
   `n` embeds in `D`). So `h` gives locally constant character functions `θ_ρ` on the regular
   elliptic set and `θ_ρ'` on the regular set of `Dˣ`, constant on conjugacy classes, with
   `θ_ρ(g) = (-1)^(n-1) θ_ρ'(g')` for corresponding `g`, `g'`.
2. **Traces as integrals.** The support of `f` is compact and open and lies in the regular
   elliptic set; covering it by finitely many disjoint compact open sets on which
   `HasCharacterValue` applies gives `Θ_ρ(f) = ∫ f θ_ρ dμ`, and likewise
   `Θ_ρ'(f') = ∫ f' θ_ρ' dμ'`. No local integrability of characters is needed, because both
   supports stay inside the regular set.
3. **Weyl integration over elliptic tori.** With representatives `T_i` of the conjugacy classes
   of elliptic maximal tori of `GL_n(F)`, `T'_i` the corresponding tori of `Dˣ`, `ψ_i : T_i ≃ T'_i`
   induced by `F`-algebra isomorphisms, Haar measures `dt_i` on `T_i` and `dt'_i` their images
   under `ψ_i`:
   `∫ f θ_ρ dμ = Σ_i |W(T_i)|⁻¹ ∫_{T_i} D(t) θ_ρ(t) O_t(f) dt_i`, where `O_t(f)` is the orbital
   integral for the quotient measure `μ/dt_i` and `D(t)` the Weyl discriminant, and likewise on
   `Dˣ` with `T'_i`, `dt'_i` and `μ'`.
4. **Comparison.** `|W(T_i)| = |W(T'_i)|` (both are the automorphism group of the field
   `F[t]` over `F`, by Skolem–Noether on `Dˣ`), `D(t) = D(ψ_i(t))` (a function of the
   characteristic polynomial), `θ_ρ(t) = (-1)^(n-1) θ_ρ'(ψ_i(t))`, and `O_t(f) = O_{ψ_i(t)}(f')`
   by `AreMatching`, the measures `dt_i` and `dt'_i` being associated. Since `ψ_i` carries
   `dt_i` to `dt'_i`, the two sums agree up to the factor `(-1)^(n-1)`.

## Comparison with the sources (derived content)

- **Direction and scope.** DKV's B.2.a states that the trace identity characterizes the
  bijection, for all matching `φ ∈ H`, `φ' ∈ H'`. The statement here is one direction for
  `m = 1`, restricted to `f` supported in the regular elliptic set and `f'` supported in the
  regular set: the character relation on the regular elliptic set, encoded by
  `IsJacquetLanglandsPair`, implies the trace identity for such matching functions. The
  restriction removes the need for the local integrability of characters, and it is the form
  used in the spectral comparison of the simple trace formulas of `GL_n` and of a division
  algebra.
- **Sign.** DKV's `(-1)^m trace π'(φ') = (-1)^n trace π(φ)` with `m = 1` gives
  `trace π(φ) = (-1)^(n-1) trace π'(φ')`, the sign of `IsJacquetLanglandsPair` and of
  Badulescu's Théorème 1.1 with `r = 1`.
- **Measures.** DKV take traces of measures `φ = f dg`; here `Character.distribution μ ρ hρ f`
  uses the explicit Haar measure `μ`. Both sides of the identity and the matching relation are
  homogeneous in `(μ, μ')`: replacing `(μ, μ')` by `(a μ, b μ')` multiplies `Θ_ρ(f)` by `a` and
  `Θ_ρ'(f')` by `b`, and `f` matches `f'` for `(μ, μ')` if and only if `a⁻¹ b f` matches `f'`
  for `(a μ, b μ')`. So the statement for one pair of Haar measures is equivalent to the
  statement for all pairs.

## Hypotheses

- `CharZero F`, as in DKV; the Library's regularity notions ask for separable (reduced)
  characteristic polynomials, which is the sources' regularity in characteristic zero.
- `IsJacquetLanglandsPair F D n ρ ρ'` supplies irreducibility, admissibility, essential square
  integrability and the character relation; only the admissibility (to form the characters)
  and the character relation are used in the proof sketch.
- `IsEllipticSupported f` and `IsDivisionRegularSupported F D f'` keep the supports in the sets
  where `IsJacquetLanglandsPair` provides character values.
- No other hypothesis is added: the statement is for every such `F`, `D`, `n`, every pair of
  Haar measures and every representation in the universes `uV`, `uW`.

## Dependencies and names

The module imports `Langlands.JacquetLanglands.DivisionMatching` (`IsDivisionRegularSupported`,
`AreMatching`), `Langlands.JacquetLanglands.DivisionUnits` (the topological facts on `GL_n(F)`
and `Dˣ`), `Langlands.JacquetLanglands.Relation` (`IsJacquetLanglandsPair`),
`Langlands.Representation.Character.Basic` (`Character.distribution`),
`Langlands.HarmonicAnalysis.Basic` (`SchwartzBruhat`), and Mathlib's
`Mathlib.NumberTheory.LocalField.Basic` and `Mathlib.Topology.Algebra.Module.ModuleTopology`.
`IsEllipticSupported` comes from `Langlands.BaseChange.EllipticSupport` through these imports.
