# Statement: regular transfer from the units of a `p`-adic division algebra to `GL_n(F)`

The module `Langlands.JacquetLanglands.DivisionRegularTransferStatement` (namespace
`Langlands.JacquetLanglands`) states, as the proposition
`DivisionRegularTransferStatement.{u}`, that every Schwartz–Bruhat function on the unit group
of a central division algebra `D` of dimension `n^2` over a `p`-adic field `F`, supported in the
regular set, matches a Schwartz–Bruhat function on `GL_n(F)` supported in the regular elliptic
set. The statement is **not proved** here.

## Sources

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*, in
  Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984; source ID `bdkv-1984-representations-local-field` (printed page =
  PDF page − 4). Cited as DKV.
  - B.2.c 1), printed p. 83, for `G = GL(n, F)` and `G' = GL(m, D)`: every orbital integral of
    `G'`, extended by `0` at the regular classes of `G` that do not come from `G'`, is an
    orbital integral of `G`, and conversely every orbital integral of `G` vanishing off `G'` is
    of this form. Here `m = 1`, so `G' = Dˣ`. The regular classes of `G` that come from `Dˣ`
    are then the regular elliptic ones, so the extension by `0` vanishes off the elliptic set.
  - Introduction, printed p. 33: the Hecke algebra `H` of locally constant compactly supported
    measures; printed p. 36, f.: normalized orbital integrals on the regular set.
- Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique non
  nulle*, Ann. Sci. ÉNS (4) 35 (2002), 695–747; source ID `badulescu-2002-jl-char-p`.
  - §5, printed p. 733: the definition of corresponding functions `f` and `f'` supported in the
    regular semisimple set, the normalization of the measures on the elliptic tori, and the
    remark that for every `f'` there is a corresponding `f`, by Harish-Chandra's submersion
    theorem.
  - §6 (Annexe), printed pp. 745–746: the isomorphism `F[g]ˣ ≃ F[g']ˣ` of the centralizers of
    corresponding elements and the transport of measures between them.

## Notation

`GL_n(F)` is the Library's `GeneralLinear n F = (Matrix (Fin n) (Fin n) F)ˣ` with Mathlib's
topology on units of the matrix ring; `Dˣ` is Mathlib's `Units D` with its topology on units.
`SchwartzBruhat X` (module `Langlands.HarmonicAnalysis.Basic`) is the space `C^∞_c(X)` of
locally constant compactly supported functions `X → ℂ`, coerced to functions. For a measure `μ`,
`μ.IsHaarMeasure` is Mathlib's (left) Haar measure class; `GL_n(F)` and `Dˣ` are unimodular, so
these are all their Haar measures. The predicates used are:

- `IsEllipticSupported f` (`Langlands.BaseChange.EllipticSupport`): `f` vanishes off the regular
  elliptic elements of `GL_n(F)` (separable irreducible characteristic polynomial);
- `IsDivisionRegularSupported F D f'` (`Langlands.JacquetLanglands.DivisionMatching`): `f'`
  vanishes off the regular units of `D` (separable reduced characteristic polynomial);
- `AreMatching μ μ' f f'` (`Langlands.JacquetLanglands.DivisionMatching`): the orbital integrals
  of `f` vanish at the regular semisimple elements that are not regular elliptic, and at every
  pair `γ ∈ GL_n(F)`, `γ' ∈ Dˣ` with `Corresponds F D γ γ'` the orbital integral of `f` at `γ`
  equals that of `f'` at `γ'`, for all associated right Haar measures on the two centralizers
  and the quotient measures compatible with `μ`, `μ'` and them. No sign is built in.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), let
`D : Type u` be a division ring with `[Algebra F D] [FiniteDimensional F D]
[Algebra.IsCentral F D]`, carrying its `F`-module topology (`[TopologicalSpace D]
[IsModuleTopology F D]`), and let `n : ℕ` with `Module.finrank F D = n ^ 2`. Give `GL_n(F)` and
`Dˣ` their Borel σ-algebras (introduced locally with `letI ... := borel _` and `BorelSpace`
instances `⟨rfl⟩`), and make `D` a topological ring by `Langlands.JacquetLanglands.isTopologicalRing F D`
(module `Langlands.JacquetLanglands.DivisionUnits`), so that `Dˣ` is a topological group. Then
for every Haar measure `μ` on `GL_n(F)`, every Haar measure `μ'` on `Dˣ` and every
`f' : SchwartzBruhat Dˣ` with `IsDivisionRegularSupported F D f'`, there is
`f : SchwartzBruhat (GL_n(F))` with `IsEllipticSupported f` and `AreMatching μ μ' f f'`.

## Why it is true (proof sketch, not formalized)

This is the argument that Badulescu (§5, p. 733) summarizes as Harish-Chandra's submersion
theorem.

1. **Tori.** The maximal tori of `Dˣ` are the groups `Eˣ` for the subfields `E ⊆ D` of degree
   `n`; every regular `g'` lies in exactly one of them, `F[g']ˣ`, its centralizer. By the
   Skolem–Noether theorem their conjugacy classes correspond to the isomorphism classes of
   extensions `E/F` of degree `n`, and so do the conjugacy classes of elliptic maximal tori of
   `GL_n(F)`; there are finitely many such extensions. Choose representatives `T_i ⊆ GL_n(F)`,
   `T'_i ⊆ Dˣ` and the isomorphisms `ψ_i : T_i ≃ T'_i` induced by `F`-algebra isomorphisms; a
   regular `t ∈ T_i` corresponds to `ψ_i(t)`. Fix Haar measures `dt_i` on `T_i` and let
   `dt'_i` be their images under `ψ_i` (associated measures).
2. **The target function.** For a regular `t ∈ T_i` put `φ_i(t)`, the orbital integral of `f'`
   at `ψ_i(t)` for `μ'/dt'_i`. Since `Dˣ/Fˣ` is compact, the union of the conjugates of the
   support of `f'` is compact and contained in the regular set, so `φ_i` is locally constant
   with compact support in the regular part of `T_i`; it is invariant under the Weyl group
   `N(T_i)/T_i`, because orbital integrals are constant on conjugacy classes and `ψ_i`
   intertwines the normalizers.
3. **Submersion.** In characteristic zero the map
   `p_i : T_i^reg × (T_i\GL_n(F)) → GL_n(F)`, `(t, T_i x) ↦ x⁻¹ t x`, is a local
   homeomorphism (Harish-Chandra's submersion theorem) onto an open set `U_i` of regular
   elliptic elements. Its fibres are the orbits of the finite Weyl group
   `W_i = N(T_i)/T_i` acting by `w · (t, T_i x) = (w t w⁻¹, T_i w x)`, and this action is free
   because a regular `t` has centralizer `T_i`. So the fibres have `|W_i|` points and `p_i`
   is a covering map onto `U_i`. Choose `β_i ∈ C^∞_c(T_i\GL_n(F))` with integral `1` for the
   quotient measure `μ/dt_i`, put `Φ_i(t, T_i x) = φ_i(t) β_i(T_i x)`, and define `f_i` on
   `U_i` as the average of `Φ_i` over the fibre: `f_i(y) = |W_i|⁻¹ Σ_{p_i(z) = y} Φ_i(z)`.
   - *Support and local constancy.* `Φ_i` is locally constant with compact support
     `K_i = supp φ_i × supp β_i`. Since `p_i` is a covering map with finite fibres, `f_i` is
     locally constant on `U_i`, and it vanishes off `p_i(K_i)`, a compact subset of `U_i`.
     Extend `f_i` by `0` to `GL_n(F)`. The extension is locally constant on the open set `U_i`
     and is `0` on the open set `GL_n(F) \ p_i(K_i)` (a compact set is closed). These two open
     sets cover `GL_n(F)`, so `f_i ∈ C^∞_c(GL_n(F))`, with support in `p_i(K_i)`, which
     consists of regular elliptic elements.
   - *Orbital integrals.* For regular `t₀ ∈ T_i`, the fibre over `x⁻¹ t₀ x` consists of the
     points `(w t₀ w⁻¹, T_i w x)` for `w ∈ W_i`, so
     `f_i(x⁻¹ t₀ x) = |W_i|⁻¹ Σ_w φ_i(w t₀ w⁻¹) β_i(T_i w x)`. Conjugation by `w`
     preserves the Haar measure `dt_i` (an automorphism of `T_i = Eˣ` fixes the maximal compact
     subgroup `O_Eˣ`), and `μ` is bi-invariant, so `T_i x ↦ T_i w x` preserves the quotient
     measure `μ/dt_i`. With the Weyl invariance of `φ_i`, the orbital integral of `f_i` at
     `t₀` for `μ/dt_i` is `|W_i|⁻¹ Σ_w φ_i(t₀) · 1 = φ_i(t₀)`. At a regular semisimple element
     not conjugate into `T_i` the orbital integral of `f_i` is `0`, because `f_i` vanishes off
     `U_i`, which is a union of conjugacy classes.
4. **Conclusion.** `f = Σ_i f_i` is supported in the regular elliptic set, so its orbital
   integrals vanish off the elliptic set (`vanishesOffElliptic_of_isEllipticSupported`). At a
   corresponding pair `(γ, γ')`, `γ` is conjugate to some regular `t ∈ T_i` and `γ'` to `ψ_i(t)`
   (equal characteristic polynomials), and the orbital integrals agree for the measures of
   step 1. For other associated measures both sides change by the same factor, so
   `AreMatching μ μ' f f'` holds.

## Comparison with the sources (derived content)

- **Restricted form of DKV's B.2.c 1).** For `m = 1`, DKV transfer every `φ' ∈ H'` to some
  `φ ∈ H` whose orbital integrals vanish off the elliptic set; Badulescu (§5) transfers
  functions supported in the regular semisimple set. The statement here assumes that `f'` is
  supported in the regular set and asks for `f` supported in the regular elliptic set. The
  construction of the proof sketch provides this. It also follows from DKV's transfer by a
  cutoff along the characteristic polynomial:
  - Identify monic polynomials of degree `n` over `F` with `F^n` through their coefficients.
    The set `R` of separable irreducible ones is open (Krasner's lemma).
  - The reduced characteristic polynomial is a continuous map from `Dˣ` to `F^n`. It carries
    the compact set `{f' ≠ 0}` to a compact set `C`, and `C ⊆ R` because `f'` is supported in
    the regular set and a separable reduced characteristic polynomial is irreducible
    (`irreducible_reducedCharpoly_of_separable`).
  - Since `F^n` has a basis of compact open sets, there is a compact open `K` with
    `C ⊆ K ⊆ R`.
  - Let `φ` be a function on `GL_n(F)` matching `f'` as in B.2.c 1). Put `f = (1_K ∘ P) · φ`,
    where `P(g)` is the characteristic polynomial of `g`. Then `1_K ∘ P` is locally constant
    on all of `GL_n(F)`, because `K` is open and closed. So `f` is locally constant with
    compact support, and `f` vanishes off `P⁻¹(K)`, which consists of regular elliptic
    elements.
  - The function `1_K ∘ P` is constant on conjugacy classes, so the orbital integral of `f`
    at a regular semisimple `γ` is `1_K(P(γ))` times that of `φ`. This is `0` off the
    elliptic set. At a corresponding pair `(γ, γ')` it equals the orbital integral of `f'` at
    `γ'`. If `P(γ) ∈ K`, this is the equality for `φ`. If `P(γ) ∉ K`, both sides are `0`:
    `f'` vanishes on the conjugacy class of `γ'`, all of whose elements have reduced
    characteristic polynomial `P(γ) ∉ C`.

  Multiplying `φ` by the indicator of the regular elliptic set itself would not work. That set
  is open and closed in the regular semisimple set, but its indicator is not locally constant
  at singular elements, such as unipotent elements, that are limits of regular elliptic
  elements. This restricted form is the one used to compare the simple trace formula of `GL_n`
  with that of a division algebra, where test functions with regular elliptic support at a
  place isolate the regular elliptic terms. Keeping both supports regular keeps the
  statement's proof local.
- **Functions, measures and normalizations.** DKV transfer measures `φ = f dg`; here the Haar
  measures `μ`, `μ'` are explicit and arbitrary. The matching relation is homogeneous: if `f`
  matches `f'` for `(μ, μ')`, then `a⁻¹ b f` matches `f'` for `(a μ, b μ')`, `a, b > 0`. So the
  statement for one pair of Haar measures, for instance Badulescu's (volume `1` for
  `GL_n(O_F)` and `O_Dˣ`), is equivalent to the statement for all pairs. Orbital integrals are
  not normalized; see the Markdown of `Langlands.JacquetLanglands.DivisionMatching` for why this
  does not change the matching condition.
- **No central character.** Badulescu works with functions compactly supported modulo the
  centre with a central character; the statement uses compactly supported functions, as in
  DKV's Hecke algebra `H`.

## Hypotheses

- `CharZero F`: DKV work in characteristic zero; the Library's `IsRegularSemisimple`,
  `IsRegularElliptic` and `IsRegular` ask for a separable (reduced) characteristic polynomial,
  which is the sources' regularity in characteristic zero, and the submersion argument of the
  proof sketch uses characteristic zero.
- `Module.finrank F D = n ^ 2`: `D` has reduced degree `n`, so corresponding elements of
  `GL_n(F)` and `Dˣ` exist (`Langlands.JacquetLanglands.exists_corresponds` and
  `Corresponds.eq_reducedDegree`). It forces `n ≥ 1`.
- The module topology on `D` (`IsModuleTopology F D`) is the natural topology of the
  finite-dimensional `F`-algebra `D`; the topological facts on `Dˣ` used here are those of
  `Langlands.JacquetLanglands.DivisionUnits`.
- No other hypothesis is added: the statement is for every such `F`, `D`, `n` and every pair of
  Haar measures.

## Dependencies and names

The module imports `Langlands.JacquetLanglands.DivisionMatching` (`IsDivisionRegularSupported`,
`AreMatching`), `Langlands.JacquetLanglands.DivisionUnits` (`isTopologicalRing`),
`Langlands.HarmonicAnalysis.Basic` (`SchwartzBruhat`), and Mathlib's
`Mathlib.NumberTheory.LocalField.Basic` and `Mathlib.Topology.Algebra.Module.ModuleTopology`.
`IsEllipticSupported` comes from `Langlands.BaseChange.EllipticSupport` through these imports.
