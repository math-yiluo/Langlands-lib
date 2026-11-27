# Matching of test functions between `GL_n(F)` and the units of a central division algebra

Module `Langlands.JacquetLanglands.DivisionMatching`, namespace `Langlands.JacquetLanglands`.
Write `GL_n(F)` for the Library's `GeneralLinear n F`, the unit group
`(Matrix (Fin n) (Fin n) F)ˣ`, and `Dˣ` for Mathlib's unit group `Units D`.

The module defines what it means for a function `f` on `GL_n(F)` and a function `f'` on `Dˣ`,
`D` a central division algebra over `F`, to *match*: equal orbital integrals at corresponding
regular elliptic elements, for associated measures on the centralizers, and vanishing orbital
integrals of `f` at the regular semisimple elements that are not elliptic. These predicates
express the matching condition for regular transfer and the Jacquet–Langlands trace identity.

## Sources

- Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples `p`-adiques*, in
  Bernstein–Deligne–Kazhdan–Vignéras, *Représentations des groupes réductifs sur un corps
  local*, Hermann, 1984, pp. 33–117; source ID `bdkv-1984-representations-local-field`
  (printed page = PDF page − 4). Cited as DKV.
  - Introduction, printed p. 33: the Hecke algebra `H` of locally constant compactly
    supported measures, and the character `φ ↦ trace π(φ)`; printed p. 34, c.: the main
    theorem, a bijection between the square-integrable representations of `G' = GL(m, D)`
    and of `G = GL(n, F)` characterized by `(-1)^m χ_π' = (-1)^n χ_π` on the regular
    classes; printed p. 36, f.: the normalized orbital integral `F` of `φ ∈ H` on `G^rég`.
  - B.2, printed p. 83: `G = GL(n, F)`, `G' = GL(m, D)`. B.2.a: the bijection `π ↦ π'` is
    characterized by `(-1)^m trace π'(φ') = (-1)^n trace π(φ)` whenever the orbital integral
    of `φ ∈ H` is the orbital integral of `φ' ∈ H'` extended by `0`. B.2.c 1): every orbital
    integral of `G'` extended by `0` is an orbital integral of `G`, and conversely every
    orbital integral of `G` that vanishes off `G'` is of this form.
- Badulescu, *Correspondance de Jacquet–Langlands pour les corps locaux de caractéristique non
  nulle*, Ann. Sci. ÉNS (4) 35 (2002), 695–747; source ID `badulescu-2002-jl-char-p`.
  - §5, printed p. 733: functions `f` on `G_v` and `f'` on `G'_v`, supported in the regular
    semisimple set, *correspond* when their orbital integrals are equal at corresponding
    elements (`Φ(f; g) = Φ(f'; g')` for all `g ↔ g'`) and the orbital integral of `f` vanishes
    at every `g` that corresponds to no element of `G'`; the measures on the elliptic maximal
    tori `T` of `G_v` and `G'_v` are normalized by `vol(T/Z_v) = 1` for one Haar measure on the
    centre `Z_v`; for every `f'` there is a corresponding `f`, by Harish-Chandra's submersion
    theorem.
  - §6 (Annexe), printed pp. 745–746: for `g ↔ g'` there is a unique isomorphism of
    `F`-algebras `F[g] ≃ F[g']` sending `g` to `g'`; it gives an isomorphism of the elliptic
    maximal tori `F[g]ˣ` and `F[g']ˣ`, the centralizers of `g` and `g'`, which is the identity
    on the centre and therefore carries the normalized measure of one torus to that of the
    other.

DKV work in characteristic zero (their B.2 assumes that the characters are locally
integrable, which Harish-Chandra proved in characteristic zero, printed p. 34); Badulescu
treats every characteristic. The definitions below make sense over any topological field, but
their comparison with the sources (the sections "Associated measures" and "Comparison with the
sources" below) is asserted only in the local setting described next.

## Setting

- `F` is a field with a topology making it a topological ring; `D` is a division ring with a
  topology making it a topological ring; for `AreMatching`, `D` is moreover a
  finite-dimensional central `F`-algebra (`[Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]`). `GL_n(F)` carries Mathlib's topology on units of the matrix ring
  and `Dˣ` Mathlib's topology on units; both are topological groups. Subgroups carry the
  subspace topology.
- `GL_n(F)` and `Dˣ` carry supplied σ-algebras with `[BorelSpace _]`; subgroups carry the
  subtype σ-algebra. A left coset space `LeftQuotient H` (module
  `Langlands.Group.LeftQuotient`; its points are the cosets `H g`) carries its Borel σ-algebra:
  the module installs `Langlands.BaseChange.leftQuotientMeasurableSpace` with
  `attribute [local instance high]` and `Langlands.BaseChange.leftQuotient_borelSpace` with
  `attribute [local instance]`, exactly as `Langlands.BaseChange.OrbitalIntegral` does.
- Orbital integrals are the Library's `Langlands.TraceFormula.orbitalIntegral δ ν f`
  (module `Langlands.TraceFormula.TwistedOrbital`): the Bochner integral
  `∫ f(x⁻¹ δ x) dν(x)` over `LeftQuotient (twistedCentralizer (MonoidHom.id G) δ)`, for a
  supplied measure `ν`; it is `0` when the integrand is not integrable, and nothing is
  normalized.
- Quotient measures enter only through `Langlands.QuotientIntegration.IsCompatible H μG μH ν`
  (module `Langlands.Analysis.Local.QuotientMeasure`): `ν` is nonzero, regular and invariant
  under right translations, and `∫_{H\G} (∫_H f(h g) dμH(h)) dν = ∫_G f dμG` for every
  continuous compactly supported `f`, with integrability of the inner average. This is the
  source's quotient measure `dg/dt`.
- `IsRegularSemisimple`, `IsRegularElliptic`, `IsRegular F D` and `Corresponds F D` are those of
  `Langlands.JacquetLanglands.RegularElliptic`: `γ ∈ GL_n(F)` is regular semisimple when its
  characteristic polynomial is separable, regular elliptic when it is moreover irreducible;
  `g' ∈ Dˣ` is regular when its reduced characteristic polynomial is separable; and
  `Corresponds F D γ γ'` says that `γ` is regular elliptic, `γ'` is regular, and the
  characteristic polynomial of `γ` equals the reduced characteristic polynomial of `γ'`.
  `glCentralizer γ` is the Library's centralizer of `γ` in `GL_n(F)`
  (`Langlands.BaseChange.OrbitalIntegral`), and `IsEllipticSupported f` says that `f` vanishes
  off the regular elliptic set (`Langlands.BaseChange.EllipticSupport`).
- **The local setting.** `F` is a nonarchimedean local field; `D` is a central division algebra
  over `F` with `dim_F D = n^2`; `F`, `D` and `M_n(F)` carry their finite-dimensional
  `F`-module topologies, and `GL_n(F)` and `Dˣ` the induced topologies on units; the
  σ-algebras on `GL_n(F)`, `Dˣ` and their subgroups are the Borel σ-algebras; and the measures
  on the two groups and on the centralizers are Haar measures. This is the setting of the
  sources, and every comparison with them below is asserted in it only. The Lean definitions
  are stated more generally, and outside this setting some of these comparisons fail (see
  "Associated measures").

## Definitions and lemmas

1. **Regular support on `Dˣ`.** `IsDivisionRegularSupported F D f'`, for `f' : Dˣ → ℂ`: every
   `g'` with `f' g' ≠ 0` satisfies `IsRegular F D g'`. The lemmas
   `isDivisionRegularSupported_zero`, `IsDivisionRegularSupported.add` and
   `IsDivisionRegularSupported.const_mul` show that these functions form a subspace. Badulescu
   (§5, p. 733) uses functions supported in the regular semisimple set; on the units of a
   division algebra every regular element is elliptic (its reduced characteristic polynomial,
   being separable, is irreducible: `irreducible_reducedCharpoly_of_separable`).
2. **Centralizers.** `divisionCentralizer γ'`, for `γ' : Dˣ`, is the reducible abbreviation of
   `twistedCentralizer (MonoidHom.id Dˣ) γ'`, the subgroup `{x ∈ Dˣ | x⁻¹ γ' x = γ'}`;
   `divisionCentralizer_eq_centralizer` identifies it with Mathlib's
   `Subgroup.centralizer {γ'}`. It is written through `twistedCentralizer`, like
   `glCentralizer`, so that `LeftQuotient (divisionCentralizer γ')` is exactly the domain of
   the quotient measure in `orbitalIntegral γ' ν f'`. The lemmas
   `self_mem_twistedCentralizer_id`, `self_mem_glCentralizer` and
   `self_mem_divisionCentralizer` say that an element lies in its own centralizer.
3. **Associated measures.** `IsDivisionAssociatedMeasure γ γ' μγ μγ'`, for `γ : GL_n(F)`,
   `γ' : Dˣ`, a measure `μγ` on `glCentralizer γ` and a measure `μγ'` on
   `divisionCentralizer γ'`: there is an isomorphism of topological groups
   `φ : glCentralizer γ ≃ₜ* divisionCentralizer γ'` (Mathlib's `ContinuousMulEquiv`) with
   `φ γ = γ'` and `Measure.map φ μγ = μγ'`. See "Associated measures" below for its relation to
   the sources and for its nonvacuity. The lemma `isDivisionAssociatedMeasure_map` says that
   `Measure.map φ μγ` is associated with `μγ` for every such `φ`;
   `isMulRightInvariant_map_continuousMulEquiv` says that the image of a right invariant
   measure under an isomorphism of topological groups is right invariant (the image of a Haar
   measure is Haar by Mathlib's instance `ContinuousMulEquiv.isHaarMeasure_map`); and
   `exists_isDivisionAssociatedMeasure` combines them: given such a `φ`, every right Haar
   measure on `glCentralizer γ` has an associated right Haar measure on
   `divisionCentralizer γ'`.
4. **Vanishing off the elliptic set.** `OrbitalIntegralsVanishOffElliptic μ f`, for a measure `μ` on `GL_n(F)`
   and `f : GL_n(F) → ℂ`: for every `γ` with `IsRegularSemisimple γ` and
   `¬ IsRegularElliptic γ`, every right Haar measure `μγ` on `glCentralizer γ` (instance
   binders `IsHaarMeasure` and `IsMulRightInvariant`) and every `νγ` with
   `IsCompatible (glCentralizer γ) μ μγ νγ`, `orbitalIntegral γ νγ f = 0`. It is the analogue
   of `Langlands.BaseChange.VanishesOffNorms`. The lemmas `charpoly_conj` (conjugation does not
   change the characteristic polynomial) and `isRegularElliptic_conj_iff` give
   `vanishesOffElliptic_of_isEllipticSupported`: if `IsEllipticSupported f`, then
   `OrbitalIntegralsVanishOffElliptic μ f` for every `μ`, because `f` vanishes on the whole conjugacy class
   of an element that is not regular elliptic, so the integrand is `0`.
5. **Matching at a pair.** `MatchAt μ μ' f f' γ γ'`, for measures `μ` on `GL_n(F)` and `μ'` on
   `Dˣ`, `f : GL_n(F) → ℂ`, `f' : Dˣ → ℂ`, `γ : GL_n(F)` and `γ' : Dˣ`: for all right Haar
   measures `μγ` on `glCentralizer γ` and `μγ'` on `divisionCentralizer γ'`, all `νγ` with
   `IsCompatible (glCentralizer γ) μ μγ νγ` and all `νγ'` with
   `IsCompatible (divisionCentralizer γ') μ' μγ' νγ'`, if
   `IsDivisionAssociatedMeasure γ γ' μγ μγ'` then
   `orbitalIntegral γ νγ f = orbitalIntegral γ' νγ' f'`.
6. **Matching.** `AreMatching μ μ' f f'`: `OrbitalIntegralsVanishOffElliptic μ f`, and
   `MatchAt μ μ' f f' γ γ'` for every `γ : GL_n(F)` and `γ' : Dˣ` with
   `Corresponds F D γ γ'`. No sign is built in. The lemma
   `areMatching_iff_of_isEllipticSupported` says that for `f` with `IsEllipticSupported f`,
   `AreMatching μ μ' f f'` is equivalent to its second half.

The model is `Langlands.BaseChange.ConcordAt` and `Langlands.BaseChange.AreConcordant`
(Henniart–Lemaire 2011, I.2.5) for the identity twist, with the second group `GL_n(E)`
replaced by `Dˣ` and norms replaced by corresponding elements. The association of measures is
expressed by a continuous group isomorphism between the centralizers.

## Associated measures

The mathematical claims of this section are asserted in the local setting only (see
"Setting"), apart from the real counterexample at the end of "Equivalence", which shows why.
The Lean lemmas named here are proved in the module's general setting.

**The source's definition.** For `Corresponds F D γ γ'` let `P` be the common (separable,
irreducible, degree `n`) characteristic polynomial. Then `F[γ] ⊆ M_n(F)` and `F[γ'] ⊆ D` are
fields isomorphic to `F[X]/(P)`, and there is a unique `F`-algebra isomorphism
`F[γ] ≃ F[γ']` with `γ ↦ γ'` (Badulescu, §6, p. 746). The centralizer of `γ` in `GL_n(F)` is
`F[γ]ˣ`: `F^n` is a one-dimensional `F[γ]`-vector space, so the matrices commuting with `γ`
are the multiplications by elements of `F[γ]`. The centralizer of `γ'` in `Dˣ` is `F[γ']ˣ`:
`F[γ']` has degree `n` over `F` (by `reducedCharpoly_eq_minpoly_of_separable`, `P` is the
minimal polynomial of `γ'`), and by the double centralizer theorem its centralizer in `D`
has dimension `n^2 / n = n` and contains `F[γ']`. The `F`-algebra isomorphism restricts to a
group isomorphism `ψ : F[γ]ˣ ≃ F[γ']ˣ`. It is a homeomorphism: it is an `F`-linear bijection
of finite-dimensional subspaces of `M_n(F)` and `D` carrying their module topologies, and on
the units of these fields inversion is continuous, so the topologies induced from `GL_n(F)`
and `Dˣ` are the subspace topologies. The sources call right Haar measures `μγ` and `μγ'`
associated (Badulescu: "les mesures se correspondent") when `ψ` carries `μγ` to `μγ'`.

**Equivalence.** In the local setting, for Borel right Haar measures (`MatchAt` applies the
association predicate only to these; `OrbitalIntegralsVanishOffElliptic` does not use it, and involves only
one centralizer measure and its compatible quotient measures),
`IsDivisionAssociatedMeasure γ γ' μγ μγ'` holds if and only if `Measure.map ψ μγ = μγ'`.
Indeed `ψ` is one admissible `φ`. Conversely, if `φ` is any
isomorphism of topological groups between the centralizers, `α = ψ⁻¹ ∘ φ` is a continuous
automorphism of `Eˣ = F[γ]ˣ`, so `Measure.map α μγ = c • μγ` for some `c > 0`; the group
`O_Eˣ` of units of the ring of integers of the local field `E` is the unique maximal compact
subgroup of `Eˣ` (the absolute value maps a compact subgroup to a compact subgroup of
`ℝ_{>0}`, which is trivial), so `α(O_Eˣ) = O_Eˣ`, the two measures give `O_Eˣ` the same
finite positive volume, and `c = 1`. Hence `Measure.map φ μγ = Measure.map ψ μγ`. The
condition `φ γ = γ'` is not needed for this equivalence; it is kept because the sources'
isomorphism has this property. The argument uses the compact open subgroup `O_Eˣ`, which has
finite positive Haar measure, and the equivalence fails without it: for `F = D = ℝ` with their
usual topologies, `n = 1` and `γ = γ' = 1` (which correspond, with common polynomial `X - 1`),
both centralizers are all of `GL_1(ℝ) = ℝˣ` and the canonical identification `ψ` is the
identity, while the
continuous automorphism `x ↦ x^3` of `ℝˣ` fixes `1` and maps the Haar measure `dx / |x|` to
one third of itself (in the coordinate `log |x|` on each component it is multiplication by
`3`). So `IsDivisionAssociatedMeasure` relates `dx / |x|` to `(1/3) dx / |x|` there, whereas
transport by `ψ` relates it only to itself.

**The volume formulation.** Both `ψ` and its inverse are the identity on the centre `Fˣ`
(scalar matrices and scalars of `D`). Fix a Haar measure on `Fˣ`; the compact quotients
`F[γ]ˣ/Fˣ` and `F[γ']ˣ/Fˣ` then carry quotient measures, and two right Haar measures are
associated if and only if these quotients have the same volume, since `ψ` induces an
isomorphism of the quotients and a Haar measure is determined by the volume of the compact
quotient by `Fˣ`. Badulescu's normalization (§5, p. 733: `vol(T/Z_v) = 1` on every elliptic
maximal torus of `G_v` and `G'_v`) is the instance of this where both volumes are `1`; his
argument on p. 746 is the one just given.

**Nonvacuity.** In the local setting, for corresponding `γ` and `γ'` and every Borel right Haar
measure `μγ` on `glCentralizer γ`, the measure `Measure.map ψ μγ` is a right Haar measure on
`divisionCentralizer γ'` associated with `μγ`: this is `exists_isDivisionAssociatedMeasure`
applied to `ψ`. The module proves `exists_isDivisionAssociatedMeasure`, in its general
setting, for every supplied isomorphism of topological groups sending `γ` to `γ'`; the
construction of `ψ` described above is not formalized here.

## Comparison with the sources (derived content)

- **Functions and measures.** DKV integrate measures `φ = f dg` of the Hecke algebra
  (printed p. 33, p. 36 f.); here the test function `f` and the Haar measure `μ` are separate,
  and the orbital integral of `f` is taken with the quotient measure of `μ` by `μγ`, which is
  the orbital integral of the measure `f dμ` relative to the measure `μγ` on the torus.
- **Normalization of orbital integrals.** DKV compare normalized orbital integrals (printed
  p. 36 f.). The Library's `orbitalIntegral` is not normalized. A normalizing factor that is a
  function of the characteristic polynomial, such as the usual `|D(γ)|^{1/2}`, takes the same
  value at corresponding elements, so equality of normalized and of unnormalized orbital
  integrals at corresponding elements are the same condition.
- **All measures are quantified.** Badulescu fixes Haar measures on `G` and `G'` and
  normalizes the measures on the tori. Here `μ` and `μ'` are parameters, and `MatchAt`
  quantifies over all associated right Haar measures on the two centralizers and all
  compatible quotient measures. In the local setting, with `μ` and `μ'` Haar measures on
  `GL_n(F)` and `Dˣ`: for given `μ` and `μγ` there is exactly one compatible quotient measure
  (Weil's formula determines its integrals of continuous compactly supported functions, and it
  is regular), and likewise on `Dˣ`. Now let `γ` and `γ'` satisfy `Corresponds F D γ γ'`. An
  associated pair of right Haar measures exists (see "Nonvacuity" above). By "Equivalence",
  any two associated pairs differ by a common factor, `(c • μγ, c • μγ')` with `c > 0`, and
  replacing `(μγ, μγ')` by `(c • μγ, c • μγ')` divides both compatible quotient measures by
  `c`. So, in the local setting and for such a pair, `MatchAt μ μ' f f' γ γ'` is equivalent to
  the equality of the two orbital integrals computed with any one chosen associated pair of
  right Haar measures and its compatible quotient measures, for instance Badulescu's
  normalized pair. The hypothesis `Corresponds F D γ γ'` is needed. Without it no associated
  pair may exist: for `F = D = ℚ₃`, `n = 1`, `γ = 1` and `γ' = -1`, no group isomorphism
  sends `1` to `-1`, so `MatchAt` holds vacuously for all functions. `AreMatching` therefore
  applies `MatchAt` only to corresponding pairs. These facts are not proved here; they explain
  why the universal quantifiers express the sources' condition.
- **Vanishing condition.** Badulescu requires the orbital integral of `f` to vanish at every
  regular semisimple `g` corresponding to no element of `G'`. In the local setting, for
  `G' = Dˣ`, these are exactly the regular semisimple `g` that are not regular elliptic:
  a corresponding `g` is regular elliptic (`Corresponds` includes `IsRegularElliptic`; compare
  `corresponds_iff`), and conversely every regular elliptic `g` has a corresponding element of
  `Dˣ`, because every field extension of `F` of degree `n` embeds in `D`. That converse is a
  fact about central division algebras over local fields and is not proved here. DKV's
  B.2.c 1) ("nulle hors de `G'`") is the same condition.
- **Matching at corresponding pairs.** `AreMatching` asks for `MatchAt` at every pair with
  `Corresponds F D γ γ'`, which is Badulescu's `Φ(f; g) = Φ(f'; g')` for all `g ↔ g'`
  (Badulescu's `g ↔ g'` asks for regular semisimple elements with equal characteristic
  polynomials; `corresponds_iff` shows that this is `Corresponds F D g g'`).
- **Supports.** Badulescu restricts the definition to functions supported in the regular
  semisimple set and with a central character; DKV's B.2.a uses all of the Hecke algebra. The
  definitions here apply to arbitrary functions; the support conditions are hypotheses of the
  statements that use them.
- **No sign.** Matching is the plain equality of orbital integrals (DKV's "l'intégrale
  orbitale de `φ` est égale à l'intégrale orbitale de `φ'` prolongée par 0"); the sign
  `(-1)^(n-1)` appears only in the trace identity.

## Dependencies and names

The module imports `Langlands.JacquetLanglands.RegularElliptic`,
`Langlands.BaseChange.EllipticSupport`, `Langlands.BaseChange.OrbitalIntegral` (which brings
`Langlands.TraceFormula.TwistedOrbital` and `Langlands.Analysis.Local.QuotientMeasure`),
`Mathlib.MeasureTheory.Group.Measure` and `Mathlib.Topology.Algebra.ContinuousMonoidHom`.
The Library objects `IsRegularSemisimple`, `IsRegularElliptic`, `IsRegular`, `Corresponds`,
`orbitalIntegral`, `twistedCentralizer`, `glCentralizer`, `IsCompatible` and
`IsEllipticSupported` are used as published, not redefined. The names
`IsDivisionRegularSupported` and `IsDivisionAssociatedMeasure` avoid a clash with
`Langlands.BaseChange.IsRegularSupported` and `Langlands.BaseChange.IsAssociatedMeasure` when
both namespaces are open.
