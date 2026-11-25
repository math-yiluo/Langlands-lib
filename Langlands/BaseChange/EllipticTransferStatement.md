# Statement: transfer of test functions supported in the elliptic set

The module `Langlands.BaseChange.EllipticTransferStatement` (namespace
`Langlands.BaseChange`) states, as the proposition `EllipticTransferStatement.{u, v}`, the
regular transfer of test functions for cyclic base change of `GL_n` restricted to functions
supported in the (σ-)elliptic set: such functions have concordant partners that are again
supported in the (σ-)elliptic set. The statement is **not proved** here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL.
  - I.2.5, Définition (printed p. 17): concordant functions; I.2.5, Proposition (printed
    p. 18): (1) every `φ` supported in `G(E)_{σ-r}` is concordant with some `f` supported in
    `G(F)_r`; (2) every `f` supported in `G(F)_r` whose orbital integrals vanish at the
    non-norms is concordant with some `φ` supported in `G(E)_{σ-r}`. This is
    `RegularTransferStatement`.
  - II.1.2 (printed pp. 55–56): the sets `G(F)_e` and `G(E)_{σ-e}`.
  - II.6.3 (printed p. 120) and II.6.4 (printed p. 121): the simple trace formula and its
    σ-twisted form, under the condition `c_{v₁}(f)` (`f_{v₁}` vanishes off the regular
    elliptic elements, and is a combination of coefficients of cuspidal representations) and
    its twisted analogue `c^σ_{v₁}(φ)`; II.6.6, continued at the top of printed p. 123: the
    comparison of the two formulas for concordant `φ` and `f` satisfying `c_{v₁}(f)` and
    `c^σ_{v₂}(φ)`.
  - II.6.10 (printed pp. 125–126): concordant pairs `(φ_v, f_v)` at every place, supported in
    `G(E_v)_{σ-r} × G(F_v)_r` at the places of `S` other than `v₁`.

## The statement

Let `F : Type u` be a nonarchimedean local field of characteristic zero (`[Field F]
[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`), let
`E : Type v` be a commutative `F`-algebra with `[TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, `σ : E ≃ₐ[F] E`, `l n : ℕ`, and assume `IsCyclicAlgebra σ l`
(`Langlands.BaseChange.Norm`: `E` is a finite reduced `F`-algebra of dimension `l`, `σ` has order `l`, and the
σ-fixed elements are those of `F`). Let `GL_n(F)` and `GL_n(E)` carry their Borel σ-algebras
(introduced locally with `letI ... := borel _` and `BorelSpace` instances `⟨rfl⟩`). For all
Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`:

- **(1)** for every `φ : SchwartzBruhat (GL_n(E))` with `IsSigmaEllipticSupported σ l φ`
  there is `f : SchwartzBruhat (GL_n(F))` with `IsEllipticSupported f` and
  `AreConcordant σ l μF μE φ f`;
- **(2)** for every `f : SchwartzBruhat (GL_n(F))` with `IsEllipticSupported f` and
  `VanishesOffNorms σ l μF f` (the orbital integrals of `f` vanish at every regular
  semisimple `γ` that is not a norm) there is `φ : SchwartzBruhat (GL_n(E))` with
  `IsSigmaEllipticSupported σ l φ` and `AreConcordant σ l μF μE φ f`.

`IsEllipticSupported` and `IsSigmaEllipticSupported` are defined in
`Langlands.BaseChange.EllipticSupport`; `AreConcordant` and `VanishesOffNorms`
are defined in `Langlands.BaseChange.OrbitalIntegral`, the latter being the first half of `AreConcordant`.

## Use

In the global comparison of HL II.6.7–II.6.10 (printed pp. 123–126), the simple trace formula
and its twisted form (II.6.3–II.6.4) need, at one place `v₁`, test functions supported in the
regular elliptic set and in the σ-elliptic set, and the comparison needs concordant pairs
`(φ_v, f_v)` at every place. This statement provides concordant pairs that keep the elliptic
support on both sides: from an elliptic-supported `φ_v` one gets an elliptic-supported `f_v`
and conversely. Stating it separately keeps the global argument free of the cut-off by the
indicator of the elliptic set.

## Proof idea (not formalized)

Combine `RegularTransferStatement` (HL I.2.5, Proposition) with a cut-off by the
indicator of the elliptic set. Two separate facts are used: the elliptic sets are open and
closed in the regular sets, which keeps the cut-off function locally constant with compact
support, and they are unions of (σ-)conjugacy classes, which controls the orbital integrals of
the cut-off function. The first fact is proved with characteristic polynomials, not with
conjugacy invariance.

1. **Characteristic polynomials.** For `γ ∈ GL_n(F)` let `P_γ ∈ F[X]` be its characteristic
   polynomial; `IsRegularSemisimple γ` says that `P_γ` is separable, and `IsRegularElliptic γ`
   that `P_γ` is separable and irreducible over `F`. For `δ ∈ GL_n(E)` let
   `N(δ) = δ · δ^σ ⋯ δ^{σ^{l-1}}` (`cyclicNorm σ l δ`). Since `σ^l = 1`,
   `N(δ)^σ = δ⁻¹ N(δ) δ` (`entrywiseAut_cyclicNorm`), so the coefficients of the
   characteristic polynomial of `N(δ)` are fixed by `σ` and lie in `F` (`IsCyclicAlgebra`);
   call this polynomial `P_δ ∈ F[X]`. If `δ` is associated with `γ`, then `P_δ = P_γ`. Hence a
   σ-regular `δ` has separable `P_δ`, a σ-elliptic `δ` has separable and irreducible `P_δ`, and
   a σ-regular `δ` with irreducible `P_δ` is σ-elliptic (its associated regular semisimple `γ`
   has `P_γ = P_δ`, so is regular elliptic).
2. **Continuity.** The coefficients of `P_γ` are polynomial in the entries of `γ`. The
   automorphism `σ` is `F`-linear on the finite-dimensional `E`, hence continuous for the
   module topology, so `δ ↦ N(δ)` is continuous; the coefficients of `P_δ` are therefore
   continuous functions with values in the image of `F` in `E`, on which the module topology
   induces the topology of `F`. So `γ ↦ P_γ` and `δ ↦ P_δ` are continuous into the space `F^n`
   of monic polynomials of degree `n`.
3. **Openness and closedness.** In `F^n`, the set `Sep` of separable polynomials is open
   (nonzero discriminant), and its subset `Irr` of irreducible polynomials is open and closed
   in `Sep`: by Krasner's lemma, the factorization type over the nonarchimedean local field `F`
   of a separable polynomial does not change under small perturbations of its coefficients.
   Let `U = {δ : P_δ ∈ Sep}` and `U_e = {δ : P_δ ∈ Irr ∩ Sep}`; both are open in `GL_n(E)`,
   `U_e` is closed in `U`, the σ-regular set lies in `U`, and by step 1 the σ-elliptic set is
   the intersection of the σ-regular set with `U_e`. The same holds on `GL_n(F)`, with
   `G(F)_r = {γ : P_γ ∈ Sep}` and `G(F)_e = {γ : P_γ ∈ Irr ∩ Sep}`.
4. **The cut-off is again a test function.** Let `φ'` be locally constant with compact support
   and supported in the σ-regular set. Its nonvanishing set `S` is open, closed and compact,
   and `S ⊆ U`. Then `S ∩ U_e` and `S \ U_e = S ∩ (U \ U_e)` are both open, so `S ∩ U_e` is
   open and closed in `GL_n(E)`, and `φ = φ' · 1_{U_e} = φ' · 1_{S ∩ U_e}` is locally constant
   with compact support and supported in the σ-elliptic set. The same argument applies to
   `f' · 1_{G(F)_e}` for `f'` supported in `G(F)_r`.
5. **Orbital integrals.** Conjugation does not change `P_γ`, and σ-conjugation does not change
   `P_δ` (`cyclicNorm_twistedConj`: `N(x⁻¹ δ x^σ) = x⁻¹ N(δ) x` when `σ^l = 1`). So `1_{U_e}`
   is constant on each σ-conjugacy class and `1_{G(F)_e}` on each conjugacy class: the
   σ-orbital integral of `φ' · 1_{U_e}` at `δ` is that of `φ'` if `P_δ` is irreducible and `0`
   otherwise, and likewise for `f' · 1_{G(F)_e}` at `γ`.

For (1), a σ-elliptic-supported `φ` is σ-regular-supported
(`IsSigmaEllipticSupported.isSigmaRegularSupported`), and regular transfer gives a concordant
`f'` supported in `G(F)_r`. Put `f = f' · 1_{G(F)_e}`, an elliptic-supported test function by
step 4. Its orbital integrals at the regular non-norms are `0` or those of `f'`, hence vanish.
At an associated pair `(δ, γ)` with `γ` regular semisimple: if `γ` is regular elliptic, the
orbital integral of `f` at `γ` is that of `f'`, which equals the σ-orbital integral of `φ` at
`δ`; otherwise `P_δ = P_γ` is reducible, no element of the σ-conjugacy class of `δ` is
σ-elliptic (step 1), so `φ` vanishes on that class, and both integrals are `0` (step 5).
Part (2) is symmetric: an elliptic-supported `f` is regular-supported, regular transfer gives a
concordant `φ'` supported in the σ-regular set, and `φ = φ' · 1_{U_e}` is a σ-elliptic-supported
test function (step 4); at an associated pair `(δ, γ)` with `γ` regular elliptic the integrals
are unchanged, and otherwise the σ-orbital integral of `φ` is `0` (step 5) and so is the
orbital integral of `f`, which vanishes on the conjugacy class of `γ`. The vanishing off the
norms is a hypothesis on `f`.

## Hypotheses

- `CharZero F`, as in the statements on orbital integrals, twisted characters and functions
  whose orbital integrals vanish off the elliptic set: the Library's `IsRegularSemisimple` and
  `IsRegularElliptic` ask for a separable characteristic polynomial, which is HL's regularity
  (II.1.2) in characteristic zero; the regular transfer used in the proof idea is
  `RegularTransferStatement`, which also assumes `CharZero F`. In characteristic zero, `IsEllipticSupported`
  and `IsSigmaEllipticSupported` are HL's support conditions in `G(F)_e` and `G(E)_{σ-e}`.
  For the σ-elliptic set this also uses HL I.2.2: the elements associated with `δ` form one
  conjugacy class. For imperfect `F` the Library's notions would be strictly smaller. The
  Markdown of `Langlands.BaseChange.EllipticSupport` explains both points.
- `IsCyclicAlgebra σ l` and the module topology on `E` (`IsModuleTopology F E`) give the
  setting of HL: a cyclic algebra over `F` with its natural topology.
- In (2), `VanishesOffNorms σ l μF f` is necessary, since it is part of `AreConcordant`
  (HL I.2.5, Proposition (2)).

## Measures

Every measure is quantified: the statement holds for all Haar measures `μF` and `μE`, and the
right Haar measures on the centralizers and the compatible quotient measures are quantified
inside `AreConcordant` and `VanishesOffNorms`. Nothing is normalized.

## Dependencies and names

The module imports `Langlands.BaseChange.EllipticSupport`,
`Langlands.BaseChange.OrbitalIntegral` (`AreConcordant`, `VanishesOffNorms`) and the
Library's `Langlands.HarmonicAnalysis.Basic` (`SchwartzBruhat`);
`IsCyclicAlgebra` (`Langlands.BaseChange.Norm`) comes through these imports. The names and
argument orders are those of the published declarations.
