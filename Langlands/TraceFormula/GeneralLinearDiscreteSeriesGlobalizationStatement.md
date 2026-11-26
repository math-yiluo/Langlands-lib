# Globalization of a square-integrable representation of `GL_n` with two supercuspidal places

Module `Langlands.TraceFormula.GeneralLinearDiscreteSeriesGlobalizationStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.GeneralLinearDiscreteSeriesGlobalizationStatement.{u, uV, uQ} : Prop`.

It states that an irreducible admissible square-integrable representation `ρ` of
`GL_{r+1}(K_{v₀})`, prescribed at a finite place `v₀` of a number field `K`, occurs up to a
unitary unramified determinant twist as the local component at `v₀` of a cuspidal automorphic
representation with unitary central character. The local components of that representation at
two further prescribed finite places `v₁` and `v₂` are supercuspidal. The output is an actual
cuspidal realization with a spectral presentation whose finite local components are all
irreducible and admissible.

## Statement

Let `K : Type u` be a number field with `CompactSpace (AdeleQuotient K)`, the instance required
by the Library's `CuspidalOperatorRealization`. Let `v₀ v₁ v₂ : Langlands.Global.FinitePlace K`
be pairwise distinct and let `r : ℕ` with `0 < r`. The group is `GL_n` with `n = r + 1 ≥ 2`.

Write `K_{v₀}` for `v₀.adicCompletion K`. It carries its completion topology, the Mathlib
instance. Its valuative relation is `(CompletionPadic.topologicalData v₀).valuativeRel`, whose
order is the order of the completion valuation by `CompletionPadic.topologicalData_vle`. The
nonarchimedean local-field structure is `(CompletionPadic.topologicalData v₀).localField`. The
topology of `CompletionPadic.topologicalData v₀` is the completion topology. The matrix group
`GeneralLinear (r + 1) K_{v₀}` carries the induced matrix topology. These are the conventions used
at a finite place in `CuspidalCyclicBaseChangeLiftStatement`, and the completion topology is the
one for which `LocalRealization.IsAdmissible` is defined.

Let `V : Type uV` be a complex vector space and
`ρ : Representation ℂ (GeneralLinear (r + 1) K_{v₀}) V` with:

- `IsAdmissible ρ` and `ρ.IsIrreducible`;
- `JacquetLanglands.IsSquareIntegrable ρ`, with the topology and local-field structure above.
  For every Borel Haar measure on `GL_{r+1}(K_{v₀}) / Z`, the representation is admissible, has
  a unitary central character and has square-integrable absolute matrix coefficients on the
  central quotient. Admissibility is therefore also implied by this hypothesis.

Then there exist `S : CuspidalOperatorRealization K r` and
`D : CuspidalSpectralPresentation.{u, uQ} S` such that:

1. `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S`: the central
   character of `S` is a continuous idele class character of absolute value one;
2. for every finite place `v`, `(D.localComponent v).IsIrreducible` and
   `(D.localComponent v).IsAdmissible`. This is the predicate `HasIrreducibleAdmissibleComponents D`
   of `Langlands.Global.CuspidalPairFunctionalEquation`, written out;
3. `(D.localComponent v₁).IsSupercuspidal` and `(D.localComponent v₂).IsSupercuspidal`: these
   components are irreducible and admissible, and their canonical `p`-adic classes are
   supercuspidal in the Jacquet-vanishing sense of `Correspondence.IsSupercuspidalClass`;
4. there is a homomorphism `χ : K_{v₀}ˣ →* ℂˣ` with `χ t = 1` whenever
   `Valued.v (t : K_{v₀}) = 1` and with `‖(χ t : ℂ)‖ = 1` for all `t`. The twist
   `Langlands.twist (χ.comp GeneralLinear.determinant) ρ` is equivalent, as a representation,
   to the local action `(D.localComponent v₀).representation`. That local action is a
   representation of `FiniteLocalGL K (r + 1) v₀`, which is the same matrix group
   `GL_{r+1}(K_{v₀})`.

The first condition on `χ` says that `χ` is trivial on the units of the completed valuation
ring, so `χ` is unramified. Such a character is continuous, since that unit group is open.
The second condition makes `χ` unitary.

The supercuspidal classes at `v₁` and `v₂` are not prescribed. Nothing is asserted at the other
finite places, which may be ramified, or at the archimedean places. The universes of the number
field (`u`), of the prescribed carrier (`uV`) and of the local factors of the presentation
(`uQ`) are independent.

Conditions 1–3 are the hypotheses on `S` and `D` in
`Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement`, with the presentation universe
`uQ` in the place of that statement's `uV`. Its splitting conditions on the places and the
cyclic extension are not part of this proposition.

## The unramified twist

The Library's simple trace formula, `GeneralLinearSimpleTraceFormulaStatement`, is stated on
`L²` of the quotient `[G]` of `GL_n(𝔸_K)` by `GL_n(K)` and the positive real points `A⁺` of the
centre, for compactly supported test functions on `GL_n(𝔸_K)`. In this setting an unramified twist
cannot be avoided, for two reasons.

- The central character of an irreducible summand is a unitary idele class character trivial on
  `A⁺`. Its value at a uniformizer of `K_{v₀}` is constrained by its components at the other
  places. For `K = ℚ`, such a character factors through `𝔸_ℚ^× / ℚ^× ℝ_{>0} ≅ Ẑ^×`. It
  therefore has finite order, and its value at the idele equal to `p` at `v₀ = p` and to `1`
  elsewhere is a root of unity. The page of `GeneralLinearSupercuspidalGlobalizationStatement`
  works out this constraint. The central character of `ρ ⊗ |det|^{it}` takes the value
  `ω_ρ(p) p^{-(r+1)it}` at `p`. For all real `t` outside a countable set this is not a root of
  unity, and then `ρ ⊗ |det|^{it}` is not the component at `v₀` of any summand.
- A compactly supported local test cannot separate unramified twists. For `|a| = 1` let
  `η_a(t) = a^{ord t}`. For a compactly supported `f`, `a ↦ tr (ρ ⊗ (η_a ∘ det))(f)` is a
  Laurent polynomial in `a`, because `ord ∘ det` takes finitely many values on the support of
  `f`. If its value at `a = 1` is `1`, it vanishes at only finitely many `a`.

The proof sketched below uses local tests supported on `{g : |det g| = 1}`. Their traces do not
change under unramified twists, and they recover `ρ` up to such a twist. If
`π_{v₀} ≅ ρ ⊗ (η ∘ det)` with `η` unramified and both central characters unitary, then
`|η(ϖ)|^{r+1} = 1` for a uniformizer `ϖ`, so `η` is unitary. The proposition does not require
`χ = 1`.

## Intended proof

This is a route sketch with named prerequisites. It follows Arthur–Clozel, Chapter 1, Lemma 6.5,
and Henniart–Lemaire II.6.7–II.6.9, with one change. Those sources take the trace on cusp forms
with a fixed central character (Arthur–Clozel Lemma 2.4, condition (1); the space `L⁰_ω` of
Henniart–Lemaire II.6.9). The Library's simple trace formula is the trace on the full space
`L²([G])`. Its cuspidal summands carry all the central characters trivial on `K^×` and `A⁺`. The
local tests at `v₀`, `v₁`, `v₂` are therefore restricted to the subgroup where the determinant
is a unit. The trace then selects the local components up to unramified twists.

Notation. For a finite place `v`, write `n = r + 1`, `G_v = GL_n(K_v)`, `Z_v ≅ K_vˣ` for its
centre, `𝒪_vˣ` for the units and
`G_v¹ = {g ∈ G_v : |det g|_v = 1}`. The subgroup `G_v¹` is open and normal. It contains every
compact subgroup, and every unramified character `η ∘ det` is trivial on it. Also
`Z_v ∩ G_v¹ = 𝒪_vˣ` (unit scalars), and `Z_v G_v¹ = {g : ord det g ∈ nℤ}` has index `n`. For
`ζⁿ = 1` let `η_ζ(t) = ζ^{ord t}`. Then `∑_ζ η_ζ(det g) = n · 1_{Z_v G_v¹}(g)`.

1. **Truncation identity.** Let `ω` be a unitary character of `Z_v`. Let `h` be a smooth
   function on `G_v`, compactly supported modulo `Z_v`, with `h(zg) = ω(z)⁻¹ h(g)`. Put
   `h¹ = 1_{G_v¹} · h`. Its support lies in `G_v¹ ∩ C Z_v` for a compact `C`, and this set is
   compact because the determinant bounds the central factor. So `h¹` is smooth and compactly
   supported on `G_v`. Let `π` be an admissible representation with central character `ω_π`.
   Write `π(h¹) = ∫_{G_v} h¹(g) π(g) dg`, and `π(h) = ∫_{G_v/Z_v} h(g) π(g) dġ` when `ω_π = ω`.
   - (T1) `π(h¹) = (π ⊗ (η ∘ det))(h¹)` for every unramified `η`.
   - (T2) `π(h¹) = 0` unless `ω_π = ω` on `𝒪_vˣ`. Indeed, for a unit scalar `u`,
     `h¹(ug) = ω(u)⁻¹ h¹(g)`, so `π(h¹) = ω(u)⁻¹ ω_π(u) π(h¹)`.
   - (T3) If `ω_π = ω`, then `π(h¹) = (c/n) ∑_{ζⁿ=1} (π ⊗ (η_ζ ∘ det))(h)`, where `c > 0` is
     the volume of `𝒪_vˣ` for the measures used. To see this, integrate the `Z_v`-invariant
     function `h(g) π(g)` over `G_v¹`. The group `G_v¹` maps onto `Z_v G_v¹ / Z_v` with fibres
     `𝒪_vˣ`. Then expand `1_{Z_v G_v¹}` in the characters `η_ζ ∘ det`. The twists
     `π ⊗ (η_ζ ∘ det)` have central character `ω`.

   Suppose `ω_π = ω` on `𝒪_vˣ`. An unramified `η` with `η(ϖ)ⁿ = ω(ϖ) ω_π(ϖ)⁻¹` gives
   `ω_{π ⊗ η} = ω`. Then (T1) and (T3) express `π(h¹)` through the operators at `h` of the
   twists `π ⊗ (η η_ζ ∘ det)`. If `ω` and `ω_π` are unitary, so is `η`.
2. **Local tests at `v₀`, `v₁`, `v₂`.**
   - At `v₀`, let `ω_ρ` be the central character of `ρ`. The Library states, without proof, the
     existence of an elliptic pseudo-coefficient as
     `Langlands.BaseChange.CuspidalPseudoCoefficientExistenceStatement` (Kazhdan's Theorem K,
     cited in the proof of Arthur–Clozel Lemma 6.5). It gives a compactly supported `f₀` with
     clauses (a)–(d). By (a), `tr π'(f₀)` is `1` at `ρ` and `0` at every other irreducible
     tempered `π'` with central character `ω_ρ`. By (b), the characters of properly induced
     representations vanish at `f₀`. By (c), the regular non-elliptic orbital integrals of `f₀`
     vanish. Put `h₀(g) = ∫_{Z_{v₀}} f₀(zg) ω_ρ(z) dz` and `φ₀ = h₀¹`. Then `π'(h₀) = π'(f₀)`
     for every `π'` with central character `ω_ρ`.

     Let `π` be irreducible and admissible, either tempered or properly induced, with
     `tr π(φ₀) ≠ 0`. By (T2), `ω_π = ω_ρ` on `𝒪_{v₀}ˣ`. With `η` as in step 1, some twist
     `π ⊗ (η η_ζ ∘ det)`, of central character `ω_ρ`, has nonzero trace at `f₀`. Twists of a
     properly induced representation are properly induced, so (b) rules out the induced case.
     Hence `π` is tempered, `η` is unitary, and the twists are tempered. By (a), some twist is
     isomorphic to `ρ`. So `π ≅ ρ ⊗ (η' ∘ det)` with `η'` unramified and unitary. By (T3),
     `tr ρ(φ₀) = (c/n) · #{ζ : ρ ⊗ (η_ζ ∘ det) ≅ ρ}`, which is nonzero.
   - At `v_i` (`i = 1, 2`), fix an irreducible supercuspidal representation `σ_i` with unitary
     central character `ω_i`. For example, take a depth-zero representation compactly induced
     from an open subgroup that is compact modulo the centre, and twist it by an unramified
     character to make its central character unitary. Then `σ_i` is unitarizable. Fix an
     invariant inner product, linear in the first variable, and a unit vector `w_i`. Put
     `h_i(g) = \overline{⟨σ_i(g) w_i, w_i⟩}` and `ψ_i = h_i¹`. Then `h_i(zg) = ω_i(z)⁻¹ h_i(g)`,
     and `h_i` has compact support modulo the centre. Let `π'` be irreducible admissible with
     central character `ω_i`, and let `e` be a vector of `π'`. Then
     `x ↦ ∫_{G/Z} ⟨x, σ_i(g) w_i⟩ π'(g) e dġ` is a `G_{v_i}`-map from `σ_i` to `π'` sending `w_i`
     to `π'(h_i) e`. So `π'(h_i) ≠ 0` forces `π' ≅ σ_i`. By step 1, every irreducible admissible
     `π` with `π(ψ_i) ≠ 0` is `σ_i ⊗ (η ∘ det)` with `η` unramified, hence supercuspidal. Schur
     orthogonality for `σ_i` is the Library theorem
     `Langlands.Renard.CompactRepresentation.schurOrthogonality`. From it,
     `σ_i(h_i) = d(σ_i)⁻¹ ⟨·, w_i⟩ w_i` with formal degree `d(σ_i) > 0`. So
     `tr σ_i(ψ_i) = (c/n) · #{ζ : σ_i ⊗ (η_ζ ∘ det) ≅ σ_i} · d(σ_i)⁻¹`, which is nonzero.
     Because `σ_i` is supercuspidal, `∫_N h_i(x m y) dm = 0` for the unipotent radical `N` of every
     proper parabolic subgroup and all `x, y`. Since `1_{G¹}(x m y) = 1_{G¹}(x y)`, `ψ_i` has the
     same property.
   - The regular non-elliptic orbital integrals of `φ₀`, `ψ₁` and `ψ₂` vanish. For `φ₀` this
     follows from (c), since `O_γ(h₀¹) = 1_{G¹}(γ) ∫_Z ω_ρ(z) O_{zγ}(f₀) dz`. For `ψ_i` it
     follows from the vanishing constant terms, by descent of orbital integrals to a Levi
     subgroup. Their traces at `ρ`, `σ₁`, `σ₂` are nonzero. By the Weyl integration formula,
     with the local integrability of Harish-Chandra characters, each of them therefore has a
     nonzero orbital integral at some regular elliptic `γ_i ∈ G_{v_i}¹` (`i = 0, 1, 2`).
     Orbital integrals are locally constant on the regular set, as used in Henniart–Lemaire
     II.6.7, so they are nonzero near `γ_i`.
3. **Global test.** Choose a further finite place `v₃` and a regular elliptic point of `G_{v₃}`.
   By weak approximation there is a monic polynomial over `K` close to the characteristic
   polynomials of `γ₀`, `γ₁`, `γ₂` and of that point. Let `γ ∈ GL_n(K)` be its companion matrix.
   By Krasner's lemma, `γ` is regular elliptic at `v₀, …, v₃`. At `v_i` it is conjugate to an
   element near `γ_i`, so `O_γ(φ₀)`, `O_γ(ψ₁)` and `O_γ(ψ₂)` are nonzero, and `det γ` is a unit
   at `v₀`, `v₁`, `v₂`. Take `f = f₁ * f₂` with factorizable smooth compactly supported `f₁` and
   `f₂` on `GL_n(𝔸_K)`:
   - `f₂` has components `φ₀`, `ψ₁`, `ψ₂` at `v₀`, `v₁`, `v₂`. At `v₃` its component is a
     nonnegative function, supported in a small compact neighbourhood of `γ` inside the regular
     elliptic set and positive at `γ`. At almost all other places it is the unit-group
     indicator. At the remaining places, including the archimedean ones, it is nonnegative and
     positive at `γ`.
   - At each finite place, `f₁` is the normalized indicator of an open compact subgroup. At
     `v₀`, `v₁`, `v₂` that subgroup leaves `f₂` left invariant, so `f_v = f₂,v` there. At the
     archimedean places, `f₁` is a nonnegative bump near `1`.

   Then every local factor of `f` away from `v₀`, `v₁`, `v₂` is nonnegative and positive at
   `γ`. Because of its factor at `v₁`, `f₂` integrates to zero along every two-sided translate
   of the adelic unipotent radical of every proper rational parabolic. Every point of the
   support of `f` is regular elliptic at `v₃`. The remaining hypotheses of
   `GeneralLinearSimpleTraceFormulaStatement` are that `f₁` and `f₂` have Hilbert–Schmidt
   cuspidal operators. The Library page of `GroupSchemeFullAEL2CuspidalTraceClassStatement`
   records that Getz–Hahn prove this for smooth compactly supported functions on
   `A_G \ G(𝔸)` (Theorem 9.1.2 and its proof). The operator of `f_i` on `L²([G])` is that of
   its `A⁺`-average. The proof has to supply this property for these tests.
4. **Geometric side.** Only finitely many rational conjugacy classes meet the support of the
   `A⁺`-average `f¹` of `f`. A rational regular elliptic class is determined by its
   characteristic polynomial. Shrinking the support at `v₃` therefore leaves only the class of
   `γ`, as in Henniart–Lemaire II.6.9. The Library theorem
   `Langlands.TraceFormula.generalLinearSingleOrbitTrace` proves
   `GeneralLinearSingleOrbitTraceStatement`, which takes
   `GeneralLinearSimpleTraceFormulaStatement` as a premise. It gives `tr R(f)` on `L²([G])` as a
   centralizer volume times the orbital integral of `f¹` at `γ`. That orbital integral is the
   product of the finite local orbital integrals at `γ` with the `A⁺`-average of the
   archimedean orbital integrals at the points `aγ`. All these factors are nonzero, so
   `tr R(f) ≠ 0`.
5. **Spectral side.** `R(f) = R(f₁) R(f₂)`, and `R(f₂)` maps `L²([G])` into the cuspidal
   subspace because `f₂` integrates to zero along the unipotent radicals (as in Arthur–Clozel
   Lemma 2.4). So `tr R(f)` is the trace of the restriction of `R(f)` to the cuspidal subspace.
   That subspace is a Hilbert sum of irreducible closed invariant subspaces with finite
   multiplicities. This is the Library theorem
   `Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2CuspidalDecomposition`,
   whose premise is the compactness of the cuspidal operators of compactly supported
   continuous functions. That premise follows from the Hilbert–Schmidt property for smooth
   functions and approximation in `L¹`. Hence some irreducible summand `P` has
   `tr(R(f)|_P) ≠ 0`.
6. **Realization and local components.**
   `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalSummandRealizationStatement`
   gives a cuspidal operator realization `S` whose image is dense in `P`. The centre acts on the
   irreducible unitary `P` by a unitary idele class character, so `S` has unitary central
   character. A spectral presentation `D` of `S` with irreducible admissible finite components
   comes from `Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement`
   and Flath's tensor product theorem. The Library's
   `Langlands.TraceFormula.GeneralLinearCuspidalLocalComponentTraceStatement` says that the
   trace on `P` of a test `f_v ⊗ f^v` is the trace of `f_v` at `D.localComponent v` times a
   factor depending only on `f^v`. So the traces of `D.localComponent v_i` at the tests of
   step 2 are nonzero. At `v₁` and `v₂`, step 2 makes these components unramified twists of
   `σ₁` and `σ₂`, hence supercuspidal. At `v₀` the component is generic and unitary, by the
   Library theorems `Langlands.Automorphic.cuspidalUnitaryLocalGenericity` and
   `Langlands.Automorphic.cuspidalUnitaryLocalUnitarity`. It is therefore either properly
   parabolically induced or square-integrable, as in Henniart–Lemaire II.6.9, and so tempered
   or properly induced. Step 2 then gives `ρ ⊗ (χ ∘ det) ≅ D.localComponent v₀` with `χ`
   unramified and unitary. This is condition 4.

The route uses the ordinary simple trace formula and local harmonic analysis on `GL_{r+1}` over
a single local field. The local inputs are pseudo-coefficients, supercuspidal coefficients,
orbital integrals, the Weyl integration formula and local genericity. It uses no global
character extension, no cyclic extension and no local pair-factor base change. It also uses no
σ-lift existence, structure or converse, no automorphic induction and no full local Langlands
correspondence.

## Sources

- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
  Trace Formula*, Annals of Mathematics Studies 120 (1989). Retained source
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  - Chapter 1, Lemma 6.5 and its proof, printed pp. 54–55 (PDF pp. 68–69). The lemma starts
    from a discrete series `π₀` of trivial central character at `v₀`. It gives a cuspidal `π`
    with `π_{v₀} ≅ π₀`, a given supercuspidal component at `v₁` and a Steinberg component at
    `v₃`, unramified outside `{v₀, v₁, v₂, v₃}`. The proof takes compactly supported
    pseudo-coefficients at `v₀` and `v₃` (Kazhdan, *Cuspidal geometry of p-adic groups*,
    Theorem K), a coefficient of the supercuspidal at `v₁`, and the elliptic test of
    Lemma 2.4 at `v₂`. These are used inside the trace formula of Lemma 2.4. The single
    surviving orbit is arranged with that test and the archimedean tests. Genericity of
    cuspidal components (Shalika, *The multiplicity one theorem for GL(n)*) gives the
    component at `v₀`.
  - Chapter 1, §2.2 and Lemma 2.4 (Deligne–Kazhdan), printed pp. 12–13 (PDF pp. 26–27). A
    unitary character `χ` of a central subgroup `Z₁ ⊂ Z(𝔸)` is fixed, trivial on `Z₁ ∩ F^×`. The
    test `f` satisfies four conditions. (1) `f(zg) = χ(z)⁻¹ f(g)` for `z ∈ Z₁`. (2) `f` is a
    tensor product of local functions. At almost all places the local function is `χ(z)⁻¹` at
    `zk`, for `z` in the local part of `Z₁` and `k ∈ G(𝒪_v)`, and zero elsewhere. (3) `f_{v₁}`
    is a coefficient of a supercuspidal representation. (4) `f_{v₂}` is supported on the regular
    elliptic elements of `G(F_{v₂})` whose image in `PGL(n, F_{v₂})` is regular. Then `r(f)`
    maps `L²` automorphic forms into cusp forms. The trace of `r_cusp(f)` on
    `L²(G(F) Z₁ \ G(𝔸), χ)` is a sum over regular elliptic rational classes of volumes times
    orbital integrals. The route above uses instead the Library's full-space formula on `L²([G])`. Its hypotheses are
    cuspidality of the factor `f₂` and regular elliptic support at one finite place. They
    contain no central-character condition and no regularity condition in `PGL_n`.
- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011). Retained source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`, II.6.7–II.6.9, printed pp.
  123–125 (PDF pp. 131–133). In II.6.7 the fixed central-character datum `ω` is changed so that
  the central character of the prescribed discrete series extends the component `ω_{v₀}` of that
  datum. A pseudo-coefficient is used at `v₀`. At a split place `v₁`, the test is a level-zero
  combination of supercuspidal coefficients with elliptic support. The orbital integrals of
  these tests are locally constant on the regular set. In II.6.8, elliptic tests at the further
  places of a finite set `S` are chosen. In II.6.9 the support is shrunk until one rational
  orbit contributes. The trace on the cuspidal space `L⁰_ω` with that character is then nonzero.
  It gives a cuspidal `π'` in `L⁰_ω` with `tr π'_v(f_v) ≠ 0` at every place. Its component at
  `v₁` is one of two depth-zero supercuspidals. Its component at `v₀` is generic and unitary,
  hence properly induced or a discrete series. The pseudo-coefficient kills properly induced
  representations, so that component is isomorphic to the prescribed discrete series. The source
  works over global function fields; here the method is transferred to number fields. The fixed
  space `L⁰_ω` is replaced by the full positive-central space with truncated local tests, which
  produces the unitary unramified twist of condition 4.

The proposition is derived from these sources. Lemma 6.5 prescribes one supercuspidal class and
a Steinberg component. Here supercuspidal components are required at two places, without
prescribed classes, and no Steinberg place is used. The distinguished hypothesis allows any
square-integrable `ρ`, with no condition on its central character. The output has no
ramification condition away from `v₀`, `v₁`, `v₂`, which leaves the isolating place free.

## Related statements

`Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationStatement` prescribes
supercuspidal representations at a finite set of places, up to unramified twists. Its output is
an irreducible closed invariant subspace of the cuspidal `L²` space, unramified away from the
prescribed set and one auxiliary place. The present proposition prescribes a square-integrable
representation at one place and only requires supercuspidal components at two others. Its
output is a cuspidal operator realization with a spectral presentation. Neither proposition
contains the other.
