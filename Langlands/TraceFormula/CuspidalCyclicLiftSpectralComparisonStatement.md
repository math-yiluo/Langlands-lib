# The spectral comparison for the cuspidal cyclic lift (statement)

Module `Langlands.TraceFormula.CuspidalCyclicLiftSpectralComparisonStatement`, namespace
`Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.CuspidalCyclicLiftSpectralComparisonStatement.{u, uV, uW}`.

In words: let `L/K` be a cyclic extension of number fields of degree `l` with generator `σ`,
in which every infinite place of `K` splits with cyclic shift action. Let `S` be a cuspidal
automorphic representation of `GL_{r+1}(𝔸_K)` with unitary central character, given with a
spectral presentation `D` whose finite local components `π_v` are irreducible and admissible,
and supercuspidal at two distinct finite places `v₁`, `v₂` that split with cyclic shift
action. Then there is a list of **at most one** cuspidal automorphic representation `T` of
`GL_{r+1}(𝔸_L)`, with a spectral presentation `P`, having the global properties of the base
change of `S` (unitary central character, arithmetic weak base change, residue-degree Satake
parameters, irreducible admissible local components), and satisfying, with constants `b`
(one for each member of the list) and `a ≠ 0`:

- at a finite place `v` that splits with cyclic shift action and every `w | v`:
  `Σ_j b_j · tr Π_{j,w}(f) = a · tr π_v(f)` for every Schwartz–Bruhat `f` on `GL_{r+1}(K_v)`,
  where `Π_{j,w}` is the component of `P j` at `w`, pulled back to `GL_{r+1}(K_v)` along
  `K_v ≅ L_w`;
- at a finite place `v` with a single place `w` above it:
  `Σ_j b_j · tr (Π_{j,w}(φ) ∘ A_j) = a · tr π_v(f)` for all concordant pairs `(φ, f)` with
  `φ` supported in the `σ`-regular set, `f` in the regular semisimple set, and `det g` a norm
  from `(K_v ⊗_K L)^×` wherever `f g ≠ 0`.

This is what the comparison of the simple trace formula for `GL_{r+1}` over `K` with its
twisted form for `Res_{L/K} GL_{r+1}` gives at one place, after separation by the spherical
Hecke algebras, after the collapse of the cuspidal fibre of `S` (Arthur–Clozel III.3.1: the
cuspidal representations with the same base change as `S` are the twists of `S` by idele class
characters trivial on the norms, and these have the traces of `S` on the test functions used)
and after strong multiplicity one over `L`. At the two auxiliary places `v₁`, `v₂`, where the
simple trace formula only admits restricted test functions, the derivation identifies the
components first and reads the identity off the isomorphism (see "From the trace formula"
below). The statement leaves out the local end of the argument: that the list is not empty,
that the identities at split places give isomorphisms, and that `b_j ≠ 0` at the places with
one place above. The module
`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeReductionStatement` states
that this statement and the local nonvanishing statement
`Langlands.BaseChange.RegularNormTraceNonvanishingStatement` imply the Library's
`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`.

The module declares five `local instance`s of `AddCommGroup`: on the Library's form spaces
`Langlands.Automorphic.RationalInvariantFunctions`, `ContinuousRationalFunctions`,
`FiniteSmoothRationalFunctions` and `AutomorphicForms`, and on the carrier `A.Space` of a
`LocalRealization`. They are `Submodule.addCommGroup _`, as in the Library's
`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`. They are not exported.

## Setting and notation

The hypotheses are those of the Library's
`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`, binder for binder
and in the same order, and the local objects at the places `v` are the same; its Markdown page
describes each of them. In short:

- `K L : Type u` are number fields with `[Algebra K L]` and compact adele quotients;
  `σ : L ≃ₐ[K] L` and `l : ℕ` with `IsCyclicAlgebra σ l`;
  `IsCyclicShiftSplit K L x.Completion σ l` at every infinite place `x` of `K`.
- `S : CuspidalOperatorRealization K r` and `D : CuspidalSpectralPresentation.{u, uV} S`, with
  `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S` and
  `(D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible` at every finite `v`.
- `v₁ ≠ v₂` finite places of `K` with `IsCyclicShiftSplit K L (vᵢ.adicCompletion K) σ l` and
  `(D.localComponent vᵢ).IsSupercuspidal`.
- For a finite place `v` of `K`, `K_v := v.adicCompletion K` with the local field data of
  `CompletionPadic.topologicalData v`, and `π_v := (D.localComponent v).representation`.
  For `w : FinitePlacesAbove L v`, `completionPlaceAboveRepresentation v w ρ` pulls a
  representation `ρ` of `GL_{r+1}(L_w)` back to `GL_{r+1}(K_v)` along the completion map
  `K_v → L_w`, and `tensorPlaceAboveRepresentation v w ρ` pulls it back to
  `GL_{r+1}(K_v ⊗[K] L)` along the `w`-component of `finiteTensorMap v` (both defined in
  `Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftStatement`).
- `Character.distribution μ ρ hρ f` (module `Langlands.Representation.Character.Basic`) is the
  trace of `ρ(f) = ∫ f(g) ρ(g) dμ(g)`; `twistedDistribution μE ρ hρ A φ` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`) is the trace of `ρ(φ) ∘ A`.
- `AreConcordant`, `IsSigmaRegularSupported`, `IsRegularSupported` (module
  `Langlands.BaseChange.OrbitalIntegral`): matching of orbital integrals in the sense of
  Henniart–Lemaire I.2.5 (printed p. 17), and support in the `σ`-regular, respectively regular
  semisimple, set. `(Units.map (Algebra.norm K_v)).range` is the norm subgroup of `K_v^×`.
- `∑ j, …` is the finite sum over `j : Fin k`.

## Statement

Under these hypotheses there are `k : ℕ` with `k ≤ 1`,
`T : Fin k → CuspidalOperatorRealization L r` and
`P : ∀ j, CuspidalSpectralPresentation.{u, uW} (T j)` such that:

1. **Global properties.** For every `j`: `T j` has unitary central character;
   `(P j).spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem`; for every finite `v`
   with `hv : v ∉ D.spectralSystem.exceptional` at which every `w | v` has ramification index
   `1`, every such `w` is outside `(P j).spectralSystem.exceptional` and the Satake parameters of
   `P j` at `w` are those of `D` at `v` raised to the residue degree of `w`; and every finite
   local component of `P j` is irreducible and admissible. These are clauses 1, 2, 3 and 6 of
   `CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement` for `(T j, P j)`, verbatim.
2. **Split places.** For every finite `v` with `IsCyclicShiftSplit K L (v.adicCompletion K) σ l`
   and every `w : FinitePlacesAbove L v`, with the Borel σ-algebra on `GL_{r+1}(K_v)`, there
   are `hπ : Langlands.IsAdmissible π_v` and admissibility proofs `hT j` of
   `Π_{j,w} := completionPlaceAboveRepresentation v w ((P j).localComponent w.1).representation`,
   each `Π_{j,w}` is irreducible, and there are `b : Fin k → ℂ` and `a : ℂ` with `a ≠ 0` such
   that for every Haar measure `μ` on `GL_{r+1}(K_v)` and every
   `f : SchwartzBruhat (GL_{r+1}(K_v))`
   `∑ j, b j * Character.distribution μ Π_{j,w} (hT j) f = a * Character.distribution μ π_v hπ f`.
3. **Places with one place above.** For every finite `v` and `w : FinitePlacesAbove L v` with
   `∀ w', w' = w`: give `E_v := K_v ⊗[K] L` its module topology over `K_v`, put
   `σv := Algebra.TensorProduct.congr AlgEquiv.refl σ` and
   `Π_{j,w} := tensorPlaceAboveRepresentation v w ((P j).localComponent w.1).representation`.
   There are `hπ : Langlands.IsAdmissible π_v`, admissibility proofs `hP j` of `Π_{j,w}`,
   `A : ∀ j, SigmaIntertwiner σv (r + 1) Π_{j,w}`, `b : Fin k → ℂ` and `a : ℂ` with `a ≠ 0`
   such that, with the Borel σ-algebras, for all Haar measures `μF` on `GL_{r+1}(K_v)` and `μE`
   on `GL_{r+1}(E_v)` and all `φ : SchwartzBruhat (GL_{r+1}(E_v))` and
   `f : SchwartzBruhat (GL_{r+1}(K_v))` with
   - `AreConcordant σv l μF μE φ f`,
   - `IsSigmaRegularSupported σv l φ`,
   - `IsRegularSupported f`,
   - `GeneralLinear.determinant g ∈ (Units.map (Algebra.norm K_v)).range` whenever `f g ≠ 0`,

   we have
   `∑ j, b j * twistedDistribution μE Π_{j,w} (hP j) (A j).toLinearMap φ =
     a * Character.distribution μF π_v hπ f`.

The constants `b` and `a` of clauses 2 and 3 depend on the place (and on `w`), and come before
the Haar measures.

## Remarks on the form

- **At most one lift, possibly none.** The bound `k ≤ 1` records strong multiplicity one over
  `L`: the cuspidal `σ`-stable representations of `GL_{r+1}(𝔸_L)` whose Satake parameters are,
  at almost all places, the residue-degree powers of those of `S` form at most one isomorphism
  class. The form allows `k = 0`. With `k = 0`, however, clause 2 at `v₁` says
  `a · tr π_{v₁}(f) = 0` for every `f`, with `a ≠ 0`, while the character of the irreducible
  admissible `π_{v₁}` is not zero; so `k = 0` is impossible under the hypotheses, and this
  statement asserts the existence of the lift through its trace identities.
- **The fibre is collapsed.** The right sides contain only `π_v`, the component of the given
  `S`. The sum over the cuspidal fibre of `S` (the cuspidal representations with the same base
  change) that the trace comparison produces has been replaced by a multiple of the trace of
  `π_v`; that step is part of this statement.
- **The coefficients `b j` may vanish; `a` does not.** In the trace comparison, `b j` is a
  product of local twisted traces of `Π` at the other places of a finite set of places, and
  `a` a product of local traces of `S` there, times the number of distinct twists in the fibre
  divided by `l`. The local data at the other places can be chosen so that `a ≠ 0`; no choice
  is asserted to make `b j ≠ 0`. That `b j ≠ 0` at a place with one place above follows from
  the identity of clause 3 and a regular pair with nonzero trace (the reduction module), and at
  a split place from `a ≠ 0` and the nonvanishing of the character of `π_v`.
- **Ordinary traces at split places.** The cyclic convolution gives both the ordinary matching
  function and the test against which the ordinary trace equals the twisted tensor trace.
  In the trace formula this convolution uses quotient measures and acts on centrally equivariant
  factors. Central averaging converts their quotient traces into the full-group characters of
  clause 2 (steps 1–3 below). At `v₁` and `v₂` the isomorphism `Π_w ≅ π_v` gives the identity
  on all tests (step 6).
- **Homogeneity in the measures.** Both sides of clause 2 scale by the same factor when `μ` is
  scaled. For clause 3, let `μF = s μF₀` and `μE = t μE₀` for positive `s` and `t`. With the
  centralizer measures fixed, the two orbital integrals scale by `s` and `t`. Thus if `(φ, f)`
  is concordant for the new pair, `(φ, (s/t)f)` is concordant for `(μF₀, μE₀)` with the same
  support conditions. Apply the identity for `(μF₀, μE₀)` to this pair and multiply by `t`.
  The operators scale with their measures, so the identity holds for `(μF, μE)` with the
  same coefficients, as in `IsRegularSigmaLift` (module
  `Langlands.BaseChange.SigmaDiscreteRegularDescentStatement`).
- **Universes.** `K` and `L` are in `Type u`, the presentation `D` in universe `uV` and the
  presentations `P j` in universe `uW`, as in the target statement.

## Why the statement is true

### From the cuspidal cyclic lift

The Library's `CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement.{u, uV, uW}` implies this
statement. Let `T`, `P` be as there and take `k = 1`, `T 0 = T`, `P 0 = P`. Clause 1 is clauses
1, 2, 3 and 6 of the lift. At a split place clause 4 of the lift gives an isomorphism
`Π_w ≅ π_v`; so `Π_w` is admissible and irreducible, its character is that of `π_v`, and
clause 2 holds with `b 0 = 1` and `a = 1`. At a place with one place above, clause 5 of the lift
gives `hπ`, `hP`, `A` and `c` with `IsRegularSigmaLift σv l π_v hπ Π_w hP A c`, that is `c ≠ 0`
and `tr (Π_w(φ) ∘ A) = c · tr π_v(f)` on the pairs of clause 3; take `b 0 = 1` and `a = c`.

### From the trace formula

For `r ≥ 1`, the argument uses the number-field trace formulas of Arthur–Clozel 1989,
Chapter 1, Lemmas 2.4–2.5 and §§4–6, and the local passage between compactly supported and
centrally equivariant tests of Henniart–Lemaire 2011, I.2.9–I.2.10 and II.2.6–II.2.8.
Write `G = GL_{r+1}` and reserve `x` for a place of `K`.

1. **Central characters and measures.** Let `ω` be the restriction of the unitary central
   character of `S` to `Z₁ := N(𝔸_L^×)` and let `η := ω ∘ N` on `𝔸_L^×`. At `x` write
   `E_x := K_x ⊗_K L`, `Z₁x := N_x(E_x^×)` and `η_x := ω_x ∘ N_x`. The ordinary and twisted
   trace formulas use decomposable functions with factors `F_x` on `G(K_x)` and `Φ_x` on
   `G(E_x)`. They are smooth and compactly supported modulo `Z₁x` and `E_x^×`, respectively,
   with `F_x(zg) = ω_x(z)⁻¹ F_x(g)` and `Φ_x(zg) = η_x(z)⁻¹ Φ_x(g)`. The lower spectrum
   consists of representations that restrict to `ω` on `Z₁`. The upper spectrum has
   central character `η`. The spectral operators integrate `F_x(g)π_x(g)` and
   `Φ_x(g)Π_x(g)` on the corresponding central quotients, with Haar measures
   `d̄g_x = dg_x/dz_x` and `d̄g_{E_x} = dg_{E_x}/dz_{E_x}`. At almost every finite place the
   factors are the centrally equivariant spherical units with the compact subgroups and their
   central unit subgroups of volume one. These are the central conditions of Arthur–Clozel,
   (1)–(2) and their upper analogues (printed pp. 13–14), with the quotient conventions of
   Henniart–Lemaire II.2.6–II.2.7 and II.6.2–II.6.4 (printed pp. 66–67 and 118–121).

   Arthur–Clozel (3) and (3′) require a supercuspidal coefficient at one split place, with
   coefficients of the same supercuspidal representation on all upper factors there.
   Conditions (4) and (4′) require a lower test supported on regular elliptic elements with
   regular image in `PGL_{r+1}` at a different split place, and the product of the supports
   of the upper factors there must lie in that set.

2. **Local averaging and cyclic convolution.** At a finite place with one place above it,
   `E_x` is a field. Choose Haar measure `dz_{E_x}` on `E_x^×` and take its pushforward by
   `N_x` for `dz_x` on `Z₁x`. The kernel of the norm is compact, so this gives a Haar measure
   and makes the averaging constant of Henniart–Lemaire I.2.10 equal to one. For compactly
   supported inputs `f` and `φ` put

   `F_x(g) = f^ω(g) := ∫_{Z₁x} f(zg) ω_x(z) dz_x` and
   `Φ_x(g) = φ^η(g) := ∫_{E_x^×} φ(zg) η_x(z) dz_{E_x}`.

   Scalar translation takes an associated pair `(δ, γ)` to `(zδ, N_x(z)γ)` with the same
   associated centralizer measures and ambient Haar measures. The twisted orbital integral
   of `φ^η` is the integral of `η_x(z)` times the twisted orbital integral of `φ` at `zδ`.
   For concordant inputs this becomes the integral of `ω_x(N_x z)` times the ordinary
   orbital integral of `f` at `N_x(z)γ`, which is the ordinary orbital integral of `f^ω`
   by the choice of `dz_x`. At a regular nonnorm, every translate by `Z₁x` is again a
   nonnorm, so the averaged ordinary orbital integral also vanishes there. Scalar saturation
   preserves regular and σ-regular support, and multiplication by `z ∈ Z₁x` multiplies the
   lower determinants by `z^{r+1} ∈ Z₁x`. These are the matching and support arguments of
   Henniart–Lemaire I.2.10 and II.2.6 (printed pp. 22–23 and 66). Quotient integration then
   gives the operator identities of II.2.7 (printed p. 67). The quotient operators at `f^ω`
   and `φ^η` equal the full-group operators at `f` and `φ` for `dg_x` and `dg_{E_x}`.
   The latter equality also gives equality of traces after composition with a
   local σ-intertwiner.

   At a place where `E_x` has `m` field factors, identify them with `E_{x,1}` so that
   `σ` sends `(g₁, …, gₘ)` to `(g₂, …, gₘ, τ(g₁))`, where `τ` is induced by `σ^m`.
   Use the product measure on the upper central quotient. The central character on
   each factor is `ω_x ∘ N_{E_{x,1}/K_x}`. For `Φ_x = Φ₁ ⊗ ⋯ ⊗ Φₘ`, the matching condition
   at `x` is that `Φ₁ ∗ ⋯ ∗ Φₘ` matches `F_x` for the field norm and twist `τ`. Here `∗`
   is convolution using the Haar measure on `E_{x,1}^× \ G(E_{x,1})`. The reduction of the
   twisted orbital integrals uses the compatible measures on the centralizers and
   concentrates the product on the class of `δ₁ ⋯ δₘ` in the first factor
   (Arthur–Clozel I §5, printed pp. 48–50, and Henniart–Lemaire I.2.9, printed p. 22).
   The same convolution computes the twisted tensor trace on a σ-stable component, using
   the local intertwiner on the first factor (Henniart–Lemaire II.2.8, printed pp. 67–68).
   This permits averaging on the field factor with compact norm kernel and then applying
   cyclic convolution. At a completely split place the field factor is `K_x` and `τ` is
   the identity. Take the same measures `dg_x`, `dz_x` on every factor, so the match is
   the ordinary quotient convolution and the twisted tensor trace is the ordinary trace on
   this convolution, up to the scalar in the choice of the shift intertwiner.

3. **Choice of concordant tests.** Fix a finite set `Σ` containing the place `v` under
   study, `v₁`, `v₂`, the infinite places, the places ramified in `L`, and the exceptional
   places of `D` and of the central character. At finite split `v ∉ {v₁, v₂}`, start with
   any Schwartz–Bruhat `f` and set `F_v = f^ω`. For a small compact open subgroup `J` for
   which `f` is right invariant, let `e_J = 1_J / vol_{dg_v}(J)` and `Q_J = (e_J)^ω`.
   This is the idempotent for quotient convolution supported on `K_v^× J` (shrink `J` so
   that `ω_v` is trivial on `K_v^× ∩ J`). Quotient integration identifies the operator at
   `Q_J` with convolution averaging over `J`, so `F_v ∗ Q_J = F_v`. Take
   `Φ_v = F_v ⊗ Q_J ⊗ ⋯ ⊗ Q_J`. If there is one place above `v`, use the pair
   `(φ^η, f^ω)` from step 2 for any pair `(φ, f)` of clause 3.

   At `v₁`, choose a smooth unit vector `e` and let `ξ(g) = ⟨π_{v₁}(g⁻¹)e, e⟩`, with the
   inner product linear in the first variable. This coefficient of the contragredient
   transforms by `ω_{v₁}⁻¹` under the center and has compact support modulo it.
   Schur orthogonality for the quotient Haar measure gives
   `ξ ∗ ξ = d⁻¹ ξ` for the formal degree `d > 0` and the trace of `π_{v₁}(ξ)` is `d⁻¹`.
   Thus `Φ_{v₁} = ξ ⊗ ⋯ ⊗ ξ` matches `F_{v₁} = d^{1-l} ξ` and the lower trace is
   `d^{-l}`.
   At `v₂`, use nonvanishing of the supercuspidal character on the regular elliptic set
   (Arthur–Clozel, printed p. 55, following Kazhdan's Theorem K). The elements with regular
   image in `PGL_{r+1}` are open and dense there, so local constancy gives a compact open
   neighbourhood of such an element on which the character is constant and nonzero.
   Let `q` be the central average of the characteristic function of this neighbourhood.
   Its central saturation satisfies (4), and its quotient trace equals the original
   nonzero full-group trace. Choose `J` small enough to preserve this neighbourhood by
   right multiplication. Then `q ⊗ Q_J ⊗ ⋯ ⊗ Q_J` matches `q`, and the product of the
   supports lies in the same central saturation, giving (4′).

   For the other finite places in `Σ`, use a regularly supported lower test inside the
   norms, of nonzero trace as in `RegularNormTraceNonvanishingStatement`. Transfer it for
   the single field factor by regular transfer. Average the pair as in step 2. When there
   are several upper factors, use the averaged upper function followed by small-subgroup
   idempotents in the other factors so that its cyclic convolution is that function.
   At infinite places use the split convolution (Arthur–Clozel I §5, printed p. 48).
   Choose a smooth compactly supported test modulo the center whose operator on the
   unitary component `π_x` is nonzero. Convolving it with its adjoint gives a test `q`
   whose operator is positive and nonzero. The pair `q ⊗ ⋯ ⊗ q`, `q^{∗l}` gives a positive,
   nonzero lower trace. Outside `Σ`, use upper spherical functions and their lower
   transfers, equal to the spherical units at almost all places (Arthur–Clozel I §§4–5,
   printed pp. 42–44 and 48–50).

4. **Separation and the fibre.** The comparison of the geometric sides with compatible
   measures gives the trace identity with the degree `l` multiplying the twisted side,
   as in Arthur–Clozel (4.4)–(4.6) (printed pp. 43–44). First separate the split infinite
   components by their character distributions as in (4.7). Then vary the matching spherical
   factors outside `Σ` to separate the spectra by their characters on the upper spherical
   Hecke algebra, with the lower characters composed with the base-change homomorphism
   (Arthur–Clozel (6.2), printed p. 55, and Henniart–Lemaire II.6.10, printed pp. 125–126).
   For the character from `S`, the twisted side retains the σ-stable cuspidal `Π` whose
   Satake parameters are the residue-degree powers of those of `S`, at most one class by
   strong multiplicity one. The ordinary side retains the cuspidal `π'` with the same
   residue-degree powers. By the fibre theorem (Arthur–Clozel, Chapter III, Theorem 3.1, printed
   p. 201; the Library's `CyclicCuspidalFiberStatement`) the `π'` are the twists
   `S ⊗ (χ ∘ det)` with `χ` trivial on the idele norms. Each `χ_x` is trivial on `Z₁x`.
   Each twist lies in the lower central-character sector since `det(zI) = z^{r+1}` for
   `z ∈ Z₁x`. Their local traces coincide with those of `S` on the tests of step 3.
   At split places this follows from `Z₁x = K_x^×`, and at the other finite places in
   `Σ` from the determinant condition on the inputs, preserved by averaging. At the
   spherical places it follows from the determinant-norm support of the spherical
   transfer (Henniart–Lemaire II.6.13, printed p. 129). The sum is therefore `h` times
   the trace of `S`, where `h ≥ 1` counts distinct classes of twists. Choose nonzero
   lower trace factors at all places of `Σ` by the reference tests of step 3, including
   at `v` when establishing existence. The separated ordinary side is nonzero, so `Π`
   exists and `k = 1`. If the separated comparison is repeated with another finite
   set or other local tests, strong multiplicity one identifies the same `Π` from
   the common cofinite Satake data.

5. **Factorization and return to full-group tests.** Fix the local factors of step 3 at
   all places of `Σ` other than `v`. Factoring the two sides of the separated identity gives
   `a = (h/l) ∏_{x ∈ Σ, x ≠ v} tr π_x(F_x) ≠ 0` and an upper coefficient `b` given by the
   product of the twisted trace factors away from `v`, using the factorization of the global
   intertwiner (Arthur–Clozel, printed p. 56). At a finite split `v ∉ {v₁, v₂}`, absorb the
   comparison of the local intertwiner with the cyclic shift into `b`. The twisted trace at
   `Φ_v` is then the ordinary quotient trace on the convolution `F_v = f^ω`. It equals the
   ordinary full-group trace of `Π_w(f)`, and the lower quotient trace similarly equals the
   trace of `π_v(f)`. This gives clause 2. At `v` with one place above it, transport the
   upper component and the local intertwiner along `E_v ≅ L_w`. The operator identities in
   step 2 turn the two quotient traces at `(φ^η, f^ω)` into the full-group twisted and ordinary
   traces of clause 3. The coefficients and intertwiner were fixed before varying the tests.
   The homogeneity argument gives the clauses for all the indicated Haar measures.

   At any unramified place `x` where `D` is spherical, one can also put the spherical
   comparison at `x` and separate away from `x`. With the unit test at `x`, the lower trace
   is one, so the upper spherical projection has nonzero trace after twisting. Thus each
   upper component has a spherical line. Varying all spherical tests at `x` and dividing
   by the identity for the unit gives the base-change eigencharacter on that line and hence
   the residue-degree power at each place above `x`. At an auxiliary split place the
   isomorphism in step 6 also transfers spherical data. Form `P` with spherical reference
   vectors at all these upper places, keeping them outside its exceptional set. The finite
   factors of `Π` are irreducible admissible, and its central character is `η`, as required
   in clause 1.

6. **The auxiliary places.** For `v ∈ {v₁, v₂}`, put the coefficient test at `v` and the
   elliptic test at the other auxiliary place. Both placements satisfy step 1 because both
   places split completely and both lower components are supercuspidal. Use
   `F_v = d^{1-l} ξ`, `Φ_v = ξ ⊗ ⋯ ⊗ ξ` as in step 3, with the other factors chosen there
   and the same separated spectral class. Factorization gives
   `b · tr Π_w(F_v) = a · tr π_v(F_v)` with `a ≠ 0`, where these are quotient traces
   and the upper trace uses the convolution on the quotient. The lower trace is nonzero.
   The representation `Π_w` is irreducible admissible with central character `ω_v`, because
   the split norm is onto `K_v^×`. The left translates of `ξ` span a copy of `π_v`, by the
   coefficient formula with `π_v(g^{-1})` in the argument. For each vector `y` of a smooth
   representation `ρ` with this central character, the map `h ↦ ρ(h)y`, using the quotient
   operator
   `ρ(h) = ∫_{K_v^× \ G(K_v)} h(g)ρ(g) d̄g_v`, is equivariant for left translation.
   Therefore a nonzero action of `ξ` on the irreducible `Π_w` gives an isomorphism
   `Π_w ≅ π_v`, by the argument of Bernstein–Zelevinsky 1976, 2.42, part (4) (printed p. 27).
   The components at all other places above `v` are isomorphic to `Π_w` by σ-stability.
   Equality of characters of isomorphic admissible representations now gives clause 2 on
   all compactly supported tests, with `b = 1` and `a = 1`.
7. **Degree one.** If `l = 1`, every finite place splits and has a single place above it, so
   clause 3 is also asserted at `v₁` and `v₂`. There `σv` is the identity, the norm is an
   isomorphism `K_v ⊗_K L → K_v`, and concordance says that `φ`, transported to
   `GL_{r+1}(K_v)`, and `f` have the same regular orbital integrals for the compared measures.
   With `Π_w ≅ π_v` from step 6, the Weyl integration formula and the local integrability of
   the character of `π_v` (Harish-Chandra 1999, Theorem 16.3, printed p. 75) give
   `tr Π_w(φ) = tr π_v(f)` on regularly supported concordant pairs; so clause 3 holds there
   with `A` the identity, `b = 1` and `a = 1`.

For `r = 0`, take the norm pullback of the unitary idele class character. It gives the
split identifications, the norm comparison on characters in clause 3 with `A` the identity,
and the unramified parameters by the residue-degree formula for the norm of a uniformizer.
For the one-place comparison, concordance on `GL₁` integrates `φ` along the fibres of
the norm to give `f` on the norm subgroup, with the compared measures, and gives zero at
nonnorms. Integration of the lower character against this pushforward is integration of
the norm-pullback character against `φ`. This gives `a = b = 1`. The page of
`CuspidalCyclicBaseChangeLiftAnyDegreeStatement` describes this case as well.

## Provenance

This is derived content: the statement is formulated here from the sources below, none of which
states it in this form. It follows the global comparison of Arthur–Clozel 1989, Chapter 1,
§6.3, through (6.2)–(6.3) (printed pp. 55–56), with the norm-trivial twists as on printed
p. 57. Henniart–Lemaire 2011, I.2.9–I.2.10 and II.2.6–II.2.8 give the passage between the
full-group local tests and the centrally equivariant ones. Their II.6.13 (printed pp. 129–130)
uses regularly supported tests at the distinguished place. At the two auxiliary places,
the identity on all tests follows from component isomorphism via the isolating coefficient
in the fixed-central-character sector, as in step 6.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989 (Library source
`arthur-clozel-1989-base-change`), Chapter 1, Lemmas 2.4–2.5 (printed pp. 13–15),
(4.4)–(4.7) (printed pp. 43–44), §5 (printed pp. 48–50), §6.3 (printed pp. 54–57), and
Chapter 3, Theorem 3.1 (printed p. 201). Henniart–Lemaire, *Changement de base et induction
automorphe pour GL_n en caractéristique non nulle*, Mémoires de la SMF 124, 2011,
I.2.5 (printed pp. 17–18), I.2.9–I.2.10 (printed pp. 22–23), II.2.6–II.2.8 (printed
pp. 66–68), II.2.16 (printed pp. 77–78) and II.6.1–II.6.13 (printed pp. 118–130).
I. N. Bernstein and A. V. Zelevinsky, *Representations of
the group GL(n,F) where F is a non-archimedean local field*, Russian Math. Surveys 31:3 (1976)
(Library source `bernstein-zelevinsky-1976-representations-gln`): 2.42, part (4) of the proof
(printed p. 27). Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups*, University Lecture Series 16, AMS, 1999 (Library source
`harish-chandra-1999-admissible-invariant-distributions`): Theorem 16.3 (printed p. 75).
