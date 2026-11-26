# Rigidity of characters on the regular elliptic set

The module `Langlands.BaseChange.EllipticTraceRigidityStatement` states, as the proposition
`EllipticTraceRigidityStatement.{u, uV, uW}`, the following. Let `F` be a nonarchimedean local
field of characteristic zero and `H` an open subgroup of finite index of `Fˣ`. If the character
of an irreducible admissible representation `π` of `GL_n(F)` is a nonzero multiple of the
character of an irreducible supercuspidal representation `π₀` on all test functions supported
in the regular elliptic set with determinants in `H`, then `π ≅ π₀ ⊗ (χ ∘ det)` for a character
`χ` of `Fˣ` trivial on `H`. This file states the proposition and does **not** prove it.

## Notation (Library and Mathlib)

- `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]` (Mathlib,
  `Mathlib.NumberTheory.LocalField.Basic`): `F` is a nonarchimedean local field with its valued
  topology; with `[CharZero F]` it is a finite extension of some `ℚ_p`.
- `GeneralLinear n F` (module `Langlands.Group.GL.Basic`) is `GL_n(F)`, the units of the
  matrix ring. Its Hausdorff, locally compact and totally disconnected topology comes from
  `LocalFieldTopology.generalLinear_t2Space`, `generalLinear_locallyCompactSpace` and
  `generalLinear_totallyDisconnectedSpace` (module `Langlands.Group.GL.LocalFieldTopology`),
  and the σ-algebra is the Borel σ-algebra. `GeneralLinear.determinant : GeneralLinear n F →* Fˣ`
  is the determinant.
- `Fˣ` carries Mathlib's topology on a unit group, which for the topological field `F` is the
  subspace topology. `IsOpen (H : Set Fˣ)` says that `H` is open, and `H.FiniteIndex`
  (Mathlib's `Subgroup.FiniteIndex`) that `Fˣ/H` is finite.
- `IsAdmissible π` (module `Langlands.Representation.Smooth.Definitions`): every vector of `V`
  is fixed by an open subgroup, and the vectors fixed by any open subgroup form a
  finite-dimensional space. No topology is put on `V`.
- `π.IsIrreducible` (Mathlib's `Representation.IsIrreducible`): `V` is nonzero and has no
  subrepresentation other than `0` and `V`.
- `GeneralLinear.IsSupercuspidal π₀` (module
  `Langlands.Representation.Classification.Supercuspidal`): `π₀` is admissible (the first
  component, `hπ₀.1`) and its Jacquet coinvariants vanish along every proper block parabolic
  subgroup and every conjugate of its unipotent radical.
- `SchwartzBruhat (GeneralLinear n F)` (module `Langlands.HarmonicAnalysis.Basic`): the
  locally constant, compactly supported functions `GL_n(F) → ℂ`.
- `IsEllipticSupported f` (module `Langlands.BaseChange.EllipticSupport`): every `g` with
  `f g ≠ 0` is regular elliptic (`IsRegularElliptic`, module
  `Langlands.JacquetLanglands.RegularElliptic`): its characteristic polynomial is separable
  and irreducible over `F`.
- `Character.distribution μ π hπ f` (module `Langlands.Representation.Character.Basic`): the
  trace of the finite-rank operator `π(f) v = ∫ f(g) π(g) v dμ(g)`, written `tr π(f)` below.
- `twist (χ.comp GeneralLinear.determinant) π₀` (module
  `Langlands.Representation.Twist.Definitions`): the representation `g ↦ χ(det g) · π₀(g)` on
  the space `W` of `π₀`, written `π₀ ⊗ (χ ∘ det)` below.
- `π.Equiv ρ` (Mathlib): linear isomorphisms `V ≃ W` intertwining `π` and `ρ`;
  `Nonempty (π.Equiv ρ)` says that `π` and `ρ` are isomorphic.

## Statement

`EllipticTraceRigidityStatement.{u, uV, uW}` quantifies over a field `F : Type u` with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]` and over
`n : ℕ`. The topological instances and the Borel σ-algebra on `GL_n(F)` are introduced inside
the statement. The claim: for every `H : Subgroup Fˣ` that is open and of finite index; all
complex vector spaces `V : Type uV` and `W : Type uW`; every
`π : Representation ℂ (GeneralLinear n F) V` with `hπ : IsAdmissible π` and `π.IsIrreducible`;
every `π₀ : Representation ℂ (GeneralLinear n F) W` with
`hπ₀ : GeneralLinear.IsSupercuspidal π₀` and `π₀.IsIrreducible`; every `c : ℂ` with `c ≠ 0`;
and every Haar measure `μ` on `GL_n(F)`: if

`Character.distribution μ π hπ f = c * Character.distribution μ π₀ hπ₀.1 f`

for every `f : SchwartzBruhat (GeneralLinear n F)` with `IsEllipticSupported f` and with
`GeneralLinear.determinant g ∈ H` whenever `f g ≠ 0`, then there is `χ : Fˣ →* ℂˣ` with
`χ h = 1` for all `h ∈ H` and
`Nonempty (π.Equiv (twist (χ.comp GeneralLinear.determinant) π₀))`.

## Remarks

- No continuity is asked of `χ`: being trivial on the open subgroup `H`, it is locally
  constant, so `π₀ ⊗ (χ ∘ det)` is again smooth.
- In characteristic zero every subgroup of finite index `m` of `Fˣ` contains the subgroup of
  `m`-th powers, which is open, so the openness of `H` follows from its finite index; the
  statement keeps both hypotheses.
- The conclusion cannot be sharpened to `π ≅ π₀`: for `χ` trivial on `H` and `f` vanishing
  off `det⁻¹(H)`, `tr (π₀ ⊗ (χ ∘ det))(f) = tr π₀(f)`, so `π₀ ⊗ (χ ∘ det)` satisfies the
  hypothesis with `c = 1`. Henniart–Lemaire (II.6.13) make the analogous observation for
  `H = N_{E/F}Eˣ` and test functions whose regular orbital integrals vanish off the norms.
- `n = 0`: `GL_0(F)` is trivial and its element is not regular elliptic (the characteristic
  polynomial `1` is not irreducible), so only `f = 0` is tested and the hypothesis holds for
  every `c`. The conclusion holds with `χ = 1`: an irreducible representation of the trivial
  group is one-dimensional with trivial action, so `π` and `π₀` are isomorphic.
- `n = 1`: every element of `GL_1(F) = Fˣ` is regular elliptic, `π` and `π₀` are characters,
  and the hypothesis says `π = c π₀` on `H`; evaluation at `1` gives `c = 1`, and
  `χ = π π₀⁻¹` works.
- For `n ≥ 1` the hypothesis forces `c = 1`: once `π ≅ π₀ ⊗ (χ ∘ det)` with `χ` trivial on `H`,
  the characters of `π` and `π₀` agree on `det⁻¹(H)`, and that of `π₀` is not identically zero
  on the regular elliptic elements there (step 4 of the sketch below).

## Why it is true (sketch)

Let `n ≥ 1` (the case `n = 0` is above). Write `G = GL_n(F)` and `G' = det⁻¹(H)`, an open and
closed normal subgroup with `G/G' ≅ Fˣ/H` finite abelian (the determinant is onto). Let `X` be
the group of characters of `Fˣ/H`, so that `1_{G'} = |X|⁻¹ Σ_{ψ ∈ X} ψ ∘ det`. Let `Z ≅ Fˣ` be
the centre of `G` and `Z_H = {z ∈ Z : zⁿ ∈ H} = Z ∩ G'`, of finite index in `Z`. An irreducible
admissible `ρ` has a central character `ω_ρ`, and its character function `Θ_ρ` satisfies
`Θ_ρ(zg) = ω_ρ(z) Θ_ρ(g)` and `Θ_{ρ ⊗ (ψ ∘ det)}(g) = ψ(det g) Θ_ρ(g)`. Twisting `π` and `π₀`
by a common unramified character `|det|^s` changes neither the hypothesis nor the conclusion,
so we may assume that the central character `ω₀` of `π₀` is unitary. Then `π₀` is unitary, and
on regular elements `Θ_{π₀}(γ⁻¹) = Θ_{π̌₀}(γ)` (for the contragredient `π̌₀`) equals the complex
conjugate of `Θ_{π₀}(γ)` (HL II.4.10, Remarque (2)).

*Measures.* Fix a Haar measure `dz` on `Z` and give `Z\G` the quotient `dḡ` of `μ` by `dz`. For
a maximal torus `T` with `T/Z` compact (an elliptic torus) give `T/Z` total mass `1` and `T\G`
the matching quotient measure. Then the orbital integral at a regular `γ ∈ T` of a function `φ`
that transforms under `Z` by a character is `Λ(φ, γ) = ∫_{Z\G} φ(g⁻¹γg) dḡ`, the normalization
of HL II.4.10. Let `T_1, …, T_r` represent the conjugacy classes of elliptic maximal tori, `W_i`
be the Weyl group of `T_i` and `D` the Weyl discriminant.

1. *Pointwise identity.* The characters of `π` and `π₀` are given by locally integrable
   functions `Θ_π`, `Θ_{π₀}`, locally constant on the regular semisimple set (Harish-Chandra;
   the Library's `CharacterLocalIntegrabilityStatement` states this). The regular elliptic set
   is open (`Langlands.BaseChange.regularEllipticOpen`), so indicators of small compact open
   sets of regular elliptic elements of `G'` are admissible test functions, and the hypothesis
   gives `Θ_π = c Θ_{π₀}` pointwise on `G'_ell`, the regular elliptic elements of `G'`.
2. *Supercuspidal orthogonality.* Choose `v` in the space of `π₀` and a smooth linear form `ℓ`
   with `ℓ(v) = 1`, let `d_{π₀}` be the formal degree of `π₀` relative to `dḡ`, and put
   `e(g) = d_{π₀} ℓ(π₀(g⁻¹)v)`, a normalized coefficient of the contragredient `π̌₀` (the
   construction described in the Markdown of the Library's `SupercuspidalCuspFormStatement`).
   It is locally constant, compactly supported modulo `Z` because `π₀` is supercuspidal, and
   `e(zg) = ω₀(z)⁻¹ e(g)`; so `e` lies in the space `C_c^∞(G, ω₀)` of HL I.2.9. For an
   admissible `ρ` with central character `ω₀` the operator
   `ρ(e)w = ∫_{Z\G} e(g) ρ(g)w dḡ` is well defined, since the central characters cancel in the
   integrand, and has finite rank. Writing `e(g) = ∫_Z f(zg) ω₀(z) dz` with `f` compactly
   supported (a cut-off as in `SupercuspidalCuspFormStatement`) gives `ρ(e) = ρ(f)`, so the
   trace of `ρ(e)` is `∫_{Z\G} e(g) Θ_ρ(g) dḡ`. If `ρ` is irreducible, then `tr ρ(e) = 1` when
   `ρ ≅ π₀` and `tr ρ(e) = 0` otherwise. Indeed, Schur orthogonality gives `π₀(e)w = ℓ(w)v`.
   For `ρ ≇ π₀` and a fixed vector `w'` of `ρ`, the map
   `w ↦ ∫_{Z\G} ℓ(π₀(g⁻¹)w) ρ(g)w' dḡ` intertwines `π₀` with `ρ`, hence is zero by
   irreducibility, and its value at `v` is `d_{π₀}⁻¹ ρ(e)w'`. No temperedness is needed. In
   particular `e` is a pseudo-coefficient of `π₀` in the sense of Arthur–Clozel,
   Corollary 2.10 (untwisted case). Hence its orbital integrals vanish at the regular
   semisimple elements that are not elliptic (Arthur–Clozel, Lemma 2.12 (ii)). At a regular
   elliptic `γ`, HL II.4.10, Lemme 2 with `E = F`, gives
   `Λ(e, γ) = Σ_ρ tr ρ(e) Θ_{ρ̌}(γ) = Θ_{π̌₀}(γ) = conj(Θ_{π₀}(γ))`, the sum running over the
   essentially discrete series with central character `ω₀`. By the Weyl integration formula
   on `Z\G`, to which only the elliptic tori contribute, every irreducible admissible `ρ` with
   central character `ω₀` satisfies

   `δ_{ρ ≅ π₀} = tr ρ(e) = Σ_i |W_i|⁻¹ ∫_{T_i/Z} |D(t)| Θ_ρ(t) conj(Θ_{π₀}(t)) dt,`

   where `δ_{ρ ≅ π₀}` is `1` if `ρ ≅ π₀` and `0` otherwise. The integrand is invariant under
   `Z` because `ω_ρ = ω₀` and `|ω₀| = 1`. The integral converges absolutely, because `e Θ_ρ`
   is integrable on `Z\G`. This is the fixed-central-character analogue, for every irreducible
   admissible `ρ`, of the pseudo-coefficient identities of Arthur–Clozel, Corollary 2.10 and
   Lemma 2.12, and of Kazhdan, Theorem K, which test tempered representations (Kazhdan with
   compact centre).
3. *Restriction to `G'`.* For an irreducible admissible `ρ` with `ω_ρ = ω₀` on `Z_H` put

   `⟨Θ_ρ, Θ_{π₀}⟩_H = Σ_i |W_i|⁻¹ ∫_{T_i/Z_H} 1_{G'}(t) |D(t)| Θ_ρ(t) conj(Θ_{π₀}(t)) dt,`

   where `T_i/Z_H` carries the measure that is the mass-one measure on `T_i/Z` times counting
   measure on the finite group `Z/Z_H`. The integrand is invariant under `Z_H`, because
   `Z_H ⊂ G'`. Expand `1_{G'}`. The summand for `ψ` has first factor `Θ_{ρ ⊗ (ψ ∘ det)}` and
   transforms under `Z` by `z ↦ ψ(zⁿ) ω_ρ(z) ω₀(z)⁻¹`, which is trivial on `Z_H`. Summing over
   `Z/Z_H`, it contributes `[Z : Z_H]` times the integral of step 2 for `ρ ⊗ (ψ ∘ det)` when
   that representation has central character `ω₀`, and `0` otherwise. Hence step 2 gives

   `⟨Θ_ρ, Θ_{π₀}⟩_H = [Z : Z_H] |X|⁻¹ · #{ψ ∈ X : ρ ⊗ (ψ ∘ det) ≅ π₀}.`

   HL II.4.8, formulas (1)–(4), average in the same way over the characters trivial on
   `N_{E/F}Eˣ` to restrict the elliptic pairing of discrete series to the norms.
4. *Conclusion.* For `ρ = π₀` the right side of step 3 is at least `[Z : Z_H] |X|⁻¹ > 0`
   (take `ψ = 1`), so `Θ_{π₀}` is not identically zero on `G'_ell`. Since `zγ ∈ G'_ell` for
   `z ∈ Z_H` and `γ ∈ G'_ell`, comparing `Θ(zγ) = ω(z) Θ(γ)` on both sides of step 1, at a `γ`
   with `Θ_{π₀}(γ) ≠ 0`, gives `ω_π = ω₀` on `Z_H` (this uses `c ≠ 0`). So `⟨Θ_π, Θ_{π₀}⟩_H` is
   defined. Its integrand only involves `G'_ell`, so step 1 gives
   `⟨Θ_π, Θ_{π₀}⟩_H = c ⟨Θ_{π₀}, Θ_{π₀}⟩_H ≠ 0`. By step 3, `π ⊗ (ψ ∘ det) ≅ π₀` for some
   `ψ ∈ X`, and `χ = ψ⁻¹` is trivial on `H` with `π ≅ π₀ ⊗ (χ ∘ det)`.

The same device, orthogonality relations on the kernel of a character composed with the
determinant, appears in the proof of Arthur–Clozel, Proposition 6.6 (ii).

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL.
  - I.2.9, printed p. 22: `C_c^∞(G(F), ω)` is the space of locally constant functions that
    are compactly supported modulo the centre and satisfy `f(zγ) = ω(z)⁻¹ f(γ)` on the norm
    subgroup of the centre; the coefficient `e` of step 2 lies in it for `E = F`.
  - II.4.6, Théorème (2), printed p. 88: every σ-discrete series of `G(E)` lifts a discrete
    series `π` of `G(F)`, and every other generic irreducible representation of `G(F)` lifting
    to it is isomorphic to `κπ` for a character `κ ∈ K(E/F)`, the characters of `Fˣ` trivial
    on `N_{E/F}Eˣ`.
  - II.4.8, Lemme and formulas (1)–(4), printed pp. 90–91: the orthogonality relations for the
    characters of discrete series, with the centre replaced by `N_{E/F}Eˣ`; the elliptic
    pairing is split according to the class of `det γ` modulo `N_{E/F}Eˣ`, and averaging over
    `κ ∈ K(E/F)` isolates the part on the norms, which detects whether `π' ≅ κπ` for some
    `κ`. This is the restriction to elliptic norms and the character averaging of steps 3–4,
    for discrete series and `H = N_{E/F}Eˣ`.
  - II.4.10, Lemmes 1 and 2 and Remarque (2), printed pp. 93–94: for an elliptic
    `f ∈ C_c^∞(G(F), ω)` and regular elliptic `γ`, `Λ(f, γ) = Σ_π Θ_π(f) Θ_{π̌}(γ)` over the
    essentially discrete series with central character extending `ω`, with the orbital
    integral normalized as an integral over the quotient of `G(F)` by the central norm
    subgroup; and `conj(Θ_π(γ)) = Θ_{π̌}(γ)` for unitary `π`. With `E = F` this is the
    orbital-integral formula used in step 2.
  - II.6.12, Lemme, printed pp. 128–129: the global counterpart, the cuspidal representations
    lifting to a given one are the twists `κⁱπ`.
  - II.6.13, printed pp. 129–130: for `f_v` concordant with some `φ_v`, so that its regular
    orbital integrals vanish off the norms, the Weyl integration formula gives
    `tr((χρ)(f_v)) = tr(ρ(f_v))` for every admissible `ρ` and every `χ` trivial on
    `N_{E/F}Eˣ`. The global comparison then gives a nonzero constant `c` with
    `tr π'_{v₀}(f_{v₀}) = c · tr(Π'_{v₀}(φ_{v₀}) ∘ A)` for all concordant pairs
    `(φ_{v₀}, f_{v₀})` supported in the σ-regular and regular sets.
  - II.6.17, printed p. 132: the same proportionality, between the twisted trace of `Π'_{v₀}`
    and the trace of `τ'_{v₀}`, for all concordant pairs supported in the σ-regular and
    regular sets.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14), Chapter 1.
  - Corollary 2.10, printed p. 18: a pseudo-coefficient `φ` of a σ-discrete `Π` with central
    character `X` satisfies `φ(zg) = X(z)⁻¹ φ(g)`, acts by `T(φ) = ∫_{Z(E)\G(E)} φ(g) T(g) dg`,
    has `trace(Π(φ) I_σ) = 1`, and `trace(T(φ) I_σ) = 0` for every tempered σ-stable `T ≇ Π`
    with central character `X`.
  - Lemma 2.12 and its proof, printed p. 19: the (twisted) orbital integrals of a
    pseudo-coefficient vanish off the (σ-)elliptic set and not identically on it, by the
    identity `1 = trace(Π(φ) I_σ) = ∫ Θ_{Π,σ}(g) φ(g) dg`. Step 2 uses the untwisted case.
  - §6.3, proof of Theorem 6.2 (b), printed pp. 56–57: the local characters of the twists
    `π ⊗ χ` appearing in the comparison coincide "on the image of the norm", and the
    comparison of trace formulas gives, at a place `v₃`, `trace π_{v₃} ∘ N = c · trace(Π_{v₃} I_σ)`
    for some constant `c`. So the character of `π_{v₃}` equals a Steinberg character on the
    image of the norm, and `π_{v₃}` is shown to be a Steinberg representation. The same page
    notes that all representations lifting a given one are obtained from one of them by
    twisting by powers of the local class field character.
  - Proposition 6.6 (ii) and its proof, printed pp. 58–59: orthogonality relations for
    σ-discrete characters, reduced to orthogonality on `G(F)¹ = {x : ξ(det x) = 1}`.
  - Proposition 6.7 and its proof, printed p. 59: if a tempered `π = ind(π_1 ⊗ ⋯ ⊗ π_r)`, with
    the `π_i` discrete series, lifts to `Π`, the other representations lifting to `Π` are the
    inductions of the `π_i ⊗ (η_i ∘ det)` with `η_i` powers of the class field character. The
    proof uses that such a representation has the same character as `π` on the image of the
    norm, together with the orthogonality relations.
- Kazhdan, *Cuspidal geometry of p-adic groups*, J. Analyse Math. 47 (1986), 1–36, source ID
  `kazhdan-1986-cuspidal-geometry`, file
  `/home/taskhub/central-library/Kazhdan--Cuspidal geometry of p-adic groups--1986.pdf`
  (PDF page = journal page). Kazhdan assumes throughout that the centre of `G` is compact
  (p. 2 and §1.1, p. 7), and pairs an admissible `π` with a test function by
  `(π, f) = Tr π(f*)`, `f*(g) = f(g⁻¹)` (p. 2).
  - Theorem A, p. 3: the virtual representations whose characters vanish on the functions with
    vanishing non-elliptic orbital integrals are the combinations of properly induced ones.
  - Theorem K, p. 7, proved as §5, Proposition 3, p. 28: for a square-integrable `π` there is
    `h_π` with vanishing non-elliptic orbital integrals that separates `π` from the other
    tempered irreducible representations, and whose orbital integrals on the regular elliptic
    set are given by the character of `π`. In Proposition 3, `h_π` is obtained from the
    coefficient `f_π(g) = (π(g)v, v)` of `π`, and `(π', h_π) = Tr π'(h_π*)` applies `π'` to the
    inverted function; the coefficient `e` of step 2 is likewise inverted.

  For `GL_n`, whose centre is not compact, step 2 works instead with a fixed central character
  and integration over `Z\G`. Its intertwiner argument covers every irreducible admissible `ρ`
  with central character `ω₀`, not only the tempered ones that Kazhdan and Arthur–Clozel test.

## Related statements in the Library

- `EllipticNormCriterionStatement`: for a cyclic `F`-algebra `E` with generator `σ`, a regular
  elliptic `γ` satisfies `IsNorm σ l γ` (in `GL_n(E)` it is conjugate to a
  norm `δ σ(δ) ⋯ σ^{l-1}(δ)`, `δ ∈ GL_n(E)`) if and only if `det γ` lies in the image of the norm
  `Eˣ → Fˣ`. Test functions supported on regular elliptic norms are therefore the test
  functions of this statement for `H` that image.
- `EllipticDiscreteTraceSeparationStatement`: in positive rank, an irreducible admissible
  essentially square-integrable `π` whose character agrees, on all elliptically supported test
  functions, with a linear combination of the characters of finitely many irreducible
  admissible essentially square-integrable `ρ i` is isomorphic to one of the `ρ i`. It tests all
  regular elliptic elements and asks `π` to be essentially square-integrable. The present
  statement also covers rank `0`, tests only `det⁻¹(H)`, allows any irreducible admissible `π`,
  and has the twist by `χ` in its conclusion.
- `TwistedSupercuspidalEllipticNonvanishingStatement`, `EllipticTransferStatement`,
  `TwistedSupercuspidalCuspFormMatchingStatement` and
  `TwistedTraceRegularNonvanishingStatement`: the other local inputs of the comparison of the
  simple trace formula with its twisted form for cyclic base change.

## Derived content

The statement is formulated for the Library. In the proof of local base change by the simple
trace formula (Arthur–Clozel §6.3; HL II.6.13 and II.6.17), the global comparison yields at the
place under study a proportionality, with a nonzero constant, between the ordinary trace of a
representation of `GL_n(F)` and the twisted trace of a representation of `GL_n(E)`. In HL it
holds for all concordant pairs of test functions supported in the regular and σ-regular sets,
and the regular orbital integrals of the ordinary test functions in such pairs vanish off the
norms; in Arthur–Clozel it appears as an identity between the character of `π_{v₃}` composed
with the norm and `c` times a twisted character. The local representation is then identified
up to a character of `Fˣ/N_{E/F}Eˣ` (HL II.4.6 (2)).

The present proposition is a formulation of the local step that remains when two ordinary
characters are compared: it restricts to test functions supported on regular elliptic
elements with determinant in `H`, and compares the characters of `π` and `π₀` there. For
`H = N_{E/F}Eˣ` these are the test functions supported on regular elliptic norms
(`EllipticNormCriterionStatement`). HL II.4.8, formulas (1)–(4), carry out this restriction and
the averaging over the characters of `Fˣ/H` for discrete series, and Arthur–Clozel §6.3 and
Proposition 6.7 identify representations from equality of ordinary characters on the image of
the norm. Here `π₀` is supercuspidal, `π` is any irreducible admissible representation, `H` is
any open subgroup of finite index, every nonzero `c` and every Haar measure are allowed, and the
conclusion records that `χ` is trivial on `H`.
