# The spectral comparison at a place with one place above for a stable cusp (statement)

Module `Langlands.TraceFormula.CyclicStableCuspidalSpectralComparisonStatement`, namespace
`Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.CyclicStableCuspidalSpectralComparisonStatement.{uF, uE, uV, uW}`.

In words: let `E/F` be a cyclic extension of number fields of degree `l` (any `l ≥ 1`) with
generator `σ`, in which every infinite place of `F` splits completely. Let `v` be a finite place
of `F` with only one place `w` of `E` above it, and `v₁ ≠ v₂` finite places of `F` that split
completely in `E`. Let `Π` be a cuspidal automorphic representation of `GL_n(𝔸_E)`
(`n = r + 1`) with unitary central character, isomorphic to its `σ`-conjugate, whose local
components at all places above `v₁` and above `v₂` are supercuspidal and whose local component
`Π_w` is irreducible and admissible. Then there are finitely many cuspidal automorphic
representations `π_1, …, π_k` of `GL_n(𝔸_F)` with unitary central characters, each having `Π`
as weak base change and with irreducible admissible local components `π_{i,v}`, a
`σ`-intertwiner `A` of `Π_w`, complex numbers `a_1, …, a_k` and Haar measures at `v` such that

`tr (Π_w(φ) ∘ A) = Σ_i a_i · tr π_{i,v}(f)`

for all concordant (matching) test functions `φ` on `GL_n(F_v ⊗_F E)` and `f` on `GL_n(F_v)`
such that `φ` is supported in the `σ`-regular set, `f` in the regular semisimple set, and
`det g` is a norm from `(F_v ⊗_F E)^×` wherever `f g ≠ 0`.

This is the comparison of the simple trace formula with its twisted form for the given
`σ`-stable `Π`, after separation by Hecke eigenvalues and factorization over the bad places,
read at `v`: the identity (6.5) of Arthur–Clozel 1989, Chapter 1, §6.3(b) (printed p. 57),
`ℓ trace(Π(φ) I_σ) = Σ trace π'(f)`, before its right side is collapsed with the fibre theorem
III.3.1. The Library's `CyclicStableCuspidalDescentTraceIdentityStatement` is the collapsed
form, with a single `π` and a constant `c ≠ 0`; the module
`Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityReductionStatement` states that
the collapsed form follows from this statement, the equality of traces in a fibre
(`Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement`) and the nonvanishing
of twisted traces (`Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement`).

The module declares five `local instance`s of `AddCommGroup`: on the Library's form spaces
`Langlands.Automorphic.RationalInvariantFunctions`, `ContinuousRationalFunctions`,
`FiniteSmoothRationalFunctions` and `AutomorphicForms`, and on the carrier `A.Space` of a
`LocalRealization`. They are `Submodule.addCommGroup _`, as in the Library's
`Langlands.Automorphic.SupercuspidalComponent`. They are not exported.

## Setting and notation

The hypotheses, the binders and the local objects at `v` are those of the Library's
`Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityStatement`, copied verbatim; its
Markdown page describes each of them. In short:

- `F : Type uF`, `E : Type uE` number fields with compact adele quotients, `σ : E ≃ₐ[F] E` and
  `l : ℕ` with `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`), and
  `IsCyclicShiftSplit F E A σ l` (module
  `Langlands.TraceFormula.CyclicFieldGlobalizationStatement`) at the infinite places and at
  `v₁`, `v₂`: these places split completely, `σ` permuting the places above them cyclically.
- `v : Langlands.Global.FinitePlace F` and `w : FinitePlacesAbove E v` with `∀ w', w' = w`.
- `T : CuspidalOperatorRealization E r` with a spectral presentation
  `P : CuspidalSpectralPresentation.{uE, uW} T` (module
  `Langlands.Automorphic.CuspidalSpectralPresentation`), with unitary central character
  (`ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter`, module
  `Langlands.Automorphic.AssociatedFactorStatement`) and `T.isoClass.IsGaloisStable σ`.
- `LocalRealization.IsSupercuspidal`, `IsIrreducible`, `IsAdmissible`: the Library's predicates on
  local components.
- `CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}` (module
  `Langlands.Automorphic.Unramified.WeakTransfer`): spectral systems of the two classes (universes
  `uV` and `uW`) of which the one over `E` is an arithmetic weak base change of the one over `F`.
- Local data at `v`: `F_v := v.adicCompletion F` with the local field structure of
  `CompletionPadic.topologicalData v`; `E_v := F_v ⊗[F] E` with its module topology;
  `σv := Algebra.TensorProduct.congr AlgEquiv.refl σ`; and
  `PiV := (P.localComponent w.1).representation.comp (Matrix.GeneralLinearGroup.map h)`, where
  `h : E_v → E_w` is the `w`-component of the Library's `finiteTensorMap v` (module
  `Langlands.Global.AdelicFunctoriality.Norm`), an isomorphism as `w` is the only place above
  `v`. `GL_n(F_v)` and `GL_n(E_v)` carry their Borel σ-algebras.
- `Character.distribution μ ρ hρ f` (module `Langlands.Representation.Character.Basic`) is the
  trace of `ρ(f) = ∫ f(g) ρ(g) dμ(g)`; `twistedDistribution μE PiV hP A φ` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`) is the trace of `PiV(φ) ∘ A` for a
  `SigmaIntertwiner σv (r + 1) PiV` `A`, that is `A ∘ PiV(g) = PiV(σv g) ∘ A`.
- `AreConcordant σv l μF μE φ f`, `IsSigmaRegularSupported σv l φ` and `IsRegularSupported f`
  (module `Langlands.BaseChange.OrbitalIntegral`): matching of orbital integrals in the sense of
  Henniart–Lemaire I.2.5 (printed p. 17) for measures compatible with `μF` and `μE`, and support
  in the `σv`-regular, respectively regular semisimple, set.
- `(Units.map (Algebra.norm F_v)).range` is the norm subgroup `N(E_v^×)` of `F_v^×`, and
  `GeneralLinear.determinant` the determinant `GL_n(F_v) → F_v^×`.
- `∑ i, …` is the Mathlib finite sum over `i : Fin k`.

## Statement

For all `F`, `E`, `σ`, `l`, `v`, `w`, `v₁`, `v₂`, `r`, `T`, `P` as above, assume:

1. `IsCyclicAlgebra σ l`;
2. `IsCyclicShiftSplit F E u.Completion σ l` for every infinite place `u` of `F`;
3. `w` is the only place of `E` above `v`;
4. `v₁ ≠ v₂`, `IsCyclicShiftSplit F E (v₁.adicCompletion F) σ l` and
   `IsCyclicShiftSplit F E (v₂.adicCompletion F) σ l`;
5. `T` has unitary central character and `T.isoClass.IsGaloisStable σ`;
6. `P.localComponent w₁.1` is supercuspidal for every `w₁ : FinitePlacesAbove E v₁`, and
   `P.localComponent w₂.1` is supercuspidal for every `w₂ : FinitePlacesAbove E v₂`;
7. `P.localComponent w.1` is irreducible and admissible.

Then there are `k : ℕ`, `S : Fin k → CuspidalOperatorRealization F r` and
`D : ∀ i, CuspidalSpectralPresentation.{uF, uV} (S i)` such that

- for every `i`: `S i` has unitary central character,
  `IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass (S i).isoClass`, and
  `π_{i,v} := (D i).localComponent v` is irreducible and admissible;
- there are `hπ : ∀ i, Langlands.IsAdmissible π_{i,v}.representation`,
  `hP : Langlands.IsAdmissible PiV`, `A : SigmaIntertwiner σv (r + 1) PiV` and `a : Fin k → ℂ`,
  and Haar measures `μF` on `GL_n(F_v)` and `μE` on `GL_n(E_v)`, such that for all
  `φ : SchwartzBruhat (GL_n(E_v))` and `f : SchwartzBruhat (GL_n(F_v))` with
  - `AreConcordant σv l μF μE φ f`,
  - `IsSigmaRegularSupported σv l φ`,
  - `IsRegularSupported f`,
  - `GeneralLinear.determinant g ∈ N(E_v^×)` for every `g` with `f g ≠ 0`,

  we have
  `twistedDistribution μE PiV hP A φ = ∑ i, a i * Character.distribution μF π_{i,v}.representation (hπ i) f`.

Remarks on the form.

- **A sum, not one term.** The comparison of trace formulas matches the twisted trace of `Π`
  with the traces of all cuspidal `π'` whose base change agrees with `Π` outside a finite set of
  places. This statement keeps that sum. Collapsing it to one term (the fibre theorem and the
  equality of the local characters of the twists on the image of the norm) and showing that it
  is not empty (the nonvanishing of twisted traces) are not part of it.
- **Fixed Haar measures.** The measures `μF`, `μE` are existential: they come from the
  components at `v` of the global measures. The statement asserts the identity for this one pair
  only. By scaling, the identity then holds for every pair of Haar measures, with the same `A`
  and the same coefficients `a i`. Let `μF = s • μF⁰` and `μE = t • μE⁰` with `s, t > 0`, where
  `μF⁰`, `μE⁰` is the pair of the statement. The associated quotient measures scale in the same
  way, so `(φ, f)` is concordant for `(μF, μE)` exactly when `(φ, (s/t) • f)` is concordant for
  `(μF⁰, μE⁰)`. The support conditions do not change under this rescaling. Apply the identity for
  `(μF⁰, μE⁰)` to `(φ, (s/t) • f)` and multiply by `t`. The integrated actions are linear in the
  measures, so the left side becomes the twisted trace for `μE`, and each term on the right
  becomes `a i · tr π_{i,v}(f)` for `μF`. For example, doubling only `μF` replaces a concordant
  `f` by `f / 2`, whose ordinary traces for `2 • μF⁰` are the old ones; changing a coefficient
  would break a one-term identity with a nonzero trace. This is the computation of the remark
  "`c` before the measures" on the page of `CyclicStableCuspidalDescentTraceIdentityStatement`.
- **No normalization of the left side.** A factor `b ≠ 0` in front of the twisted trace, as in
  `ℓ trace(Π(φ) I_σ)` of Arthur–Clozel (6.5) or in the product `X` of local twisted traces at
  the other bad places (step 5 of "Why the statement is true" on the page of
  `CyclicStableCuspidalDescentTraceIdentityStatement`), is divided into the `a i`.
- **`k = 0` is not excluded.** If `k = 0` the identity says that the twisted trace vanishes on
  all `φ` as in the statement. That never happens, by the nonvanishing of twisted traces on the
  `σv`-regular set and regular transfer, but this statement does not say so.
- **The family is not normalized.** The `S i` need not be pairwise non-isomorphic and the `a i`
  may vanish; only the identity and the properties of each `S i` are asserted.
- **Degree one is included.** The statement covers `l = 1`, where it follows without a trace
  formula (below).

## Why the statement is true

Write `Π`, `π'` for the representations of `T` and of cuspidal realizations over `F`, `G = GL_n`.

### Degree one

If `l = 1`, the argument "Degree one" on the page of
`CyclicStableCuspidalDescentTraceIdentityStatement` gives a cuspidal `S` over `F` (a
representative of the arithmetic pullback of the class of `T` along the field isomorphism
`F ≃+* E`) with unitary central character and the class of `T` as weak base change, a
presentation `D` of `S` with irreducible admissible component `π_v` at `v`, and the identity
`tr (PiV(φ) ∘ A) = tr π_v(f)` with `A` the identity, for all Haar measures and all pairs as in
the statement. Take `k = 1`, `S 0 = S`, `D 0 = D` and `a 0 = 1`.

### Degree at least two

Then `v ∉ {v₁, v₂}`, since `v₁` and `v₂` have `l ≥ 2` places above them and `v` only one. The
argument is steps 1–5 of "Degree at least two" on the page of
`CyclicStableCuspidalDescentTraceIdentityStatement`, which follow Arthur–Clozel 1989, Chapter 1,
§6.3(b) (printed pp. 56–57, with the simple trace formulas of Lemmas 2.4–2.5, printed
pp. 13–15) and Henniart–Lemaire 2011, II.6.2–II.6.6 (printed pp. 118–123). In outline:

1. The central character of `Π` factors through the norm, `ω_Π = ω ∘ N` on the norm subgroup
   `Z₁ = N(𝔸_E^×)` of the center.
2. At `v`, averaging over the center relates the compactly supported `φ` and `f` of the
   statement to functions in the spaces of the trace formulas with central character, without
   changing traces, concordance or the support conditions.
3. Decomposable concordant global test functions `φ_𝔸`, `f_𝔸` are chosen with the given `φ`, `f`
   at `v`, a supercuspidal coefficient at `v₁`, a function supported in the regular elliptic set
   at `v₂`, functions with nonzero twisted trace on the components of `Π` at the other places of
   a finite set `Σ` (the Library's `TwistedTraceRegularNonvanishingStatement` and
   `RegularTransferStatement` at the finite ones), and spherical functions related by base change
   outside `Σ`.
4. The simple trace formula and its twisted form, compared through concordance
   (Henniart–Lemaire II.6.6, printed pp. 122–123: `d Σ_Π tr(Π(φ) ∘ A_Π) = Σ_π tr(π(f))`), give
   `Σ_{Π'} tr (Π'(φ_𝔸) ∘ I_σ) = c₀ Σ_{π'} tr π'(f_𝔸)` over the `σ`-stable cuspidal `Π'` and the
   cuspidal `π'` with the prescribed central character on `Z₁`.
5. Separation by Hecke eigenvalues outside `Σ` keeps only `Π' ≅ Π` on the left (strong
   multiplicity one) and on the right the `π'` whose unramified base change agrees with `Π`
   outside `Σ`, that is, of which `Π` is a weak base change. Factoring both sides over `Σ` gives
   `tr (Π_w(φ) ∘ A) · X = c₀' Σ_{π'} tr π'_v(f) · Y(π')`, with `X ≠ 0` the product of the local
   twisted traces of `Π` at the places of `Σ` other than `v` and `Y(π')` the product of the local
   traces of `π'` there.

The `π'` on the right are finitely many: the cuspidal spectrum with the prescribed central
character on `Z₁` has finite multiplicities, and by the fibre theorem (Arthur–Clozel III,
Theorem 3.1, printed p. 201; Library `CyclicCuspidalFiberStatement`) all of them are twists of one
of them by powers of the idele class character of `E/F`, so there are at most `l`. Each such
`π'` has unitary central character (its absolute value is a positive character of `C_F` whose
`l`-th power is trivial, as in step 6 of the page of the descent statement) and a presentation
in the universe `uV` with irreducible admissible local components (Library
`CuspidalAllLocalIrreduciblePresentationExistenceStatement` with
`CuspidalSpectralPresentation.exists_small`, module
`Langlands.Automorphic.CuspidalPresentationUniverse`). Listing them as `S i` and putting
`a i := c₀' Y(S i) / X` gives the identity, for the components `μF`, `μE` at `v` of the global
measures; `PiV` is admissible because `Π_w` is and `h` is a homeomorphic isomorphism.

## Provenance

This is derived content: the statement is formulated here from the sources below, none of
which states it in this form. Arthur–Clozel 1989, Chapter 1, §6.3(b), printed p. 57, state the
global identity (6.5), `ℓ trace(Π(φ) I_σ) = Σ trace π'(f)`, for a `σ`-discrete local
representation globalized with a Steinberg component, and read it at one place after collapsing
the sum with III.3.1 ("Consequently, we have an equality at the place `v₃` of the form ...").
Henniart–Lemaire 2011, II.6.6 (printed pp. 122–123), state the comparison
`d Σ_Π tr(Π(φ) ∘ A_Π) = Σ_π tr(π(f))` over function fields; their II.6.16–II.6.17 (printed
pp. 131–132) use it for the descent. The present statement is the identity before the collapse,
for the hypotheses of `CyclicStableCuspidalDescentTraceIdentityStatement`: any cyclic degree,
the two split places `v₁`, `v₂` of the simple trace formulas, and the test functions at `v`
restricted to the (`σ`-)regular sets and to norm determinants.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989 (Library source
`arthur-clozel-1989-base-change`): Chapter 1, Lemmas 2.4–2.5 (printed pp. 13–15), §6.3 (printed
pp. 54–57); Chapter 3, Theorem 3.1 (printed p. 201). Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle*, Mémoires de la SMF 124, 2011:
II.6.2–II.6.6 (printed pp. 118–123), II.6.16–II.6.17 (printed pp. 131–132).
