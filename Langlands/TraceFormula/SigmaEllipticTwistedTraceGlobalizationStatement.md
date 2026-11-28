# A σ-stable cusp with nonzero twisted trace at a σ-elliptic test function (statement)

Module `Langlands.TraceFormula.SigmaEllipticTwistedTraceGlobalizationStatement`, namespace
`Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.SigmaEllipticTwistedTraceGlobalizationStatement.{uF, uE, uR, uW}`.

In words: let `E/F` be a cyclic extension of number fields of degree `l` (any `l ≥ 1`) with
generator `σ`, in which every infinite place of `F` splits completely. Let `v` be a finite place
of `F` with only one place `w` of `E` above it, and let `v₁, v₂, v₃` be three distinct finite
places of `F`, all different from `v`, that split completely in `E`. Let `n = r + 1`, let `χ` be
a unitary character of the centre of `GL_n(F_v ⊗_F E)`, `μ` a Haar measure on `GL_n(F_v ⊗_F E)`
and `φ` a smooth compactly supported function on `GL_n(F_v ⊗_F E)` whose `σ`-orbital integrals
vanish at the `σ`-regular elements that are not `σ`-elliptic. Suppose that some irreducible
admissible representation `τ` with central character `χ` and some isomorphism `A` of `τ` onto
its `σ`-conjugate have `tr(τ(φ) ∘ A) ≠ 0`. Then there is a cuspidal automorphic representation
`Π` of `GL_n(𝔸_E)` with unitary central character, isomorphic to its `σ`-conjugate, whose local
components at all places above `v₁` and above `v₂` are supercuspidal, and whose local component
`Π_w` is irreducible, admissible, has central character `χ` and has `tr(Π_w(φ) ∘ A') ≠ 0` for
some isomorphism `A'` of `Π_w` onto its `σ`-conjugate (`Π_w` read on `GL_n(F_v ⊗_F E)` through
`F_v ⊗_F E ≅ E_w`).

This is the global trace-formula step in the proof of the twisted globalization of a
`σ`-discrete series in Henniart–Lemaire 2011, II.6.16 (printed pp. 131–132), with split
auxiliary places as in Arthur–Clozel 1989, Chapter 1, Lemma 2.5 (printed pp. 13–15) and §6.3
(printed pp. 54–57). It is derived content, formulated for this Library; see "Provenance". The
Library's `Langlands.TraceFormula.sigmaDiscreteTwistedGlobalizationReduction` (module
`Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationReduction`) derives
`Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement` from it, with a twisted
pseudo-coefficient as `φ`.

The module declares five `local instance`s of `AddCommGroup`: on the Library's form spaces
`Langlands.Automorphic.RationalInvariantFunctions`, `ContinuousRationalFunctions`,
`FiniteSmoothRationalFunctions` and `AutomorphicForms`, and on the carrier `A.Space` of a
`LocalRealization`. They are `Submodule.addCommGroup _`, as in the Library's
`Langlands.Automorphic.SupercuspidalComponent`. They are not exported.

## Setting and notation

The global data (`F`, `E`, `σ`, `l`, `IsCyclicAlgebra`, `IsCyclicShiftSplit`, `v`, `w`, `v₁`,
`v₂`, `v₃`, `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`,
`HasUnitaryCentralCharacter`, `IsGaloisStable`, `LocalRealization.IsSupercuspidal`,
`IsIrreducible`, `IsAdmissible`) and the local data at `v` (`F_v := v.adicCompletion F` with the
local field structure of `CompletionPadic.topologicalData v`, `E_v := F_v ⊗[F] E` with its module
topology over `F_v`, `σv := Algebra.TensorProduct.congr AlgEquiv.refl σ`, and the map
`h := (Pi.evalRingHom _ w).comp (finiteTensorMap v).toRingHom : E_v → E_w`, a ring isomorphism
because `w` is the only place above `v`) are those of the Library's
`Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement`, and are written in the Lean
in the same way; its Markdown describes them. In addition:

- `GL_{r+1}(E_v)` carries the topology from `E_v` and the Borel σ-algebra; it is Hausdorff,
  locally compact and totally disconnected (`generalLinear_t2Space_of_finite`,
  `generalLinear_locallyCompactSpace_of_finite`,
  `generalLinear_totallyDisconnectedSpace_of_finite`, module
  `Langlands.Group.GL.LocalFieldTopology`).
- `χ : Subgroup.center (GeneralLinear (r + 1) E_v) →* ℂˣ` with `‖χ z‖ = 1` for all `z`.
- `μ` is a Haar measure on `GL_{r+1}(E_v)` (`μ.IsHaarMeasure`), and
  `φ : SchwartzBruhat (GeneralLinear (r + 1) E_v)` (module `Langlands.HarmonicAnalysis.Basic`)
  is a locally constant compactly supported complex function.
- `SigmaOrbitalIntegralsVanishOffElliptic σv l μ ⇑φ` (module
  `Langlands.BaseChange.EllipticOrbitalIntegral`): for every `σv`-regular `δ` that is not
  `σv`-elliptic, every right Haar measure on the `σv`-centralizer of `δ` and every quotient
  measure compatible with `μ` and it, the `σv`-orbital integral `∫ φ(x⁻¹ δ x^σ) dx` is `0`
  (Henniart–Lemaire II.5.14, Proposition 2 (2), printed p. 115).
- `τ : Representation ℂ (GeneralLinear (r + 1) E_v) W` on `W : Type uR`, with `IsAdmissible τ`,
  `τ.IsIrreducible` and `HasCentralCharacterRep τ χ` (module `Langlands.BaseChange.PseudoCoefficient`:
  `τ z x = χ(z) x` for central `z`).
- `A : SigmaIntertwiner σv (r + 1) τ` (module `Langlands.BaseChange.TwistedCharacter`): an
  isomorphism of `τ` onto `τ ∘ entrywiseAut σv (r + 1)`.
- `twistedDistribution μ τ hτ A.toLinearMap φ` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`): the trace of the finite-rank operator
  `τ(φ) ∘ A`, where `τ(φ) = ∫ φ(g) τ(g) dμ(g)`.
- `PiV := (P.localComponent w.1).representation.comp (Matrix.GeneralLinearGroup.map h)`: the
  component `Π_w` read on `GL_{r+1}(E_v)`.

## Statement

For all `F`, `E`, `σ`, `l`, `v`, `w`, `v₁`, `v₂`, `v₃`, `r` with the hypotheses of
`SigmaDiscreteTwistedGlobalizationStatement` (`IsCyclicAlgebra σ l`; every infinite place of `F`
split by `IsCyclicShiftSplit`; `w` the only place above `v`; `v₁, v₂, v₃` pairwise distinct and
different from `v`; `IsCyclicShiftSplit F E (vᵢ.adicCompletion F) σ l` for `i = 1, 2, 3`), and
for all `χ`, `μ`, `φ`, `W`, `τ`, `hτ`, `A` as above with

- `‖χ z‖ = 1` for every central `z`,
- `SigmaOrbitalIntegralsVanishOffElliptic σv l μ ⇑φ`,
- `τ.IsIrreducible`, `HasCentralCharacterRep τ χ`, and
- `twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0`,

there are `T : CuspidalOperatorRealization E r` and `P : CuspidalSpectralPresentation.{uE, uW} T`
such that

- `ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`;
- `T.isoClass.IsGaloisStable σ`;
- `(P.localComponent w₁.1).IsSupercuspidal` for every `w₁ : FinitePlacesAbove E v₁`, and
  `(P.localComponent w₂.1).IsSupercuspidal` for every `w₂ : FinitePlacesAbove E v₂`;
- `(P.localComponent w.1).IsIrreducible` and `(P.localComponent w.1).IsAdmissible`;
- `HasCentralCharacterRep PiV χ`;
- there are `hP : IsAdmissible PiV` and `A' : SigmaIntertwiner σv (r + 1) PiV` with
  `twistedDistribution μ PiV hP A'.toLinearMap φ ≠ 0`.

The binders appear in the Lean in the order of `SigmaDiscreteTwistedGlobalizationStatement` up
to `r` and the local data at `v`, then `χ`, its unitarity, `μ` with `[μ.IsHaarMeasure]`, `φ`,
the orbital vanishing, `W` with its instances, `τ`, `hτ`, irreducibility, the central
character, `A` and the nonvanishing. The universe `uR` of `W` and the universe `uW` of the local
spaces of `P` are independent.

Remarks on the form.

- **The hypothesis on `τ`.** In the source the function at `v` is a pseudo-coefficient of a
  `σ`-discrete series `Π₀`, and the argument uses that its twisted orbital integral is nonzero
  at some `σ`-elliptic `δ₀` (Henniart–Lemaire II.6.16, printed p. 131: "Puisque Π₀ est
  σ-elliptique (5.14, corollaire 2), il existe un élément δ₀ … tel que Λσ(φ, δ₀) ≠ 0"). The test
  functions of the trace formula with fixed central character are functions modulo the centre:
  `φ` enters through `φ^χ(x) = ∫_{Z(E_v)} φ(zx) χ(z) dz`, and the relevant orbital integrals are
  those of `φ^χ`. A nonzero `σ`-orbital integral of the compactly supported `φ` at a `σ`-elliptic
  element does not give one of `φ^χ`: for `z₀` central with `χ(z₀) = 1`, the function
  `φ₀ − φ₀(z₀⁻¹ ·)` has `(φ₀ − φ₀(z₀⁻¹ ·))^χ = 0`, although its `σ`-orbital integrals need not
  vanish. The hypothesis `tr(τ(φ) ∘ A) ≠ 0` for some `τ` with central character `χ` is instead
  `tr(τ(φ^χ) ∘ A) ≠ 0`, and by the twisted Weyl integration formula with central character
  (Henniart–Lemaire II.2.10, formula (1), printed p. 72, and II.2.6–II.2.7, printed pp. 66–67) it
  gives a `σ`-elliptic `δ₀` at which the orbital integral of `φ^χ` is nonzero, because those of
  `φ^χ` vanish off the `σ`-elliptic set with those of `φ`. For a twisted pseudo-coefficient of a
  `σ`-discrete series `ρ` with central character `χ`, the hypothesis holds with `τ = ρ`, whose
  twisted trace is `1`.
- **Central character at `w`.** The cusp is produced with central character `χ` at `w`, because
  the comparison with `ρ` that follows uses a pseudo-coefficient, which separates `ρ` only from
  the representations with the same central character (Henniart–Lemaire II.5.13, Définition,
  printed p. 113; the Library's `Langlands.BaseChange.IsTwistedPseudoCoefficient`).
- **Three split places.** As in `SigmaDiscreteTwistedGlobalizationStatement`: `v₁` and `v₂` carry
  coefficients of supercuspidal representations (Arthur–Clozel, condition (3′), printed p. 14),
  and `v₃` carries supports with regular elliptic images in `PGL_n` (condition (4′)) and the
  restriction that isolates one term of the geometric side.
- **What is not claimed.** Nothing is said about `Π` at `v₃` or at the other places, about the
  normalization of `A'`, or about uniqueness of `Π`.

## Why the statement is true

The argument is steps 1 and 3–6 of the sketch in the Markdown of
`SigmaDiscreteTwistedGlobalizationStatement` ("Why the statement is true"), with the given `φ`
in place of the pseudo-coefficient of step 2 there; it is that of Henniart–Lemaire II.6.16
(printed pp. 131–132) up to the existence of the cusp `Π'`.

1. **The central character.** `χ` is `σv`-invariant, since `τ ≅ τ ∘ σv` and `τ ≠ 0`. By
   Hilbert's Theorem 90 for `E_w/F_v` it factors through the norm, and it is extended to a
   `σ`-invariant unitary character `χ_𝔸 = ω ∘ N_{𝔸_E/𝔸_F}` of `𝔸_E^×/E^×` with `χ_{𝔸,w} = χ`
   (transported through `h`) and with prescribed components at `v₁` and `v₂`, as in step 1 of
   that sketch (Henniart–Lemaire II.6.15–II.6.16, printed p. 131).
2. **The function at `v`.** Put `φ_v := φ^χ`. Its twisted trace on a representation with central
   character `χ` is the twisted trace of `φ` (with compatible measures). Its `σ`-orbital
   integral at `δ` is, up to a positive constant, the integral over
   `Z(E_v)/{a⁻¹σ(a) : a ∈ Z(E_v)}` of `χ(z)` times the `σ`-orbital integral of `φ` at `zδ`
   (for central `a`, `a⁻¹σ(a)g⁻¹δσ(g) = (ga)⁻¹δσ(ga)`, and the group of the `a⁻¹σ(a)`, the
   image of `Z(E_v)/Z(F_v)`, is compact because `E_v` is a field); since `zδ` is `σ`-regular, respectively `σ`-elliptic, exactly when `δ` is,
   they vanish off the `σ`-elliptic set. By the
   twisted Weyl integration formula and `tr(τ(φ_v) ∘ A) ≠ 0`, some `σ`-elliptic `δ₀` has
   `Φ(φ_v, δ₀) ≠ 0`, and by local constancy of twisted orbital integrals on the `σ`-regular set
   (Arthur–Clozel, Chapter 1, printed p. 17) the same holds on an open neighbourhood of `δ₀`.
3. **Split places, the global element, isolation, and the simple twisted trace formula.** These
   are steps 3–6 of that sketch (Arthur–Clozel, Chapter 1, Lemma 2.5 and the proof of
   Proposition 2.7, printed pp. 13–17; Henniart–Lemaire II.6.4, II.6.8–II.6.9 and II.6.16,
   printed pp. 120–125 and 131–132). The geometric side of the simple twisted trace formula with
   central character `χ_𝔸` reduces to the nonzero term of one global element, so there is a
   `σ`-stable cuspidal `Π'` with central character `χ_𝔸` and `tr(Π'_u(φ_u) ∘ A_{Π'_u}) ≠ 0` at
   every place `u` (Henniart–Lemaire II.6.16, printed p. 132: "il existe une représentation
   automorphe cuspidale σ-stable Π′ … telle que tr(Π′(φ) ∘ A_{Π′}) ≠ 0"). The coefficients at
   `v₁` and `v₂` make the components of `Π'` above them supercuspidal.
4. **The component at `w`.** `Π'_w` is irreducible and admissible, `σ`-stable (`σ` fixes the
   only place `w` above `v`), has central character `χ_{𝔸,w} = χ`, and
   `tr(Π'_w(φ) ∘ A_{Π'_w}) = tr(Π'_w(φ_v) ∘ A_{Π'_w}) ≠ 0`. A presentation `P` of `Π'` with local
   spaces in the universe `uW` and irreducible admissible components exists by the Library's
   `Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentationExistenceStatement` and the
   universe change of the module `Langlands.Automorphic.CuspidalPresentationUniverse`.

The argument uses neither the descent of `σ`-discrete series nor the local Langlands
correspondence.

## Provenance

This is derived content, formulated for this Library. It is the part of the proof of
Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en caractéristique
non nulle*, Mém. SMF 124 (2011), II.6.16 (printed pp. 131–132), that produces, from a function
`φ_{v₀}` at `v₀` with a nonzero twisted orbital integral at a `σ`-elliptic element, a `σ`-stable
cuspidal `Π'` with `tr(Π'_{v₀}(φ_{v₀}) ∘ A_{Π'_{v₀}}) ≠ 0`; the last sentences there ("Enfin,
puisque … d'après la formule d'intégration de Weyl tordue (2.10, formule (1)), Π′_{v₀} est
σ-elliptique. Comme d'autre part Π′_{v₀} est générique et unitaire, elle est σ-discrète
(5.15, proposition 1), donc isomorphe à Π₀", printed p. 132) are not part of this statement.
The split auxiliary places follow Arthur–Clozel, *Simple algebras, base change, and the
advanced theory of the trace formula*, Annals of Mathematics Studies 120 (1989), Chapter 1,
Lemmas 2.4–2.6 (printed pp. 13–15), the proof of Proposition 2.7 (printed pp. 16–17) and §6.3 (b)
(printed pp. 56–57). The PDF page is the printed page plus 8 for Henniart–Lemaire and plus 14
for Arthur–Clozel.

Differences from the sources, none of which changes the content of the argument: the function
at `v` is any function with `σ`-orbital integrals vanishing off the `σ`-elliptic set and nonzero
twisted trace on some representation with central character `χ`, rather than a
pseudo-coefficient; it is compactly supported, and its average `φ^χ` over the centre is the
function of the trace formula with fixed central character; the auxiliary places are split as in
Arthur–Clozel; and the degree `l` is arbitrary.
