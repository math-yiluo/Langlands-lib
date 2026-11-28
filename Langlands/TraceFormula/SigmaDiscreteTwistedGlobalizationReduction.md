# The twisted globalization of a σ-discrete series: a reduction

The module `Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationReduction` proves that
`Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement` follows from a global
trace-formula statement and two local statements on `σ`-discrete series. It follows the end of
the proof in Henniart–Lemaire 2011, II.6.16 (printed pp. 131–132), and Arthur–Clozel 1989,
Chapter 1, §6.3 (b) (printed pp. 56–57): the function at `v` is a twisted pseudo-coefficient of
the given `σ`-discrete series `ρ`, the global step produces a cusp whose component at `w` has
nonzero twisted trace at it, that component is `σ`-discrete, and the pseudo-coefficient then
forces it to be isomorphic to `ρ`.

## Statement

`SigmaDiscreteTwistedGlobalizationReductionStatement.{uF, uE, uR, uW}` is the implication

`SigmaEllipticTwistedTraceGlobalizationStatement.{uF, uE, uR, uW} →
TwistedCuspidalPseudoCoefficientExistenceStatement.{uF, max uF uE, uR} →
GenericSigmaEllipticDiscreteStatement.{uF, max uF uE, uE} →
SigmaDiscreteTwistedGlobalizationStatement.{uF, uE, uR, uW}`.

The universes of the two local statements are those at which they are applied: the local field
`F_v` lies in `Type uF`, the algebra `F_v ⊗_F E` in `Type (max uF uE)`, the representation `ρ`
on a space in `Type uR`, and the local component at `w` of a spectral presentation of a cusp
over `E` on a space in `Type uE`. The four propositions are in the Library:

- `Langlands.TraceFormula.SigmaEllipticTwistedTraceGlobalizationStatement` (module
  `Langlands.TraceFormula.SigmaEllipticTwistedTraceGlobalizationStatement`): in the global
  setting of the target, for a unitary character `χ` of the centre of `GL_{r+1}(F_v ⊗_F E)`, a
  Haar measure `μ` and a Schwartz–Bruhat function `φ` whose `σv`-orbital integrals vanish off
  the `σv`-elliptic set, if some irreducible admissible `τ` (space in `Type uR`) with central
  character `χ` and some `A : τ ≅ τ^{σv}` have `tr(τ(φ) ∘ A) ≠ 0`, then there is a `σ`-stable
  cusp `T` with unitary central character and a presentation `P` (local spaces in `Type uW`),
  supercuspidal above `v₁` and `v₂`, whose component `Π_w` is irreducible and admissible and,
  read on `GL_{r+1}(F_v ⊗_F E)`, has central character `χ` and nonzero twisted trace at `φ` for
  some isomorphism onto its `σv`-conjugate.
- `Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement` (module of the same
  name): a `σ`-discrete series `τ` of `GL_n(E)`, for a cyclic field extension `E/F` of
  nonarchimedean local fields of characteristic zero, with central character `χ`, an
  isomorphism `A : τ ≅ τ^σ` and a Haar measure `μ`, has a twisted pseudo-coefficient
  (`IsTwistedPseudoCoefficient`: twisted trace `1` at `(τ, A)` and `0` at every irreducible
  admissible tempered `τ'` on a space in the universe of `τ`, with central character `χ`, not
  isomorphic to `τ`, for every `A'`) whose `σ`-orbital integrals vanish off the `σ`-elliptic
  set (Henniart–Lemaire II.5.13–II.5.14).
- `Langlands.BaseChange.GenericSigmaEllipticDiscreteStatement` (module of the same name): in
  the same local setting, a generic admissible `τ` with unitary central character, an
  isomorphism `A : τ ≅ τ^σ`, and a test function with `σ`-orbital integrals vanishing off the
  `σ`-elliptic set and `tr(τ(φ) ∘ A) ≠ 0`, make `τ` a `σ`-discrete series (Henniart–Lemaire
  II.5.8 and II.5.15, Proposition 1).
- `Langlands.TraceFormula.SigmaDiscreteTwistedGlobalizationStatement` (module of the same name):
  the target; a `σ`-discrete series `ρ` of `GL_{r+1}(F_v ⊗_F E)` is isomorphic to the component
  at `w` of a `σ`-stable unitary cusp supercuspidal above `v₁` and `v₂`.

The theorem `sigmaDiscreteTwistedGlobalizationReduction` proves the implication.

## Auxiliary results

- `tensorCongrHom : (E ≃ₐ[F] E) →* (K ⊗[F] E ≃ₐ[K] K ⊗[F] E)`, `τ ↦ id ⊗ τ`
  (`Algebra.TensorProduct.congr AlgEquiv.refl τ`), for fields `F`, `E`, `K` with `E` and `K`
  algebras over `F`; and `tensorCongrHom_injective`: it is injective, by evaluating at
  `1 ⊗ y` and using the injectivity of `E → K ⊗[F] E`
  (`Algebra.TensorProduct.includeRight_injective`).
- `isCyclicAlgebra_tensorCongr`: if `IsCyclicAlgebra σ l` and `E/F` is separable, then
  `IsCyclicAlgebra (id ⊗ σ) l` for the `K`-algebra `K ⊗[F] E`. Finiteness is base change; the
  rank is `Module.finrank_baseChange`; reducedness follows from formal unramifiedness of the
  separable extension `E/F` (`Algebra.FormallyUnramified.isReduced_of_field`); the order of
  `id ⊗ σ` is that of `σ` by injectivity of `tensorCongrHom`; and the fixed elements are those
  of `K`: the sequence `0 → F → E → E` with second map `σ − id` is exact because the fixed field
  of `σ` is `F`, and stays exact after `K ⊗[F] -` because `K` is flat over `F`
  (`Module.Flat.lTensor_exact`).
- `isGeneric_of_ringEquiv`: for commutative topological rings `R`, `S`, a bicontinuous ring
  isomorphism `e : R ≃+* S`, a representation `π` of `GL_{r+1}(S)` generic for a unitary
  additive character `ψ` (`Whittaker.IsGeneric`), the representation `π'` of `GL_{r+1}(R)` with
  `π' g = π (generalLinearRingEquiv e g)` is generic for `ψ ∘ e`
  (`UnitaryAdditiveCharacter.comapSurjective`). Irreducibility and admissibility are carried by
  `isIrreducible_comp_continuousMulEquiv_iff` and `isAdmissible_comp_continuousMulEquiv_iff`;
  the entrywise map sends the upper unipotent subgroup of `GL_{r+1}(R)` onto that of
  `GL_{r+1}(S)` (the private lemma `generalLinearRingEquiv_mem_upperUnipotent_iff`) and pulls
  the standard character for `ψ` back to the standard character for `ψ ∘ e`, so
  `Whittaker.functionals_comp` identifies the Whittaker functionals.
- `IsTemperedRep.nonempty_unitaryCentralCharacter`: a tempered representation (`IsTemperedRep`,
  module `Langlands.BaseChange.PseudoCoefficient`) of a locally compact group has a unitary
  central character (`UnitaryCentralCharacter`); temperedness for a Haar measure on the
  central quotient includes one.
- `fieldOfIsField`: the `Field` structure on a commutative ring `R` with `IsField R` whose
  underlying commutative ring is the given instance (`fieldOfIsField_toCommRing`, by `rfl` at
  reducible transparency), unlike `IsField.toField`, which starts from the ring structure only.
  It makes `F_v ⊗_F E` a field without changing its ring structure, so that the local statements
  apply to the ring in which the target and the global statement are written.

## Proof of the implication

Fix the data of the target and a `σv`-discrete series `ρ` of `GL_{r+1}(E_v)`,
`E_v := F_v ⊗_F E`, on `W : Type uR`.

1. **The local setting.** `tensorUniqueCompletion v w hw : E_v ≃ₐ[F_v] E_w` (module
   `Langlands.BaseChange.CyclicGlobalizationPlaceComparison`) shows that `E_v` is a field, and
   `fieldOfIsField` gives it a field structure over its ring structure. `F_v` is a
   nonarchimedean local field (`CompletionPadic.topologicalData v`) of characteristic zero
   (`algebraMap F F_v` is injective). `E/F` is separable (characteristic zero), so
   `isCyclicAlgebra_tensorCongr` gives `IsCyclicAlgebra σv l`. `GL_{r+1}(E_v)` carries the
   Borel σ-algebra.
2. **The pseudo-coefficient.** From `IsSigmaDiscreteSeries σv (r + 1) ρ`, `ρ` is admissible,
   irreducible and tempered, with an isomorphism `A : ρ ≅ ρ^{σv}`. By
   `IsTemperedRep.nonempty_unitaryCentralCharacter`, `ρ` has a unitary central character `χ`.
   Let `μ` be the Haar measure `Measure.haarMeasure` of some compact set with nonempty interior.
   `TwistedCuspidalPseudoCoefficientExistenceStatement` at `(F_v, E_v, σv, l, r + 1, ρ, χ, A, μ)`
   gives `φ` with `IsTwistedPseudoCoefficient μ _ χ ρ _ A φ` and
   `SigmaOrbitalIntegralsVanishOffElliptic σv l μ ⇑φ`.
3. **The global step.** `SigmaEllipticTwistedTraceGlobalizationStatement` at `χ`, `μ`, `φ` and
   `τ := ρ`, with `tr(ρ(φ) ∘ A) = 1 ≠ 0`, gives `T` and `P` with the first four conclusions of
   the target, and, for `PiV` the component `Π_w` read on `GL_{r+1}(E_v)`, central character `χ`,
   admissibility, and `A' : PiV ≅ PiV^{σv}` with `tr(PiV(φ) ∘ A') ≠ 0`.
4. **`PiV` is a `σv`-discrete series.** `CuspidalSpectralPresentation.exists_generic_at_completion`
   (module `Langlands.Automorphic.CuspidalUnitaryLocalGenericity`) makes `Π_w` generic for some
   unitary additive character of `E_w`, as `T` has unitary central character and `Π_w` is
   irreducible and admissible. `tensorUniqueCompletion_bicontinuous` and
   `isGeneric_of_ringEquiv` carry genericity to `PiV`. `GenericSigmaEllipticDiscreteStatement`
   at `(F_v, E_v, σv, l, r, PiV, χ, A', μ, φ)` makes `PiV` a `σv`-discrete series; in particular
   it is irreducible and tempered.
5. **`PiV ≅ ρ`.** The space of `Π_w` is in `Type uE`, while the pseudo-coefficient separates `ρ`
   only from representations on spaces in `Type uR`. `exists_small_finiteLocalFactor` (module
   `Langlands.Automorphic.CuspidalPresentationUniverse`) gives a smooth irreducible
   representation `σ'` of `GL_{r+1}(E_w)` on a space in `Type uR` isomorphic to `Π_w`; let `τ'`
   be `σ'` read on `GL_{r+1}(E_v)`, so that `fτ : PiV ≅ τ'`. Suppose `PiV ≇ ρ`. Then `τ' ≇ ρ`, and
   `τ'` is admissible (`isAdmissible_of_equiv`), irreducible (`isIrreducible_iff_of_equiv`),
   tempered (`isTemperedRep_iff_of_equiv`) with central character `χ`
   (`HasCentralCharacterRep.of_equiv`). The separation property of `φ` gives
   `tr(τ'(φ) ∘ A'') = 0` for `A'' := A'.transport fτ` (`SigmaIntertwiner.transport`, module
   `Langlands.BaseChange.SigmaLiftTransport`). By `twistedDistribution_eq_of_equivalent` (same
   module) this trace equals `tr(PiV(φ) ∘ A') ≠ 0`, a contradiction. Hence
   `Nonempty (Representation.Equiv PiV ρ)`.

The proof uses `set_option maxHeartbeats 1600000` for the elaboration of the instances on
`F_v ⊗_F E`.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), II.6.16 (printed pp. 131–132): with a
  pseudo-coefficient `φ_{v₀}` of `(Π₀, I_σ(Π₀))` at `v₀`, the simple twisted trace formula gives
  a `σ`-stable cuspidal `Π′` with `tr(Π′_{v₀}(φ_{v₀}) ∘ A_{Π′_{v₀}}) ≠ 0`; "d'après la formule
  d'intégration de Weyl tordue (2.10, formule (1)), Π′_{v₀} est σ-elliptique. Comme d'autre part
  Π′_{v₀} est générique et unitaire, elle est σ-discrète (5.15, proposition 1), donc isomorphe à
  Π₀" (printed p. 132). Twisted pseudo-coefficients: II.5.13, Définition and Proposition
  (printed p. 113), and II.5.14, Proposition 2 (printed p. 115). The PDF page is the printed page
  plus 8. In the Lean proof, the step "σ-elliptic, generic and unitary, hence σ-discrete" is the
  statement `GenericSigmaEllipticDiscreteStatement`, applied directly to the test function `φ`,
  and "donc isomorphe à Π₀" is the separation property of the pseudo-coefficient.
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989), Chapter 1, §6.3 (b) (printed pp. 56–57), the same
  argument with split auxiliary places, and Lemma 2.11 (printed pp. 18–19). The PDF page is the
  printed page plus 14.
