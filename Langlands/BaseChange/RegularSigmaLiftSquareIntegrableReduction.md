# Square-integrability of a regular σ-descent from σ-elliptic nonvanishing

The module `Langlands.BaseChange.RegularSigmaLiftSquareIntegrableReduction` states and proves
that the σ-elliptic nonvanishing of twisted traces of σ-discrete series implies the
square-integrability of every generic unitarizable regular σ-descent of a σ-discrete series.

## Statement

`RegularSigmaLiftSquareIntegrableFromEllipticNonvanishingStatement.{u, v, uV, uW}` is the
implication

`SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW} → RegularSigmaLiftSquareIntegrableStatement.{u, v, uV, uW}`.

The universes are those of the base field `F` (`u`), of the extension field `E` (`v`), of the
space `W` of the σ-discrete series (`uW`), and of the space `V` of the representation of
`GL_{r+1}(F)` (`uV`, only in the conclusion). Both propositions are in the Library:

- `SigmaDiscreteEllipticNonvanishingStatement` (module
  `Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingStatement`): for a nonarchimedean
  local field `F` of characteristic zero, a field `E` that is a cyclic `F`-algebra of group
  `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`, every σ-discrete series `τ` of
  `GL_{r+1}(E)` (`IsSigmaDiscreteSeries σ (r + 1) τ`), every σ-intertwiner `A` and every Haar
  measure `μ` on `GL_{r+1}(E)` admit a Schwartz–Bruhat function `φ` supported in the
  σ-elliptic set with `tr(τ(φ) ∘ A) ≠ 0`.
- `RegularSigmaLiftSquareIntegrableStatement` (module
  `Langlands.BaseChange.RegularSigmaLiftSquareIntegrableStatement`): with the same `F`, `E`,
  `σ`, `l`, `r`, let `ρ` be a σ-discrete series of `GL_{r+1}(E)`, `A` a σ-intertwiner of `ρ`, and
  `π` an admissible representation of `GL_{r+1}(F)` that is generic for a unitary additive
  character `ψ` of `F` (`Whittaker.IsGeneric ψ r π`, which includes irreducibility) and
  unitarizable (`IsUnitarizable π`). If `IsRegularSigmaLift σ l π hπ ρ hρ A c` holds for some
  `c : ℂ`, then `JacquetLanglands.IsSquareIntegrable π`.

`IsRegularSigmaLift` (module `Langlands.BaseChange.SigmaDiscreteRegularDescentStatement`)
asserts `c ≠ 0` and `tr(ρ(φ) ∘ A) = c · tr π(f)` for all Borel Haar measures and all concordant
Schwartz–Bruhat functions `φ` on `GL_{r+1}(E)` and `f` on `GL_{r+1}(F)` with `φ` supported in
the σ-regular set, `f` supported in the regular semisimple set, and `det g ∈ N_{E/F}(E^×)`
whenever `f(g) ≠ 0`.

The theorem `regularSigmaLiftSquareIntegrableFromEllipticNonvanishing` proves the implication
at all four universe parameters.

## Proof

Fix the data of `RegularSigmaLiftSquareIntegrableStatement`, the Borel σ-algebras on
`GL_{r+1}(F)` and `GL_{r+1}(E)` and the Haar measures `μF = Measure.haar` and
`μE = Measure.haar` on them.

1. *A σ-elliptic test function.* The premise, applied to `ρ`, `A` and `μE`, gives a
   Schwartz–Bruhat function `φ` on `GL_{r+1}(E)` supported in the σ-elliptic set with
   `tr(ρ(φ) ∘ A) ≠ 0`.
2. *Elliptic transfer and the norm cut.* The Library theorem `ellipticTransfer` (module
   `Langlands.BaseChange.EllipticTransfer`, the elliptic form of Henniart–Lemaire I.2.5) gives a
   Schwartz–Bruhat function `f` on `GL_{r+1}(F)` supported in the regular elliptic set and
   concordant with `φ` for `μF` and `μE`. Let `N ⊆ F^×` be the image of the norm
   `Units.map (Algebra.norm F)` on `E^×`; it is clopen (`isClopen_normUnitsRange`, module
   `Langlands.BaseChange.SigmaLiftCharacterIdentity.NormDeterminantCutoff`, using that `E` has
   positive dimension `l` over `F`). Put `f_N = cutoff (hN.preimage hdet) f`, the product of `f`
   with the indicator of `{g | det g ∈ N}` (`ConcordanceLocalization.cutoff`). The determinant
   is continuous and conjugation invariant. Each `γ` associated with some `δ` has
   `det γ = N_{E/F}(det δ) ∈ N` (`IsNormAssociated.norm_determinant_units_eq`, module
   `Langlands.BaseChange.CyclicAlgebraDeterminant`). So `concordant_cutoff_ordinary` shows that
   `φ` and `f_N` are still concordant. By `support_cutoff`, the support of `f_N` is the part of
   the support of `f` with norm determinant. Hence `f_N` is supported in the regular elliptic
   set, so in the regular semisimple set, and `det g ∈ N` whenever `f_N(g) ≠ 0`.
3. *Nonzero trace of `π`.* `φ` is σ-regularly supported
   (`IsSigmaEllipticSupported.isSigmaRegularSupported`). The identity of `IsRegularSigmaLift`
   applies to `μF`, `μE`, `φ` and `f_N` and gives `tr(ρ(φ) ∘ A) = c · tr π(f_N)`. The left side
   is nonzero, so `tr π(f_N) ≠ 0`.
4. *Essential square-integrability.* Suppose that `π` is not essentially square-integrable.
   The characteristic-zero field `F` is presented as a `p`-adic field by
   `CharZeroLocalField.padicField F` with topological data `CharZeroLocalField.topologicalData F`
   (module `Langlands.LocalField.CharZeroPadicRealization`), with the same carrier, topology
   and valuation. By `isEssentiallySquareIntegrable_iff_padic` (module
   `Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison`) the two notions of essential
   square-integrability agree. The Library theorem `padicGenericEllipticCharacterVanishing`
   (module `Langlands.Representation.Classification.GenericEllipticCharacter`) then gives the
   local character value `0` of `π` at every regular elliptic element. Since `f_N` is
   supported in the regular elliptic set, `distribution_eq_zero_of_localValues_zero` (module
   `Langlands.BaseChange.CommonShintaniLiftTrace`) gives `tr π(f_N) = 0`, a contradiction. So
   `π` is essentially square-integrable.
5. *Square-integrability.* `π` is irreducible (part of `Whittaker.IsGeneric`) and unitarizable.
   `IsEssentiallySquareIntegrable.isSquareIntegrable_of_isUnitarizable` (module
   `Langlands.JacquetLanglands.UnitarizableEssentiallySquareIntegrable`, with `n = r + 1 > 0`)
   gives `JacquetLanglands.IsSquareIntegrable π`.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011). In the proof of the Lemma of II.4.8, printed
  p. 91, the twisted character of the lift `Π` does not vanish identically on the σ-elliptic
  set. A generic `π′` lifting to `Π` has a unitary central character, so it is essentially
  discrete only if it is a discrete series. If it is not a discrete series, it is a proper
  parabolic induction, so by II.4.5 (printed pp. 86–88) its character vanishes on the elliptic
  set. The lift identity then makes the twisted character of `Π` vanish on the σ-elliptic set,
  a contradiction. Steps 3–5 are this argument on test functions; the elliptic set is reached
  through the regular test functions with norm determinants of `IsRegularSigmaLift` (steps
  2–3). Regular transfer is I.2.5, printed p. 18.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Mathematics Studies 120 (1989), Chapter 1. Lemma 2.12 (i), printed p. 19,
  states that the twisted character of a σ-discrete `Π` does not vanish identically on the
  σ-elliptic set; the premise of the implication is its test-function form. Lemma 2.11,
  printed pp. 18–19, deduces from nonvanishing on the elliptic set that a generic
  representation is discrete up to a character twist, by Zelevinsky's classification and the
  vanishing of properly induced characters on the elliptic set. Step 4 is its case of the
  identity automorphism, which the Library proves as `padicGenericEllipticCharacterVanishing`.
