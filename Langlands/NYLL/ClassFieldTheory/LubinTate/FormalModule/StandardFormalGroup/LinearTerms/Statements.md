# NYLL M354.001–M354.007: linear-term coefficient and substitution targets

This module states the seven theorems that open the linear-term section of the
NYLL standard formal-group module. It contains reducible proposition
definitions only; it proves none of them.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean),
lines 28–188 (the section header at lines 28–47 and the seven theorems at
lines 51–188). The readable copy is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`;
its SHA-256 is
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, folder
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution and verification
supplement is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL entry exists in `notes/errata/`, and no patch10 feasibility edit
affects this source module.

The Lean file keeps the original 2026 copyright, Apache-2.0 and author header
verbatim and adds a modification notice by Worker 497. The existing
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) apply
unchanged.

## Imported definitions

The targets reuse the published definitions of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`
(NYLL M347.001 and M347.003):

- `Langlands.NYLL.LubinTate.SameUniformizer.linearForm L` is
  `∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`;
- `Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm H L` is
  `(2 : ℕ∞) ≤ (H - linearForm L).order`, Mathlib's total order of a
  multivariable power series.

`MvPowerSeries.coeff d`, `MvPowerSeries.C`, `MvPowerSeries.X`,
`Finsupp.degree` (the sum of the exponents of a multi-index) and
`MvPowerSeries.subst` (multivariable substitution of a family
`G : σ → MvPowerSeries τ R` into a series in the variables `σ`) are Mathlib's.

## Parameters common to all targets

Every target keeps the source section variables (lines 45–47):
an arbitrary implicit coefficient ring `{R : Type*} [CommRing R]`, an implicit
finite variable type `{σ : Type w} [Fintype σ]`, and, only in the two targets
that use it (M354.003 and M354.004), a second implicit finite variable type
`{τ : Type w'} [Fintype τ]`. The universes of `R`, `σ` and `τ` are
independent; `w` and `w'` are declared as in the source (line 33) and `R`
keeps the automatically bound universe of `Type*`. There is no local-field,
uniformizer, field, characteristic, nontriviality or nonempty-variable
hypothesis; the source's `K`, `F` and `π` section variables (lines 40–41) are
not used by these seven theorems and do not appear. As in the source (line
31), the file installs `Classical.propDecidable` as a local instance, so the
equalities `j = i` in M354.005 and M354.006 are decided classically.

## Exact targets

Names in the first block are relative to
`Langlands.NYLL.LubinTate.SameUniformizer`; names in the second block are
relative to `Langlands.NYLL.PortInternal.M354`.

| Unit, source declaration and lines | Target | Proposition |
| --- | --- | --- |
| M354.001, `HasLinearTerm.coeff_eq_linearForm`, lines 51–64 (signature 53–58) | `HasLinearTerm.coeff_eq_linearFormStatement {H : MvPowerSeries σ R} {L : σ → R} (hH : HasLinearTerm H L) (d : σ →₀ ℕ) (hd : d.degree < 2)` | `MvPowerSeries.coeff d H = MvPowerSeries.coeff d (linearForm L)` |
| M354.002, `HasLinearTerm.coeff_single`, lines 66–74 (signature 67–70) | `HasLinearTerm.coeff_singleStatement {H : MvPowerSeries σ R} {L : σ → R} (hH : HasLinearTerm H L) (i : σ)` | `MvPowerSeries.coeff (Finsupp.single i 1) H = L i` |
| M354.004, `HasLinearTerm.subst`, lines 88–167 (signature 90–96) | `HasLinearTerm.substStatement {H : MvPowerSeries σ R} {L : σ → R} (hH : HasLinearTerm H L) {G : σ → MvPowerSeries τ R} {M : σ → τ → R} (hG : ∀ i, HasLinearTerm (G i) (M i))` | `HasLinearTerm (MvPowerSeries.subst G H) (fun j => ∑ i, L i * M i j)` |
| M354.006, `hasLinearTerm_X`, lines 178–183 (signature 179–181) | `hasLinearTerm_XStatement (i : σ)` | `HasLinearTerm (MvPowerSeries.X i : MvPowerSeries σ R) (fun j => if j = i then (1 : R) else 0)` |
| M354.007, `hasLinearTerm_zero`, lines 185–188 (signature 186–187) | `hasLinearTerm_zeroStatement` | `HasLinearTerm (0 : MvPowerSeries σ R) (fun _ => 0)` |
| M354.003, private `HasLinearTerm.linearForm_weighted_sum`, lines 76–86 (signature 76–79) | `d003Statement (L : σ → R) (M : σ → τ → R)` | `(∑ i, MvPowerSeries.C (L i) * linearForm (M i)) = linearForm (fun j => ∑ i, L i * M i j)` |
| M354.005, private `linearForm_basis`, lines 171–176 (signature 171–174) | `d005Statement (i : σ)` | `linearForm (R := R) (fun j : σ => if j = i then (1 : R) else 0) = (MvPowerSeries.X i : MvPowerSeries σ R)` |

In words: (M354.001) in total degree below two, a series with prescribed
linear term `L` has the same coefficients as `∑ i, L i X_i`; (M354.002) the
coefficient of `X_i` in such a series is `L i`; (M354.003) for a vector `L`
and a matrix `M`, `∑ i, L i · (∑ j, M i j X_j)` is the linear form with
coefficients `j ↦ ∑ i, L i M i j`; (M354.004) if `H` has linear term `L` and
each `G i` has linear term `M i`, then `H(G)` has linear term `L M`;
(M354.005) the linear form of the `i`-th standard basis vector is `X_i`;
(M354.006) `X_i` has that standard-basis linear term; (M354.007) the zero
series has the zero linear term.

Every explicit/implicit binder and its order are those of the source theorem,
and every equality keeps its source orientation. The hypotheses `hH`, `hd`
and `hG` remain explicit arguments of the targets even though the target
propositions do not mention their proofs, so the later theorems have exactly
the source telescopes. In M354.005 the coefficient type is implicit and is
fixed by `(R := R)`, as in the source. The two private source theorems receive
the fresh names `d003Statement` and `d005Statement` in the
`Langlands.NYLL.PortInternal.M354` namespace reserved by the public port
inventory; these are implementation names, not the original private kernel
names. The universe and binder telescopes above were confirmed by printing
the elaborated declarations in the approved environment.

## Adaptations

The following are all modifications to the selected source declarations and
their surrounding interface:

- Extract only the seven theorem signatures of source lines 53–188 into this
  focused statement module; omit their proofs and the rest of the source
  module.
- Prefix the source namespace `LubinTate.SameUniformizer` by `Langlands.NYLL`
  and append `Statement` to each public source theorem name; place the two
  private theorems under `Langlands.NYLL.PortInternal.M354` as `d003Statement`
  and `d005Statement`, opening `Langlands.NYLL.LubinTate.SameUniformizer` there
  to refer to `linearForm`.
- Replace each theorem and its proof by a reducible `abbrev` returning `Prop`,
  with the source parameters as arguments and the source conclusion as body.
  Reducibility lets the later theorems be used by `rw`, `simp` and dot
  notation (for example `hH.coeff_eq_linearForm d hd`) as the source proofs
  use them.
- Disable the unused-variable linter only on the three targets whose
  hypotheses are not mentioned by their conclusions (M354.001, M354.002,
  M354.004), keeping the source hypothesis names.
- Declare only the universes `w` and `w'` used by these signatures instead of
  the source's `u v w w'`, and omit the unused section variables `K`, `F`
  and `π` (lines 40–41) and the `open LocalFieldTheory.DiscreteValuationField`
  (line 38).
- Import the published focused definition module and
  `Mathlib.RingTheory.MvPowerSeries.Substitution` instead of the source's
  `RecursiveIntertwiner`, `StandardSeries` and
  `Mathlib.RingTheory.FormalGroup.Basic` imports; the statements need only
  the linear-term definitions, coefficients, degrees and multivariable
  substitution. Remove the source's `noncomputable section`.
- Order the declarations by namespace (the five public targets, then the two
  private ones) and replace the module and theorem docstrings with
  statement-specific documentation and this adaptation record.

## Proof boundary

This module makes no proof claim. The source proofs use, respectively,
`MvPowerSeries.coeff_of_lt_order` (M354.001); M354.001 at
`Finsupp.single i 1` and simplification of `linearForm` with
`MvPowerSeries.coeff_index_single_X` (M354.002); coefficient extensionality and
`Finset.sum_comm` (M354.003); M347.004 `HasLinearTerm.constantCoeff_eq_zero`,
`MvPowerSeries.hasSubst_of_constantCoeff_zero`,
`MvPowerSeries.one_le_order_iff_constCoeff_eq_zero`,
`MvPowerSeries.le_order_subst`, M354.003, `MvPowerSeries.nat_le_order` and
`MvPowerSeries.min_order_le_add` (M354.004); simplification (M354.005,
M354.007); and M354.005 with `MvPowerSeries.order_zero` (M354.006). Each exact
theorem, with its adapted source name, is to be proved by a focused
`lean.proof@1` task after this module is published; M354.004 gets its own
proof task.

## Development verification

The module compiled without warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against the published linear-term
definitions, and inspection of `HasLinearTerm.substStatement` reported
`statement_returns_prop: true`. A private, unsubmitted adaptation of the
source proofs typechecked all seven targets, showing the targets are not
vacuous mismatches. Development checks do not establish independent semantic
acceptance or prove any target.
