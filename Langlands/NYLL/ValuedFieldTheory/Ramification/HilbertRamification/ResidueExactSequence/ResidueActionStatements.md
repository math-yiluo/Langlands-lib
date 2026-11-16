# Residue action: compatibility, surjectivity and normality targets

The module states three closed propositions under
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
There are no proofs or instance registrations here.

| Row | Original lines | Adapted target | Meaning |
| --- | --- | --- | --- |
| M243.025 | 300–308, declaration 301 | `decompositionGroupResidueAction_residueStatement` | Applying the residue action to the residue of `x` gives the residue of `sigma • x`. |
| M243.029 | 356–392, declaration 358 | `decompositionGroupResidueAction_surjectiveStatement` | Every automorphism of the selected residue field over the base residue quotient is induced by the decomposition group. |
| M243.030 | 394–413, declaration 395 | `decompositionResidueExtension_normalStatement` | The selected residue field is normal over the base residue quotient. |

Source: Naganori Yamaguchi, NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`.
Each target quantifies `(K : Type u) {L : Type v} [Field K] [Field L]
[Algebra K L]` in the source order, then `[IsGalois K L]` where the source
retains it, then `(A : ValuationSubring L)`. M243.025 has no Galois binder
(the source explicitly omits it) and additionally quantifies
`(sigma : decompositionGroup K A) (x : A)`. The two residue types stay in
`Type v`. M243.029 and M243.030 retain `[IsGalois K L]`, with no finiteness
assumption, so the infinite separable-closure consumers are covered.

The theorem targets replace source theorem declarations with suffix
`Statement` and a closed proposition. M243.025 is an `abbrev` so its later
proof theorem can retain the source `@[simp]` attribute. M243.029 is a
`def`. M243.030 is an `abbrev` so its exact proof can be registered as the
source instance; it states normality for the specific Field and Algebra
instances defined by M243.020 and M243.021. Source proofs are omitted.
Namespace prefix, imports, extracted module scope, docstrings and header
modification note change; the proposition telescopes and conclusions do
not. The unused source noncomputable section, scopes and section variables
are omitted because the targets carry their own complete telescopes.

Dependencies: published M243.023/.024 data and M243.020/.021 structures,
and their published proof prerequisites. The sole direct import is
`ResidueAction`; no private fixture is imported. Proofs are later child tasks after
these targets enter the Library. Their intended routes reuse Mathlib's
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` and the Library's
M242 `Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profinite`.
The source's private compactness and continuity facts (M243.008–.010)
will be proved inline by those consuming proof children and documented
there. No finite-dimensional restriction may be added.

Registered source `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Original Apache-2.0 copyright and author header is kept; the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are reused.
