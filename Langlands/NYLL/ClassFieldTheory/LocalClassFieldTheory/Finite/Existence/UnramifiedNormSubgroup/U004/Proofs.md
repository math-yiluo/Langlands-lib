# Vanishing of the normalized valuation modulo a degree

The theorem
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_eq_zero_iff_dvd`
has exactly the published proposition type
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegree_eq_zero_iff_dvdStatement`.
It retains the arbitrary universe `u`, field `K : Type u`, instances
`[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, natural modulus `n`, and
`x : Additive Kˣ`, in the order of the published target.

For every such input, `valuationModDegree K n x = 0` if and only if
`(n : Int)` divides the published normalized integer valuation
`LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x`.
There is no positivity or nonzero hypothesis on `n`; the theorem also
covers `n = 0`. The reduced valuation, its underlying valuation, and their
sign convention are used unchanged.

## Implemented proof

After introducing the universally quantified inputs of the closed target,
`change` evaluates the published composite homomorphism
`valuationModDegree K n` definitionally. The left side becomes the
vanishing of the integer cast of `valuationMap K x` into `ZMod n`.
Mathlib's `ZMod.intCast_zmod_eq_zero_iff_dvd`, applied to that integer and
`n`, is exactly the remaining equivalence. This lemma has no condition
on `n`, so no case or hypothesis is lost at zero.

The sole direct import is the published `UnramifiedNormSubgroup.AdditiveStatements`
module, which already imports the reduced valuation definition and
`Mathlib.Data.ZMod.Basic`. No separate evaluation theorem or additional
NYLL proof is needed.

## Source correspondence and modifications

This adapts M266.004, original theorem
`LocalClassFieldTheory.valuationModDegree_eq_zero_iff_dvd`, lines 53–59 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original file was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source is under that registration's
`n-yamaguchi-0729--ClassFieldTheory/source/` directory followed by the
original module path. No applicable NYLL errata entry was found in the
project notes.

The proof follows the source's reduction to the same Mathlib divisibility
lemma. Worker 527 added the `Langlands.NYLL` namespace prefix and expressed
the theorem's signature as the exact existing closed Library target,
retaining its universe and complete hypotheses. The source's
`rw [valuationModDegree_apply]` is replaced by the definitionally equal
`change` step. Imports are reduced to the target module. No additional
mathematical declaration or assumption is introduced.

The original copyright and author header is retained, with a modification
record. Apache-2.0 license and notices are already published in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
