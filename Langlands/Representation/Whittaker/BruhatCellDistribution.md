# Distributions on actual upper Bruhat cells

Authors: Worker 634 (original interface and proofs) and Worker 1005
(source verification and expanded documentation).

This interface packages the cellwise distribution convention of Shalika (1974),
Proposition 1.8, printed p.175, using the actual cell subtype from
`Langlands.Group.GL.UpperBruhatCells` and the algebraic distributions from
`Langlands.HarmonicAnalysis.Distribution.Basic`. It is an internal adapter of
the published global Whittaker distribution convention. The cell translations,
subtype homeomorphisms, evaluation lemmas and conditional transpose restriction
are elementary deductions from the imported definitions. This pair establishes
the interface needed to state the later cellwise assertions.

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974),
171–193. The retained source is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Proposition 1.8 is on printed p.175, PDF page 6 (zero-based index 5).
The translation definitions are on printed p.174, PDF page 5; the
transpose test-function argument in the proof is on printed p.178, PDF
page 9. Worker 1005 read these three pages and visually checked pp.175
and 178. Worker 634 previously read printed pp.173–179 and visually
checked pp.176–178. No matching source-specific errata note was found
in the current project or Library notes.

The source's equation is
`T (L_(u₁⁻¹) R_u₂ f) = χ(u₁u₂) * T f`. Its definitions of left and
right translation make the test function `g ↦ f(u₁*g*u₂)`. The
homomorphism law identifies `χ(u₁u₂)` with `χ(u₁) * χ(u₂)`, explaining
the two positive factors below. The general-ring interface, bundled
homeomorphisms and explicit stability parameter are internal deductions
from the imported APIs. They extend the source's local-field conventions
at this elementary level; the conclusion of Proposition 1.8 is a separate
mathematical obligation.

All declarations are in `Langlands.Whittaker`, over every commutative topological
ring `R` in universe `uR`, every natural `n`, and every permutation `w` of
`Fin (n + 1)`. The positive rank includes rank one by taking `n = 0`. Write
`C_w = upperBruhatCell (n + 1) R w`. This is the actual double coset
`B * permutation (n + 1) R w * B`, expressed by the imported existential
membership condition, and `UpperBruhatCell (n + 1) R w` is its subtype.
The matrix group uses the existing topology on units of matrices; the
upper-unipotent subgroup and cell use the usual inherited subtype
topologies. No coordinate-space identification of the cell is used.

For this cell subtype `X`, `SchwartzBruhat X` is the actual complex vector
space of locally constant functions `X → ℂ` with compact support.
`Distribution X = Module.Dual ℂ (SchwartzBruhat X)` is its full complex
algebraic dual: every complex linear functional is allowed, with no
continuity condition on the functional. Pullback along a homeomorphism
preserves local constancy and compact support and is the existing complex
linear equivalence `Hecke.TestFunction.pullback`.

`bruhatCellBiTranslate n R w u₁ u₂` is the homeomorphism whose underlying
matrix formula is `g ↦ u₁ * g * u₂`. Its inverse is
`g ↦ u₁⁻¹ * g * u₂⁻¹`. Cell membership follows from the imported left and
right stability under upper triangular matrices, through the actual inclusion
of the upper-unipotent subgroup. Both inverse laws follow from the group laws,
and continuity follows from multiplication and the subtype topology.
`bruhatCellBiTranslate_val` and `bruhatCellBiTranslate_symm_val` expose these
formulas; `pullback_bruhatCellBiTranslate_apply` exposes test-function evaluation.

`IsBiEquivariantBruhatCellDistribution n R w ψ D` means, for every actual
upper-unipotent `u₁,u₂` and every cell test function `f`,

```text
D (f ∘ bruhatCellBiTranslate u₁ u₂) =
  (standardCharacter ψ n u₁ * standardCharacter ψ n u₂) * D f.
```

Both character factors are positive, exactly as in the global convention.
Here `ψ : UnitaryAdditiveCharacter R` is the imported continuous,
nontrivial unit-circle-valued additive character, and the adjacent-entry
character is the imported `standardCharacter ψ n`. Both values are
coerced to `ℂ` before multiplication. The
`isBiEquivariantBruhatCellDistribution_iff` lemma is the literal evaluation
equivalence, proved by `Iff.rfl`.

`bruhatCellWeylTranspose n R w hτ` restricts the actual
`weylTransposeHomeomorph n R` using a supplied proof
`hτ : Set.MapsTo tau C_w C_w`, where `tau = weylTransposeHomeomorph n R`.
Writing `J = weylLong (n + 1) R`, its underlying formula is
`g ↦ J * transposeHomeomorph (n + 1) R g * J`, with entries
`(tau g) i j = g j.rev i.rev`, by the imported global evaluation lemmas.
The same formula is its inverse, by the imported involution. Applying
`hτ` gives both membership proofs; subtype extensionality and the global
involution give both inverse laws. Composing the global continuous map
with subtype inclusion and lifting into the subtype proves continuity.
Its value and involution lemmas are
`bruhatCellWeylTranspose_val` and `bruhatCellWeylTranspose_involutive`.
`IsWeylTransposeInvariantBruhatCellDistribution n R w hτ D` is the equation
that its distribution pushforward fixes `D`. The corresponding
`isWeylTransposeInvariantBruhatCellDistribution_iff` lemma says exactly

```text
∀ f : SchwartzBruhat (UpperBruhatCell (n + 1) R w),
  D (pullback (bruhatCellWeylTranspose n R w hτ) f) = D f.
```

Evaluating the equality of distributions proves the forward implication;
extensionality of linear maps proves the reverse implication. This uses
the existing pushforward formula `(e_*D)(f) = D(f ∘ e)`, with no measure
or modular factor.

The constructions require only `CommRing R`, `TopologicalSpace R` and
`IsTopologicalRing R`. There are no field, Hausdorff, local compactness,
total disconnectedness or analytic hypotheses. In particular all
constructions specialize to each canonical p-adic field topology in
arbitrary field universe by installing `F.canonicalNormedField` for
`F : PadicField p`; the conditional transpose constructions still take
the specified `hτ`.

The parameter `hτ` is part of this interface. An arbitrary Bruhat cell need
not be stable under this transpose. Cell stability, character-compatible
support, vanishing, orbital integration and cellwise or global distribution
invariance remain separate statement and proof obligations. The present
pair defines the predicates and proves their elementary evaluation
equivalences; it supplies no implication from bi-equivariance to transpose
invariance.
