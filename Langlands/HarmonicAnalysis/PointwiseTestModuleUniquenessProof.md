# Uniqueness of the actual smooth multiplier extension

`Langlands.HarmonicAnalysis.PointwiseTestModule.smoothExtensionUnique` proves
the published
`Langlands.HarmonicAnalysis.PointwiseTestModule.SmoothExtensionUniqueStatement`.
It identifies every smooth-function module extending the specified original
nondegenerate test action with the published canonical module, as equality
of module structures on the same additive carrier.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5 lemma, printed p.39 / PDF p.45;
the surrounding construction is printed pp.38–40 / PDF pp.44–46. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Those three original pages were read, and the lemma and its multiplier formula
were checked against the rendered page. The 2010 edition's supplementary
corrections, PDF pp.1–3, clarify that smooth nondegeneracy is relative to compact
indicators; this clarification is already present in the governing 2026 passage.

## Implemented proof

Write `A = PointwiseTestAlgebra.Carrier X`, `S = LocallyConstant X ℂ`,
and `i = PointwiseTestAlgebra.inclusion`. Let `μM` be the specified original
`A`-action, `hM` its nondegeneracy witness, and `σM` a competing `S`-module.
The target's sole premise says that `i(a)` acts under `σM` exactly as `a`
acts under `μM`, for every test `a` and every vector.

The proof installs only `σM` as the local smooth module, then derives the
scalar tower `IsScalarTower S A M`. For `f : S`, `a : A`, and `m : M`,
extension agreement, the published identity
`inclusion_ambient_smul`, and the competing module's multiplication law give

```text
μM(f • a, m)
  = σM(i(f • a), m)
  = σM(f * i(a), m)
  = σM(f, σM(i(a), m))
  = σM(f, μM(a, m)).
```

Thus scalar-tower compatibility is a consequence of extension agreement,
with no added hypothesis. The proof then applies the published generic theorem
`Langlands.Algebra.NondegenerateScalars.module_eq_of_compatible` with
`k = LocallyConstant X ℂ` and the actual pointwise test algebra's
`isIdempotented` witness. That theorem compares the canonical scalar action
with a compatible action using an original fixing idempotent, then applies
module extensionality. Reversing its equality gives exactly
`σM = PointwiseTestModule.module hM`.

The proof adds no commutation, relative-nondegeneracy or characteristic-fixer
premise. The generic theorem uses only the derived tower for the competing
action; its remaining algebra hypotheses are supplied by the published
pointwise multiplication instances. All original instances and the carrier
are retained.

## Scope and provenance

The theorem has independent space and module universes `uX` and `uM`, and
assumes only the supplied `TopologicalSpace X`. This is the arbitrary-topology
compact-clopen generalization documented by the published statement and
canonical construction. On Renard's Hausdorff spaces with a compact-open
neighborhood basis, compact opens are clopen, so it specializes to the source
lemma. The implemented proof is algebraic after importing that construction.
It neither chooses a point nor imposes nonemptiness, and therefore includes
empty spaces and zero modules without exceptions.

This is a derived host formulation of the source's uniqueness assertion:
the source specifies uniqueness of the extended action, and Lean expresses
it as equality with the actual canonical `Module` structure. The proof
reuses the Library's generic compatible-action argument rather than repeating
the source's characteristic-fixer calculation.

Restriction/extension categorical equivalence, module-sheaf categories and
their natural compact-section comparisons remain separate obligations.
