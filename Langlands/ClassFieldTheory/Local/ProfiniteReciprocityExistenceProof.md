# Existence and uniqueness of normalized profinite local reciprocity

Author: Worker 4908.

The theorem `Langlands.LocalClassField.profiniteReciprocityExistenceUniqueness`
proves the published proposition
`Langlands.LocalClassField.ProfiniteReciprocityExistenceUniqueness.{u}` from
module `Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement`. It
covers every prime `p`, every p-adic field `F : PadicField.{u} p` in an arbitrary
carrier universe `u`, and every supplied original datum `T : F.TopologicalData`
with its topology `T.topology`. For each such field there is exactly one continuous
homomorphism

```lean
F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier
```

that satisfies `GeometricProfiniteReciprocityRelation F T`. That relation is the
full `ProfiniteNormResidueRelation` (density, exact finite norm kernels, surjective
finite restrictions and restriction compatibility) together with the geometric
residue congruence for every actual finite abelian extension, every supplied
extension datum and every base unit of order one. The theorem adds no hypothesis
and leaves the target's Lean/Markdown pair and its imports unchanged.

## Proof

The proof is a single application of two published theorems:

```lean
ProfiniteReciprocityAssembly.profiniteReciprocity_of_finiteArtin
  geometricFiniteArtinSystemExistenceUniqueness
```

- `Langlands.LocalClassField.geometricFiniteArtinSystemExistenceUniqueness`
  (module `Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof`)
  proves `GeometricFiniteArtinSystemExistenceUniqueness.{u}` unconditionally.
  For every prime, every `F : PadicField.{u} p` and every supplied `T`, there is
  exactly one `a : FiniteArtinFamily F.Carrier` satisfying
  `GeometricFiniteArtinSystemRelation F T a`.
- `Langlands.LocalClassField.ProfiniteReciprocityAssembly.profiniteReciprocity_of_finiteArtin`
  (module `Langlands.ClassFieldTheory.Local.ProfiniteReciprocityAssembly`) proves
  the implication from `GeometricFiniteArtinSystemExistenceUniqueness.{u}` to
  `ProfiniteReciprocityExistenceUniqueness.{u}` at the same universe. For
  existence, it reconstructs a continuous profinite homomorphism from the unique
  finite family, and `reconstruct_geometric` proves the full profinite relation.
  For uniqueness, the finite restrictions of any competing homomorphism form a
  family satisfying the finite relation. That family equals the chosen one, and
  finite restriction is injective.

Both theorems are used at the universe `u` of the target, so the universe
quantification is unchanged. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This pair is an internal assembly of published results. It makes no new
mathematical claim beyond the target statement. The arithmetic content is in the
imported proofs, and each keeps its own authorship and literature provenance in
its paired Markdown. Worker 4966 constructed the finite existence through Artin
symbols built from cyclic classes (Serre, *Local Fields*, XI.3), and Worker 1651
wrote the finite-to-profinite reconstruction assembly.
