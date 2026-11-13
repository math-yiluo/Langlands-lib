# Finite Galois subextensions of a residue algebraic closure

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.001 (private instance) | `finiteResidueBaseRingCharPrime` (43–45) | inlined by `haveI` in each declaration below that needs it |
| M236.005 | `finiteResidueExtensionEmbeddingInto` (58–68) | `finiteResidueExtensionEmbeddingInto` |
| M236.006 | `finiteResidueIntermediateFieldIn` (70–76) | `finiteResidueIntermediateFieldIn` |
| M236.007 | `finiteResidueExtensionEquivIntermediateIn` (78–85) | `finiteResidueExtensionEquivIntermediateIn` |
| M236.008 | `finiteResidueGaloisIntermediateFieldIn` (87–95) | `finiteResidueGaloisIntermediateFieldIn` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]` and `Omega : Type v` an
algebraically closed `k`-algebra field (source `variable` blocks, lines 39–41:
`[Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]`), and let `n : ℕ` with
`[NeZero n]`. Mathlib's `FiniteField.Extension k (ringChar k) n` is a chosen
degree-`n` extension of `k`; it needs the instance `Fact (ringChar k).Prime`.

- `finiteResidueExtensionEmbeddingInto k Omega n :
  FiniteField.Extension k (ringChar k) n →ₐ[k] Omega` is `IsAlgClosed.lift`, a
  chosen `k`-embedding into `Omega` (using that `Omega` is torsion free over
  the field `k`).
- `finiteResidueIntermediateFieldIn k Omega n : IntermediateField k Omega` is
  the image of the whole extension under this embedding.
- `finiteResidueExtensionEquivIntermediateIn k Omega n` is the resulting
  `k`-algebra equivalence `FiniteField.Extension k (ringChar k) n ≃ₐ[k]` that
  image (`IntermediateField.topEquiv.symm` followed by
  `IntermediateField.equivMap`).
- `finiteResidueGaloisIntermediateFieldIn k Omega n :
  FiniteGaloisIntermediateField k Omega` is that image, finite-dimensional and
  Galois over `k` because it is isomorphic to the finite field extension.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the source `variable` blocks,
  universes, `open` commands (except the one below), names, binders, bodies and
  `noncomputable` status are retained. As in the source, each definition takes
  only the section binders it uses; none of them uses
  `[Algebra.IsAlgebraic k Omega]`, so it is not a parameter (the source
  definitions have the same parameter lists).
- Private instance M236.001. The source declares the private instance
  `finiteResidueBaseRingCharPrime [Finite k] : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩` (with `omit [Fintype k]`), which
  instance search uses (with `Finite k` from `[Fintype k]`) wherever
  `FiniteField.Extension k (ringChar k) n` occurs. Here no instance is declared:
  the same value `⟨CharP.char_is_prime k (ringChar k)⟩` is supplied by
  `haveI : Fact (ringChar k).Prime := …` at the front of the type of M236.005
  and M236.007 and of the bodies of M236.005–M236.008. `haveI` substitutes the
  value into the elaborated term and leaves no binder, so each type and value is
  the source's with the private constant unfolded to its value; since
  `Fact (ringChar k).Prime` is a proposition, any instance of it is
  definitionally equal to this one. No global or local instance is added.
- The private instances M236.002 (`IsAlgClosure k Omega`), M236.003
  (`IsGalois k Omega`) and M236.004 (`T2Space (Omega ≃ₐ[k] Omega)`) are not used
  by these four definitions and are not declared.
- The type of M236.008 is filled by an anonymous structure instance
  `{ toIntermediateField := …, finiteDimensional := …, isGalois := … }` after
  the `haveI`, instead of the source's `where` clauses; the fields and their
  values are the source's.
- The source imports of the NYLL modules `ResidueAbsoluteDegree` and
  `InfiniteGaloisCorrespondence` are replaced by the Mathlib modules these
  commands use (`Mathlib.FieldTheory.Finite.Extension`,
  `Mathlib.FieldTheory.Galois.Profinite`, `Mathlib.FieldTheory.IsAlgClosed.Basic`).
  The source's `open ClassFormation` and
  `open RamificationTheory.Field.absoluteGaloisGroup` (NYLL namespaces unused
  by these commands) are dropped.
- The later data commands M236.012, M236.016 and M236.017 mention the M168
  Frobenius homomorphism or need later proofs and are not part of this module.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
