# Restriction law of the local invariant family

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRestrictionStatement`
(module `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`).
The exact-target theorem is

```
theorem localInvariantFamilyRestriction :
    LocalInvariantFamilyRestrictionStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every proof `hEx : UnramifiedH2Exhaustion.{u}`, every prime `p`, all p-adic
fields `F` and `E` with `E/F` finite (and the scalar tower `Padic p → F → E`),
every field `M` with a tower `F ⊆ E ⊆ M` such that `M/F` and `M/E` are finite
Galois, and every `x` in `H²(M/F)`,

```
(localInvariantFamily hEx p).relative E M (relativeRestriction F.Carrier E.Carrier M 2 x) =
  Module.finrank F.Carrier E.Carrier • (localInvariantFamily hEx p).relative F M x.
```

The module also proves two general lemmas about transport of relative
cohomology along field isomorphisms.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter XIII, §3, Proposition 7 (printed page 193, PDF page 198):
  `inv_L ∘ Res_{K/L} = n · inv_K` on Brauer groups, for a finite extension
  `L/K` of degree `n`.
- Chapter XI, §2, Axiom II b) (printed page 167, PDF page 173) is the same
  formula for a class formation, `inv_{E'} ∘ Res_{E/E'} = [E':E] · inv_E`. On
  the subgroups `H²(F/E)` it is the relative restriction law.

Serre regards `H²(M/F)` as a subgroup of the Brauer group, so the relative law
is the restriction of Proposition 7. The Lean proof uses continuous cohomology
of the algebraic closures in place of the Brauer groups. It derives the
relative law from the absolute degree law and the published base-change
square for closure inflation.

## General lemmas

- `relativeH2Equiv_relativeRestriction`: let `K ⊆ E ⊆ M` and `K ⊆ E ⊆ N` be
  towers, `e : M ≃ₐ[E] N`, and `x` in `H²(M/K)`. Then
  `relativeH2Equiv e (relativeRestriction K E M 2 x) =
  relativeRestriction K E N 2 (relativeH2Equiv (e.restrictScalars K) x)`.
  Proof: reduce to a cocycle (`groupCohomology.H2_induction_on`). Move both
  maps onto cocycles with `relativeH2Equiv_H2π` and
  `groupCohomology.H2π_comp_map_apply`. The two cocycles are then equal by
  definition, and `congr 1` closes the goal.
- `relativeInflation_relativeH2Equiv`: let `L'/K` be normal, `K ⊆ L' ⊆ M'` a
  tower, and `eL : M ≃ₐ[K] L'`, `eM : M ≃ₐ[K] M'` with
  `algebraMap L' M' (eL a) = eM a` for all `a`. Then for `x` in `H²(M/K)`,
  `relativeInflation K L' M' 2 (relativeH2Equiv eL x) = relativeH2Equiv eM x`.
  So inflation along a field isomorphism is transport. Proof: first,
  `relativeAutPullback eL (restrictNormalHom L' s) = relativeAutPullback eM s`
  for `s` in `Gal(M'/K)`. This follows by applying the injective maps `eL` and
  `algebraMap L' M'` and using `AlgEquiv.restrictNormal_commutes` and the
  hypothesis. Then compare cocycles as in the first lemma. The unit values
  agree by the hypothesis.

## The implemented proof of the target

After introducing the data and `x`:

1. Closure algebra. `E/F` is finite, so `AlgebraicClosure E.Carrier` is an
   algebraic closure of `F` (Mathlib instance). Let
   `ψ := IsAlgClosure.equiv F.Carrier (AlgebraicClosure F.Carrier)
   (AlgebraicClosure E.Carrier)`, an `F`-isomorphism. The proof makes `ψ` the
   algebra `AlgebraicClosure F.Carrier → AlgebraicClosure E.Carrier`. The
   scalar tower over `F` follows from `ψ.commutes`.
2. Fields in the closures. Let `fE := closureEmbedding E.Carrier M`, the
   chosen `E`-embedding of `M` into `AlgebraicClosure E.Carrier`, and
   `N := fE.fieldRange`. Let `g := ψ.symm ∘ fE`, an `F`-embedding of `M` into
   `AlgebraicClosure F.Carrier`, and `EM := g.fieldRange`. The Library instances
   `embeddedImage_finiteDimensional` and `embeddedImage_isGalois` make `N`
   finite Galois over `E` and `EM` finite Galois over `F`.
3. Algebras. `F → N` is the composite `F → E → N`. `EM → N` is `ψ`
   restricted to `EM` (`RingHom.codRestrict`). It lands in `N` because
   `ψ (g m) = fE m`. The proof checks the scalar towers `F → E → N` and
   `F → EM → N`. The compatibility `hComm` of the two embeddings of `EM` into
   `AlgebraicClosure E.Carrier` holds by `rfl`.
4. Right side. Unfold the relative invariant of `M` over `F`
   (`localInvariantFamily_relative`, `embeddedRelativeInvariant_apply`). Then
   replace the chosen embedding by `g.equivFieldRange` with the published
   `closureInflationTransportIndependence` (module
   `ClosureInflationIndependenceProof`).
5. Left side. By definition (`rfl`), it is the absolute invariant of `E`
   applied to
   `closureInflation E.Carrier N 2 (relativeH2Equiv fE.equivFieldRange
   (relativeRestriction F.Carrier E.Carrier M 2 x))`.
6. Rewrite the left side in three steps:
   - `relativeH2Equiv_relativeRestriction` moves the transport inside the
     restriction.
   - `relativeInflation_relativeH2Equiv` (with `eL := g.equivFieldRange`,
     `eM := fE.equivFieldRange.restrictScalars F.Carrier`; compatibility from
     `ψ.apply_symm_apply`) writes the transported class as the inflation from
     `EM` to `N` of `relativeH2Equiv g.equivFieldRange x`.
   - The published `closureInflationBaseChangeCompatibility` (module
     `ClosureInflationNaturalityProof`) for `F`, `E`, `EM`, `N` and `hComm`
     turns restriction after inflation and closure inflation into absolute
     restriction after closure inflation from `EM`.
7. The goal is now the degree law of the absolute invariant. Close it with
   `descendedHom_restriction` (module `AbsoluteInvariantAssembly`) and the
   published proofs `unramifiedBaseChangeStageExistence`,
   `closureInflationBaseChangeCompatibility` and
   `unramifiedInvariantBaseChangeCompatibility`.

## Notes

- The closure isomorphism `ψ` is chosen only inside the proof. The degree law
  of the absolute invariant holds for every compatible closure algebra.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
