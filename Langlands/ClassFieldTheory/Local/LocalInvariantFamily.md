# The local invariant family

Lean module: `Langlands.ClassFieldTheory.Local.LocalInvariantFamily`.

This module defines one concrete `InvariantFamily.{u,u} p` for `p`-adic fields.
It only defines maps; it proves no class-formation law. The laws are separate
statements and proofs.

## Definitions

All declarations are in the namespace `Langlands.ClassFieldTheory.Local`.

- `embeddedImage_finiteDimensional`, `embeddedImage_isGalois`: Prop-valued
  instances. Let `K` be a field, let `L` be a finite Galois extension of `K` (in
  any universe) and let `f : L →ₐ[K] AlgebraicClosure K` be a `K`-embedding.
  Then the image `f.fieldRange`, an intermediate field of `AlgebraicClosure K`,
  is finite dimensional and Galois over `K`. Both facts are transported along
  `f.equivFieldRange : L ≃ₐ[K] f.fieldRange`.
- `embeddedRelativeInvariant K L inv f`: for any additive map
  `inv : absoluteCohomology K 2 →+ RationalModIntegers` and any embedding `f`,
  this is the composite
  `relativeCohomology K L 2 → relativeCohomology K f.fieldRange 2 →
  absoluteCohomology K 2 → RationalModIntegers`. The first map is
  `relativeH2Equiv f.equivFieldRange`, the Library's transport of relative `H²`
  along a field equivalence. The second is `closureInflation`, the Library's
  inflation from a finite normal subextension of the algebraic closure to
  continuous absolute cohomology. The third is `inv`. The lemma
  `embeddedRelativeInvariant_apply` (proved by `rfl`) unfolds it.
- `closureEmbedding K L : L →ₐ[K] AlgebraicClosure K`: the embedding chosen by
  `IsAlgClosed.lift`.
- `localAbsoluteInvariant hEx F`: for `hEx : UnramifiedH2Exhaustion.{u}` and a
  `p`-adic field `F`, this is the Library map
  `AbsoluteInvariantAssembly.descendedHom F hEx closureInflationTowerCompatibility
  unramifiedInvariantInflationCompatibility`. It is an additive map
  `absoluteCohomology F.Carrier 2 →+ RationalModIntegers`. The Library builds it
  as follows. Each absolute class is the closure inflation of a class on a
  finite unramified Galois stage of `F`; this is what `hEx` asserts. The value
  is the unramified invariant of that stage class, computed with the arithmetic
  (Frobenius) coordinate. The two proved compatibilities make the value
  independent of the stage.
- `localInvariantFamily hEx p : InvariantFamily.{u,u} p` has these fields:
  - `absolute F := localAbsoluteInvariant hEx F`;
  - `relative F L := embeddedRelativeInvariant F.Carrier L
    (localAbsoluteInvariant hEx F) (closureEmbedding F.Carrier L)`.

  The lemmas `localInvariantFamily_absolute` and `localInvariantFamily_relative`
  (proved by `rfl`) unfold the two fields.

The parameter `hEx` is the Library statement `UnramifiedH2Exhaustion.{u}`: every
class in continuous absolute `H²` comes from a finite unramified stage. The
definition only needs it as a parameter. A theorem about the family can take a
proof of that statement as an argument.

## Provenance

Provenance: derived. Serre, *Local Fields* (1979), defines the invariant through
the unramified extension. Chapter XII, §1, Theorem 1 and its corollary (printed
page 181, PDF page 186) identify the Brauer group `B_K = H²(/K)` with
`H²(K_nr/K)`. Chapter XIII, §3 (printed pages 192–193, PDF pages 197–198) then
defines `inv_K : B_K → Q/Z` through the valuation and the Frobenius. Chapter
XIII, §4, Theorem 1 (printed pages 195–196, PDF pages 200–201) gives the class
formation. There the relative group `H²(F/E)` of a finite Galois subextension `F`
of a fixed separable closure is regarded as a subgroup of `H²(/E)` by inflation,
and its invariant is the restriction of `inv_E`.

`localAbsoluteInvariant` is the Library's formalization of Serre's `inv_K`,
descended from finite unramified stages. `localInvariantFamily` takes Serre's
relative invariant, but for an abstract finite Galois extension `L`, which is
not a subfield of the closure. The derived step is to first choose one
embedding of `L` into the algebraic closure and transport classes to its image.
The definition fixes the embedding `closureEmbedding`. That the invariant does
not depend on this choice is a separate theorem to be proved about the family.
It is not part of this definition.
