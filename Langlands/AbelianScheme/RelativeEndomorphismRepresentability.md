# Projective representability of the relative endomorphism functor

Authors: Worker 1042.

Module `Langlands.AbelianScheme.RelativeEndomorphismRepresentability`, the proof module of task
`6d6cc279-3071-445f-adba-589e54d9816b`. It proves the published proposition
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement.{u}` (module
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement`), for an arbitrary universe
`u`. The module adds no axioms; the proof depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Statement proved

- `Langlands.AbelianScheme.relativeEndomorphismRepresentability :
  RelativeEndomorphismRepresentabilityStatement.{u}`. For every commutative noetherian ring
  `R : Type u` and every abelian scheme `A` over `S = Spec R` whose structure morphism is
  H-projective (`Langlands.AlgebraicGeometry.IsHProjective`), there is `E : Over S` with `E.left`
  locally noetherian, such that on the full subcategory of locally noetherian schemes over `S` the
  relative endomorphism presheaf `relativeHomFunctor A.toCommGroupScheme A.toCommGroupScheme`
  (followed by the forgetful functor to sets) is naturally isomorphic to `yoneda.obj E`, and `E` is
  isomorphic over `S` to the coproduct of a family `P : I → Over S` (`I : Type u`) of H-projective
  schemes over `S`. The statement is the published one, unchanged.

## Proof

The proof term is
`relativeEndomorphismRepresentability_of_affineHomSchemePiecesStatement
AffineHomSchemePieces.affineHomSchemePieces`:

- `AffineHomSchemePieces.affineHomSchemePieces : AffineHomSchemePiecesStatement.{u}` (module
  `Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces`) gives, from the ported and
  universe-generalized FLT Hom scheme, a scheme `H` over `S`, separated, locally of finite type and
  formally unramified, representing the relative endomorphism functor on affine test schemes, with
  a family of closed, pairwise disjoint, covering opens that are quasi-compact over `S`.
- `relativeEndomorphismRepresentability_of_affineHomSchemePiecesStatement` (module
  `Langlands.AbelianScheme.RelativeHomNeronExtension`) derives the target from this interface: it
  is `relativeEndomorphismRepresentability_of_affineHomSchemePieces hP neronHomExtension` (module
  `Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityOfPieces`), where
  `neronHomExtension` is the extension of homomorphisms of abelian schemes from the generic fibre
  over a discrete valuation ring (from the ported FLT Néron mapping property). That reduction
  extends the representation from affine to all locally noetherian test schemes by Zariski gluing
  (module `Langlands.AbelianScheme.RelativeEndomorphismAffineExtension`), shows that each piece is
  proper over `S` (the noetherian valuative criterion with discrete valuation rings of
  `Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`, with lifts provided by
  `neronHomExtension`), hence finite (proper and locally quasi-finite, the latter from formally
  unramified and locally of finite type) and therefore H-projective, and identifies the
  representing scheme with the coproduct of its pieces.

## Mathematical provenance

The statement is the affine-base, H-projective case of the representability of the relative
endomorphism functor of an abelian scheme used by Kottwitz (see the Markdown of the statement
module). The proof follows the classical route: the Hom scheme of an abelian scheme is a locally
closed subscheme of a Hilbert scheme (Grothendieck; graphs of morphisms form an open subscheme of the
Hilbert scheme of the product, and homomorphisms a closed subscheme of that), its pieces of fixed
Hilbert polynomial are proper by the valuative criterion together with the Néron mapping property,
and unramified proper morphisms are finite. The Lean proof uses the Hom scheme constructed in the Anthropic Lean formalisation of
Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, literature id
`anthropic-flt-complete-lean-source-6e837e75`), ported in this contribution.

## Dependencies

- `Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement` (Library): the target.
- `Langlands.AbelianScheme.RelativeHomNeronExtension` and
  `Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces` (same contribution), with
  their dependencies listed in their Markdown files.
