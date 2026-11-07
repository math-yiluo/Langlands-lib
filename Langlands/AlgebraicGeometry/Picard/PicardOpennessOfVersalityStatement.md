# Openness of versality for actual Picard families: statement

This module states openness of versality, in the sense of The Stacks Project,
Artin's Axioms, Definition 98.13.1 (Tag 07XQ), for the actual Picard stack of a
proper flat scheme over a noetherian ring. It is a statement only. No proof is
given here.

Source: snapshot `stacks-artin-axioms-approximation-2026-11-06`, file
`artin.pdf`. Definition 98.12.2 (Tag 07XF, PDF p. 18) defines versality at a
finite type point. Lemma 98.12.5 (Tag 07XG, PDF p. 19) passes versality to
finite extensions of the residue field. Definition 98.13.1 (Tag 07XQ,
PDF pp. 21–22) defines openness of versality.

Namespace: `Langlands.AlgebraicGeometry.Picard`. All rings and schemes live in
one universe `u`.

## The statement

`PicardOpennessOfVersalityStatement : Prop` says the following. Let:

- `R : Type u` be a noetherian commutative ring;
- `X : Over (Spec R)` have `IsProper X.hom` and `Flat X.hom`;
- `U : Over (Spec R)` have `LocallyOfFiniteType U.hom`;
- `L` be an actual line bundle (`Picard.LineBundle`) on
  `(relativeSpace X.hom).obj U`, the fibre product `U ×_R X`;
- `u₀` be a point of `U.left`, `K : Type u` a field with an `R`-algebra
  structure, and `p : ArtinianTest.residueBase R K ⟶ U` a morphism over
  `Spec R`;
- `e : U.left.residueField u₀ ≅ CommRingCat.of K` be a ring isomorphism with
  `p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀`. So `p` is the
  canonical point of `u₀`, with its residue field identified with `K`;
- `p.left` be locally of finite type, that is, `u₀` is a finite type point;
- `PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p` hold.

Then there is an open `V : U.left.Opens` with `u₀ ∈ V` and the following
property. For every field `K' : Type u` with an `R`-algebra structure and every
`p' : ArtinianTest.residueBase R K' ⟶ U` such that `p'.left` is locally of finite
type and its image lies in `V`, `IsFormallyVersalAt X.hom L p'` holds.

## Correspondence with the source

- The fibred category is the actual Picard groupoid pseudofunctor of the
  Library: objects over `T` are actual line bundles on `T ×_R X`, with their
  isomorphisms (`PicardGroupoid.relative`). The Library's `Picard.StackAtlas`
  uses the same pseudofunctor.
- Versality at a point is the Library's `IsFormallyVersalAt`. Its tests are
  `ArtinianTest R K`: local Artinian `R`-algebras with a surjective
  `R`-augmentation to `K`. For such a ring, `R → A` factors through the
  localization of `R` at the image prime, so these are the Stacks category
  `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `K`. The lifting
  condition along every surjective test arrow is smoothness of the morphism of
  deformation categories in Definition 98.12.2. It keeps the actual chart map
  and the actual bundle isomorphism.
- The hypothesis on `u₀` is versality at a finite type point with its own
  residue field, as in Definition 98.12.2. The isomorphism `e` only names that
  residue field `K`.
- The conclusion asks for versality at all locally finite type field points
  `p'` with image in `V`. Such a `p'` has image a finite type point `u` of `V`
  with `K'` finite over `κ(u)`. Definition 98.13.1 gives versality at `u` with
  residue field `κ(u)`, and Lemma 98.12.5 extends it to `K'`. That lemma
  needs the Rim–Schlessinger condition (RS). The Picard stack satisfies it,
  since it is algebraic (Stacks Proposition 99.10.2, Tag 0D04) and algebraic
  stacks satisfy (RS) (Artin's Axioms, Lemma 98.5.2, Tag 07WQ). The Lean
  statement therefore combines these two source results. This form is the one
  used downstream: point fibres over finite type tests produce such points with
  `K'` the residue field of a point of the fibre.
- The base is a noetherian affine scheme `Spec R`, not a general locally
  noetherian scheme. `Flat` and `IsProper` are the hypotheses of the
  finite-type Picard atlas task. Finite presentation of `X.hom` follows from
  properness over a noetherian base.

## Intended proof route (not part of the statement)

The proposed route specializes a general criterion of Artin's Axioms,
Section 98.24 (PDF pp. 46–48), to the Picard stack. Situation 98.24.2
(Tag 07YX) fixes `X` with (RS*), an affine `U = Spec A` of finite type, an
object `x` over `U`, a complex `K•` of `A`-modules, an isomorphism of tangent
spaces `T_x(-) ≅ H¹(K• ⊗ -)`, and obstruction classes in `H²(K• ⊗ I)`, with
functoriality and the vanishing criterion for lifts. Lemma 98.24.4 (Tag 07YZ)
then proves openness of versality at a closed point when condition (iv) of
Lemma 98.24.3 (Tag 07YY) holds and `K•` is perfect. Its proof reduces to
Lemma 98.23.4 (Tag 07YN).

These passages are general and conditional. They do not carry out the Picard
application. For line bundles the inputs still to be supplied are (RS*) for
the Picard stack, the tangent identification with `H¹`, functorial `H²`
obstruction classes, compatibility (iv), and a perfect complex `K•`. The
proposed choice, which is not taken from the cited passages, is
`K• = N• ⊗_Λ A` for a finite complex `N•` of finite projective `Λ`-modules
that universally computes the cohomology of the structure sheaf. Example
98.24.1 (Tag 07YW) does not treat line bundles. It continues Example 98.22.3
(Tag 07YH), the functor of global sections of a flat quasi-coherent module `F`,
whose obstructions lie in `H¹`. With `K• = N• ⊗_Λ A[-1]` these obstructions
appear in `H²`. The example only illustrates the method.

## Provenance

Source statement: Stacks Definitions 98.12.2 and 98.13.1 with Lemma 98.12.5,
specialized to the actual Picard stack over `Spec R`, as recorded above.
