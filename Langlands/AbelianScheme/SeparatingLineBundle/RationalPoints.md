# Rational points of group schemes over algebraically closed fields

This module supplies two facts about rational points used to build the separating line
bundle of `Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement`. It
imports only Mathlib.

Throughout, `K : Type u` is an algebraically closed field (`[Field K] [IsAlgClosed K]`).
A rational point of a scheme `X` with structure morphism `p : X ⟶ Spec K` is a morphism
`x : Spec K ⟶ X` with `x ≫ p = 𝟙 _`. This equation is the definition of the Library
predicate `Langlands.AlgebraicGeometry.Picard.IsRationalPoint p x`. The module writes the
equation directly, so it does not import that file. The underlying point of `x` is the
image `x (IsLocalRing.closedPoint K)` of the unique point of `Spec K`.

## Declarations

All declarations live in the namespace `Langlands.GroupScheme.SeparatingLineBundle`.

- `exists_rationalPoint_mem_of_isOpen`. Let `X : Scheme.{u}` be irreducible and let
  `p : X ⟶ Spec K` be locally of finite type. Let `ι` be a finite index type in any
  universe. Let `U : ι → Set X` be open subsets, each nonempty. Then some rational point
  `x` has its underlying point in every `U i`. If `ι` is empty, the conclusion says only
  that `X` has a rational point.
- `commonRationalPoint p U hU hne : Spec K ⟶ X` is a choice of such a point, made with
  `Classical.choose`. It takes the same arguments as the previous theorem.
  `commonRationalPoint_comp` says it is a rational point: `commonRationalPoint p U hU hne
  ≫ p = 𝟙 _`. `commonRationalPoint_mem` says its underlying point lies in `U i` for each
  `i`. This definition is the declaration recorded for the contribution. It exists so that
  later constructions can refer to one fixed point; it adds no mathematical content beyond
  the theorem.
- `irreducibleSpace_of_grpObj`. Let `G : Over (Spec K)` be a group object (`[GrpObj G]`).
  Suppose `G.hom` is locally of finite type and the underlying space `G.left` is compact
  and connected. Then `G.left` is irreducible. Commutativity is not assumed.
- `irreducibleSpace_of_smooth_of_isProper`. For `G : Grp (Over (Spec K))` with `G.X.hom`
  smooth, proper and geometrically connected, `G.X.left` is irreducible. These are the
  geometric hypotheses of the target statement, given here as instance arguments.

## Proofs

**Common rational point.** A scheme locally of finite type over a field is a Jacobson space
(Mathlib `LocallyOfFiniteType.jacobsonSpace`). Since `X` is irreducible, finitely many
nonempty open subsets have a nonempty open intersection. The proof shows this by induction
over a `Finset` with `nonempty_preirreducible_inter`. In a Jacobson space every nonempty
locally closed subset contains a closed point (`nonempty_inter_closedPoints`). Since `K` is
algebraically closed, Mathlib's `pointOfClosedPoint` turns a closed point `c` into a
rational point. `pointOfClosedPoint_comp` shows it is a section of `p`, and
`pointOfClosedPoint_apply` shows its underlying point is `c`.

**Irreducibility of group schemes.** A scheme locally of finite type over a field is
locally Noetherian. Since `G.left` is compact, it is a Noetherian space and therefore has
finitely many irreducible components. The proof first shows that distinct components
`Z₁ ≠ Z₂` are disjoint. Suppose instead that `Z₁ ∩ Z₂` is nonempty. This intersection is
closed, so it contains a closed point `y`. The complement of the union of the components
other than `Z₁` is a nonempty open set: it is open because finitely many closed sets have
closed union, and it is nonempty because Mathlib's
`closure_sUnion_irreducibleComponents_sdiff_singleton` rules out that the other
components cover `G.left`. This set contains a closed point `w`, and `Z₁` is the only
component containing `w`.

Both `y` and `w` come from rational points `y'` and `w'`, through the equivalence
`pointEquivClosedPoint` between rational points and closed points. Composing the inverse of
right multiplication by `w'` with right multiplication by `y'` gives an automorphism `α` of
`G` over `Spec K`, built from Mathlib's `GrpObj.mulRight`. The equation `w' ≫ α.hom = y'`
holds, so the underlying homeomorphism `e` of `α` sends `w` to `y`. Homeomorphisms map
irreducible components to irreducible components (`preimage_mem_irreducibleComponents`).
So `e ⁻¹' Z₁` and `e ⁻¹' Z₂` are components containing `w`, and hence both equal `Z₁`.
Since `e` is surjective, preimage under `e` is injective, which gives `Z₁ = Z₂`, a
contradiction.

The components therefore form a finite cover of `G.left` by pairwise disjoint closed sets.
So the complement of any one component is the union of the others, a closed set, and each
component is clopen. Since `G.left` is connected and nonempty, the component of any point
is the whole space, and so `G.left` is irreducible.

**Smooth proper case.** Smoothness gives local finite type. Properness gives
quasi-compactness of `G.X.hom`, and `Spec K` is compact, so `G.X.left` is compact
(`QuasiCompact.compactSpace_of_compactSpace`). `Spec K` is a single point, so geometric
connectedness makes `G.X.left` connected
(`GeometricallyConnected.connectedSpace_of_subsingleton`). The previous theorem then
applies.

## Provenance

This is internal derived content by Worker 899. It cites no literature source.
Irreducibility of connected algebraic groups is a standard fact. The proof given here is
written for this project. It uses only Mathlib facts: Jacobson spaces, irreducible
components of Noetherian spaces, `pointEquivClosedPoint` and `GrpObj.mulRight`. It does not
use geometric integrality of group schemes, which belongs to a separate, unproved task.
The common rational point is how the separating-line-bundle proof chooses translation
parameters. Milne, *Abelian Varieties* (author revision 2022), p. 11, chooses the closed
point `b₁` outside two proper closed subsets of `A`, and then chooses `aᵢ` and `bᵢ` for
`i ≥ 2` in the same way. The common rational point makes this choice. The complements of
the proper closed subsets are nonempty open sets, and rational points are the closed
points of `A` over an algebraically closed field.
