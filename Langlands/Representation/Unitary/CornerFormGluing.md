# Gluing compatible corner-adjoint forms on fixed vectors

Author: Worker 4713.

This helper module proves the gluing step of
`Langlands.CornerFormGluingStatement` in a form that assumes compatibility.
`Langlands/Representation/Unitary/CornerFormGluingProof.lean` removes that
assumption by normalization.

## Setting

- `G` is a topological group with a Borel structure. `μ` is a Haar measure
  that is also right invariant and inversion invariant. These are the
  hypotheses under which the Library equips the Hecke algebra and its corners
  with the involution `f*(x) = conj (f x⁻¹)`
  (`Langlands/Representation/Hecke/UnimodularStar.lean`).
- `ρ : Representation ℂ G V` is smooth (`IsSmooth ρ`): every vector is
  fixed by some open subgroup. `V` carries no topology.
- `K₀` is an open subgroup with `IsCompact (K₀ : Set G)`.
- `b` assigns to every compact open `K ≤ K₀` a Mathlib
  `InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup)`, that is, a
  positive definite Hermitian form on the fixed space `ρ^K`.

## Main result

`Langlands.CornerFormGluing.isUnitarizable_of_compatibleCornerForms`
assumes two families of identities.

1. `hstar` (corner adjointness): for every compact open `K ≤ K₀`, every
   element `f` of the corner `Hecke.HeckeAlgebra.Corner μ K hK` and all
   `x, y ∈ ρ^K`,
   `(b K).inner (cornerAction f x) y = (b K).inner x (cornerAction (star f) y)`.
   Here `Hecke.cornerAction` is the Library's integrated action of the corner
   on `ρ^K`.
2. `hcompat` (compatibility): for compact open `L ≤ K ≤ K₀` and
   `v, w ∈ ρ^K`, the `L`-form evaluated at `v, w`, viewed in `ρ^L`, equals
   `(b K).inner v w`.

The conclusion is `IsUnitarizable ρ`, the existence of a `G`-invariant
positive definite Hermitian form on `V` (`Unitary/Basic.lean`).

## Auxiliary results

In namespace `Langlands.Hecke`:

- `integratedAction_rightTranslate_of_isMulRightInvariant`: for a right
  invariant `μ`, the integrated action of the right translate
  `x ↦ f (x g)` applied to `v` equals the integrated action of `f` applied to
  `ρ g⁻¹ v`. The proof tests against every linear functional
  (`integratedAction_dual`) and substitutes `x ↦ x g⁻¹` with
  `integral_mul_right_eq_self`.
- `star_leftTranslate_normalizedIndicator`: the involution of the left
  translate by `g` of the normalized indicator `e_K` is its right translate by
  `g`. This follows pointwise from `star_normalizedIndicator`.
- `Corner.star_project`: the involution commutes with the corner projection
  `h ↦ e_K h e_K`. This holds because the involution reverses products and
  fixes `e_K`.
- `cornerAction_star_translateCornerElement`: the involution of the Library's
  `translateCornerElement μ K hK g` acts on `ρ^K` as `u ↦ P_K (ρ g⁻¹ u)`,
  where `P_K` is `fixedProjection`. The Library's
  `cornerAction_translateCornerElement` gives the companion formula
  `u ↦ P_K (ρ g u)` for the element itself.

In namespace `Langlands.CornerFormGluing`:

- `conjOpenSubgroup g K` is the open subgroup `g K g⁻¹`.
  `mem_fixedVectors_conj` shows that `ρ g v` is fixed by it whenever `v` is
  fixed by `K`.
- `mem_fixedVectors_of_le`: fixed vectors of `K` are fixed by every
  `L ≤ K`.
- `isCompact_of_le`: an open subgroup of a compact open subgroup is compact,
  since open subgroups are closed. No Hausdorff hypothesis is used.
- `stabilizer ρ hρ v` is an open subgroup fixing `v`, chosen by smoothness.
  `pairLevel ρ hρ K₀ v w = K₀ ⊓ stab v ⊓ stab w` and
  `tripleLevel ρ hρ K₀ u v w = pairLevel ρ hρ K₀ u v ⊓ stab w`.
- `gluedInner ρ hρ hK₀ b v w` is the `pairLevel`-form evaluated at
  `v, w`.
- `gluedInner_eq` and `gluedInner_eq_of_mem`: under `hcompat`,
  `gluedInner v w = (b K).inner v w` for every compact open `K ≤ K₀`
  fixing `v` and `w`. Apply compatibility to `K ⊓ pairLevel v w`, which lies
  below both levels.
- `gluedCore` is the resulting `InnerProductSpace.Core ℂ V`. Each axiom is
  checked at a level fixing all vectors involved, using `pairLevel` or
  `tripleLevel`. There `gluedInner` agrees with a single form `b K`, which
  satisfies the axiom. Definiteness and nonnegativity are read off at
  `pairLevel v v`.

## Implemented proof of invariance

Fix `g`, `v`, `w`. Let `K = pairLevel v w` and `L = K ⊓ g K g⁻¹`. Then
`L ≤ K₀` is compact open, `v, w` are `L`-fixed, and so are `ρ g v` and
`ρ g w`. Let `f = translateCornerElement μ L hL g`. By
`cornerAction_translateCornerElement` and `fixedProjection_fixed`,
`f` sends `v` to `ρ g v`. By `cornerAction_star_translateCornerElement`,
`star f` sends `ρ g w` to `P_L (ρ g⁻¹ ρ g w) = w`. With
`gluedInner_eq_of_mem` at level `L`,

`gluedInner (ρ g v) (ρ g w) = (b L).inner (f v) (ρ g w)
  = (b L).inner v ((star f) (ρ g w)) = (b L).inner v w = gluedInner v w`,

where the middle equality is `hstar`. This is the invariance field of
`InvariantPositiveForm`, so `ρ` is unitarizable.

## Provenance

This is the gluing step (step 4, after normalization) and the invariance step
(step 5) of the outline in
`Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.md`.
That outline adapts the proof of Theorem 2.7 in Tadic, *Classification of
unitary representations in irreducible representations of general linear
group (non-archimedean case)*, Ann. Sci. ENS 1986, printed p.349
(`tadic-1986-unitary`). There `G` is the group of `F`-rational points of a
connected reductive group (§2.6, p.346). Tadic obtains the `G`-invariance of
the limit inner product "directly" from the adjoint relation for `H(G)`. The
explicit use of `e_L ⋆ δ_g ⋆ e_L` and of its involution is the Lean route
for that step. Here the group is any topological group with the measure
hypotheses above.

## Validation

`lean_check` diagnostic `69c731ca-4353-498b-a13b-3b644e55c619` compiled this
module and `CornerFormGluingProof` without errors or warnings. The axioms of
the final theorem were `propext`, `Classical.choice` and `Quot.sound`.
