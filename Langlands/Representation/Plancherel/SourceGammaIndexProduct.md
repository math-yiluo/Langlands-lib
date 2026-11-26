# Relative indices of split compact traces

This module is elementary group theory used to evaluate Waldspurger's
constant `γ(P)` by finite subgroup indices. It follows the index
computation in the proof of Remark (3) of I.1 in J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed pp.240–241
(PDF pp.6–7), registered as `waldspurger-2003-plancherel`. There the
index `[U ∩ K : U ∩ H]` of a unipotent radical is split into a product
of indices of smaller unipotent groups. Here the splitting is along a
semidirect decomposition `X = Bs ⋉ N` rather than along root subgroups,
and no topology or measure is involved. The provenance is internal: the
statements are standard facts about subgroup indices.

All results hold in an arbitrary group `A`. `Subgroup.relIndex H K` is
Mathlib's index of `H ∩ K` in `K`.

## Declarations

- `relIndex_eq_index_of_forall_mul`: if every element of `A` is `t * y`
  with `t ∈ T` and `y ∈ Y`, then `Y.relIndex T = Y.index`. The proof lets
  `T` act on the left cosets `A ⧸ Y`. The action is transitive by the
  hypothesis, and the stabilizer of the trivial coset is
  `Y.subgroupOf T`. Mathlib's `MulAction.index_stabilizer_of_transitive`
  then gives the equality.
- `relIndex_eq_of_forall_mem_mul`: the same statement inside a subgroup
  `Z` containing `Y` and `T`: if every element of `Z` is `t * y`, then
  `Y.relIndex T = Y.relIndex Z`. It applies the previous result in `Z`
  and Mathlib's `Subgroup.relIndex_subgroupOf`.
- `relIndex_congr_inf`: `Y.relIndex T` depends only on `Y ⊓ T`.
- `relIndex_inf_eq_mul` (indices of split traces): let `N ≤ X` and
  `Bs ≤ X`, let `X` normalize `N`, and let `Bs ∩ N = 1`. Let `H ≤ K` be
  subgroups whose traces on `X` split: every element of `K ⊓ X` is
  `b * n` with `b ∈ K ⊓ Bs` and `n ∈ K ⊓ N`, and likewise for `H`. Then
  `(H ⊓ X).relIndex (K ⊓ X) = (H ⊓ Bs).relIndex (K ⊓ Bs) *
  (H ⊓ N).relIndex (K ⊓ N)`.

  The proof uses the intermediate subgroup `Z = (H ⊓ Bs)(K ⊓ N)`,
  defined by its carrier. It is a subgroup because `H ⊓ Bs` normalizes
  `K ⊓ N`. It lies between `H ⊓ X` and `K ⊓ X`, so
  Mathlib's `Subgroup.relIndex_mul_relIndex` writes the index as
  `[Z : H ⊓ X] [K ⊓ X : Z]`. Every element `b n` of `Z` equals
  `(b n b⁻¹) b` with `b n b⁻¹ ∈ K ⊓ N` and `b ∈ H ⊓ X`, and
  `(H ⊓ X) ⊓ (K ⊓ N) = (H ⊓ N) ⊓ (K ⊓ N)`. So `[Z : H ⊓ X]` is
  `(H ⊓ N).relIndex (K ⊓ N)`, by `relIndex_eq_of_forall_mem_mul`. Every
  element of `K ⊓ X` is `b n` with `b ∈ K ⊓ Bs` and `n ∈ Z`. Since
  `Bs ∩ N = 1`, `Z ⊓ (K ⊓ Bs) = (H ⊓ Bs) ⊓ (K ⊓ Bs)`. So `[K ⊓ X : Z]` is
  `(H ⊓ Bs).relIndex (K ⊓ Bs)`, again by `relIndex_eq_of_forall_mem_mul`.
  These identities use Mathlib's natural-valued index, whose value is
  zero for an infinite quotient. The tower formula
  `Subgroup.relIndex_mul_relIndex` holds with this convention, so the
  lemma needs no finiteness hypothesis, and its intermediate indices may
  be infinite in general. In the application to compact open traces all
  indices are finite, because `K` is compact and `H` is open (the
  published `sourceTraceIndex_ne_zero`).
- `SplitTrace Y X L N` (definition): every element of `Y ⊓ X` is `b * n`
  with `b ∈ Y ⊓ (X ⊓ L)` and `n ∈ Y ⊓ N`.
- `relIndex_mul_eq_of_wall` (wall crossing for radical indices): let
  `U, U'` contain `N` and normalize it, let `V, V'` contain `N'` and
  normalize it, and let `L ∩ N = L ∩ N' = 1`. Assume
  `U ⊓ L = V' ⊓ L` and `V ⊓ L = U' ⊓ L`. If the traces of `H ≤ K` on
  `U, U'` split along `(L, N)` and those on `V, V'` split along
  `(L, N')`, then

  `[K ⊓ U : H ⊓ U] [K ⊓ V : H ⊓ V] = [K ⊓ U' : H ⊓ U'] [K ⊓ V' : H ⊓ V']`.

  Each of the four indices factors by `relIndex_inf_eq_mul` into a
  factor on the `L`-part and a factor on `N` or `N'`. The two identities
  exchange the `L`-parts, so both sides are the same product of four
  factors.

In the application, `U, V` are the radicals `U(χ), U(χ⁻¹)` of one
parabolic and `U', V'` are those of a parabolic with the same Levi on
the other side of the face of a cocharacter `φ` (see
`RationalSourceGammaWall`). `L` is the Levi of `φ`, and `N, N'` are the
radicals of `P(φ)` and of its opposite.
