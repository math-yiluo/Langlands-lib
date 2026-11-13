# The roots of a split adjoint group span its character lattice

This module proves two theorems in the namespace `Langlands.GroupScheme`.

## `IsCentralIsogeny.isIso_of_center_eq_bot`

Let `S` be any scheme, `G` and `H` group schemes over `S`, and `φ : G ⟶ H` a central
isogeny (`IsCentralIsogeny φ`). If the scheme-theoretic centre of `G` is trivial
(`center G = ⊥`), then `φ` is an isomorphism (`IsIso φ`).

Proof. `φ` is a monomorphism on points. If `a ≫ φ = b ≫ φ`, then `(a / b) ≫ φ = 1`. The
Library lemma `IsCentralIsogeny.mem_center_of_comp_eq_one` puts `a / b` in the centre, which
is trivial, so `a = b`. Hence the underlying scheme morphism of `φ` is a monomorphism. It is
also finite, flat and surjective, since `φ` is an isogeny. Mathlib's
`Flat.isIso_of_surjective_of_mono` makes it an isomorphism of schemes. Then
`Over.forget` reflects isomorphisms, and `Grp.mkIso'` lifts the isomorphism to group objects.

## `IsAdjoint.rootSpan_eq_top`

Let `k` be a field and `G` a group scheme over `Spec k` with `IsAdjoint G`. Let `T` be a
commutative group scheme with `IsSplitTorus T.toGrp` and `i : T.toGrp ⟶ G` a maximal torus
(`IsMaximalTorus i`). Let `J` be a finite type and `P : RootDatum J X^*(T) X_*(T)` a reduced
root datum of `i` (`IsRootDatumOf i P` and `P.IsReduced`). Then the roots of `P` span
`X^*(T)` over `ℤ`: `P.rootSpan ℤ = ⊤`. The affineness instance needed to state
`IsRootDatumOf` is taken from the connected reductive structure of the adjoint group.

Proof.

1. `G` is semisimple, so the Library theorem `splitSemisimpleRootDatum` shows that
   `X^*(T) / ℤR` is finite, where `ℤR = P.rootSpan ℤ`.
2. The Library's `splitReductiveExistence` provides a split connected reductive group `G'`
   with split maximal torus `i' : T' → G'` and a root datum `Q` of `i'`, together with an
   isomorphism `e` from `Q` to the adjoint root datum `AdjointRootDatum.rootDatum P` of
   `Langlands.LinearAlgebra.AdjointRootDatum`.
3. `f = AdjointRootDatum.fromRootDatum P ∘ e⁻¹ : Q → P` is a morphism of root data. Its weight
   map is injective because the inclusion `ℤR → X^*(T)` is. Its coweight map is injective by
   `injective_fromRootDatum_coweightMap`, using step 1. The Library's
   `splitCentralIsogenyExistence` then gives a central isogeny `φ : G → G'` and a torus map
   `t : T → T'` with `i ≫ φ = t ≫ i'`, whose map on characters is `f.weightMap`.
4. The centre of an adjoint group is trivial, so `φ` is an isomorphism by the first theorem.
   The Library lemma `IsMaximalTorus.isIso_factor_of_isIso` then makes `t` an isomorphism.
5. Every character `χ` of `T` equals `f.weightMap (t⁻¹ ≫ χ)`. That value lies in the image of
   the inclusion `ℤR → X^*(T)`, so `χ ∈ ℤR`.

## Provenance

The statement is the standard fact that the root lattice of a split adjoint group is its
whole character lattice: an adjoint group has the adjoint root datum `(ℤR, R, Hom(ℤR, ℤ), R^∨)`.
The proof above is internal and uses the Library's existence and isogeny theorems for split
reductive groups. It was written for the proof of
`QuasiSplitAdjointSimpleRootTransitivityStatement`. There it is applied over a finite Galois
splitting field of the centralizer torus.
