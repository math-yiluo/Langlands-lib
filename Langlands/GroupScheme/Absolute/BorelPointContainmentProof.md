# Proof that every rational point lies in a Borel subgroup

Author: Worker 1095.

The module proves

```
theorem Langlands.GroupScheme.borelPointContainment :
    BorelPointContainmentStatement.{u}
```

for the published proposition of
`Langlands.GroupScheme.Absolute.BorelPointContainmentStatement`, at an
arbitrary universe `u` and in every characteristic. Fix an algebraically
closed field `k : Type u` and a group scheme `G` over `Spec k` whose structure
morphism is smooth and affine and whose underlying space is connected. For
every rational point `g : Over.mk (𝟙 (Spec k)) ⟶ G.X`, the theorem gives a
group scheme `B`, a homomorphism `i : B ⟶ G` with `IsBorelSubgroup i`, and a
rational point `b` of `B` with `b ≫ i.hom.hom = g`.

The proof uses three helper modules, which are part of this contribution:

- `BorelPointContainmentDensity`: the conjugation map `conjugation j` of a
  homomorphism `j : H ⟶ G`, and Lemma A,
  `exists_isBorelSubgroup_of_denseRange`. If `conjugation j` has dense range
  and every rational point of `H` maps into a Borel subgroup of `G`, then
  every rational point of `G` lies in a Borel subgroup.
- `BorelPointContainmentTangent`: Lemma B,
  `isTangentSurjectiveAt_conjugation`, a Lie-algebra criterion for
  `conjugation j` to be surjective on rational tangent vectors at `(1, z₀)`.
- `BorelPointContainmentWeights`: a generic `k`-point `u` of `𝔾_m` for a
  cocharacter `χ` (`exists_generic_affinePoint`). Every Lie vector is then
  `Ad(χ(u))X − X + dι(ξ)` with `ξ` in the Lie algebra of the dynamic
  centralizer (`exists_adjoint_sub_add_eq`).

This module adds two lemmas, in the namespace
`Langlands.GroupScheme.BorelPointContainment`, and the target theorem.

## Density of the conjugation map of a dynamic centralizer

`denseRange_conjugation_centralizer`: let `k` be algebraically closed, `G`
smooth, affine and connected, `χ : (Gm (Spec k)).toGrp ⟶ G` a cocharacter,
and `iZ : Z ⟶ G` with `Z` smooth and affine and
`(Dynamic.centralizer χ).IsRepresentedBy iZ`. Then
`DenseRange (conjugation iZ).left`.

Proof. Since `k` is algebraically closed, it is infinite (Mathlib instance).
So `exists_generic_affinePoint` gives a generic `k`-point `u` of `𝔾_m`. The
range of `χ` lies in its own dynamic centralizer. This follows from the
Library results `torusCentralizer_gm_eq_dynamicCentralizer` and
`range_le_torusCentralizer`. So `χ = χ' ≫ iZ` with `χ' = hZ.factorHom χ _`.
Let `z₀` be the rational point `u⁻¹ ≫ χ'` of `Z`, with `u` transported to a
rational point along the identification `e` of `Spec k` with its
`CommAlgCat` form `P`. Then the constant point of `z₀ ≫ iZ` over `P` is
`(u ≫ χ)⁻¹`.

The product `G.X ⊗ Z.X` is smooth over `k` (`smooth_tensor`). `G.X.left` is
irreducible (`DynamicConnected.irreducibleSpace_of_smooth`), and `G.X` is
locally of finite type. The Library theorem `denseRange_of_isTangentSurjectiveAt`
then reduces density to tangent surjectivity of `conjugation iZ` at the
rational point `lift 1 z₀`. Lemma B reduces this to writing every
`W : lieKernel G k` as `C⁻¹ X C · dι(ξ) · X⁻¹`, where `C⁻¹ = χ(u)`. This is
`exists_adjoint_sub_add_eq` applied to `Additive.ofMul W`, translated back
to multiplicative notation by `adjoint_toMul` and
`lieKernelTargetLinear_toMul`.

## The central case

`isBorelSubgroup_id_of_forall_centralizer_eq_top`: let `k` be algebraically
closed and `G` smooth, affine and connected. If `Dynamic.centralizer χ = ⊤`
for every cocharacter `χ` of `G`, then `IsBorelSubgroup (𝟙 G)`.

Proof. Take a maximal torus `j₀ : T₀ ⟶ G`
(`TorusExistence.exists_isMaximalTorus`). It is split, because `k` is
algebraically closed (`isSplitTorus_of_finiteGaloisSplitting` with the Library
theorem `torusFiniteGaloisSplitting`). Every cocharacter `ν ≫ j₀` is central by
`isCentral_iff_dynamicCentralizer_eq_top`. Hence `j₀` is central by
`isCentral_of_forall_cocharacter`, which applies because `T₀` is split. The
Library theorem `IsMaximalTorus.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed`
makes `G` nilpotent, hence solvable
(`IsNilpotentGroupScheme.isSolvableGroupScheme`).

The identity is a closed immersion, and `G` is smooth and connected by its
instances. For maximality, let `i' : B' ⟶ G` be a closed subgroup and
`f : G ⟶ B'` with `f ≫ i' = 𝟙 G`. Then `i'` is a monomorphism (a closed
immersion), and `i' ≫ f = 𝟙 B'` by cancelling `i'`. So `f` is an
isomorphism with inverse `i'`, as `IsBorelSubgroup` requires.

## The main theorem

The proof is strong induction on the Lie dimension, via the Library principle
`smoothConnectedAffineGroup_lieDimension_induction`. It is applied to the
property "every rational point of `G` lies in a Borel subgroup of `G`" (the
conclusion of the target, for fixed `k`). Let `G` be smooth, affine and
connected, and assume the property for all such groups of smaller Lie
dimension.

1. If `Dynamic.centralizer χ = ⊤` for every cocharacter `χ`, the central
   case gives `IsBorelSubgroup (𝟙 G)`. Take `B = G`, `i = 𝟙 G` and `b = g`.
2. Otherwise choose `χ` with `Dynamic.centralizer χ ≠ ⊤`. Let
   `iZ = Dynamic.Affine.centralizerHom χ : Z ⟶ G` be the Library's affine
   representative of the dynamic centralizer (`G.X.left` is affine because
   `G.X.hom` is affine over `Spec k`). It represents the centralizer
   (`isRepresentedBy_centralizerHom`) and is a closed subgroup
   (`isClosedSubgroup_centralizerHom`), so `Z` is affine. `Z` is smooth by
   part 2 of the Library theorem `dynamicSmooth`. It is connected by the
   second part of the Library theorem `dynamicConnected`, which uses that
   `G` is connected.

   `iZ` is not an isomorphism. Otherwise every point of `G` would factor
   through `iZ`, and the centralizer would be `⊤`. Hence
   `Lie.dimension Z < Lie.dimension G`
   (`Lie.dimension_lt_of_proper_closedSubgroup`). By induction every
   rational point `h` of `Z` lies in a Borel subgroup `i' : B' ⟶ Z`. The
   composite `i' ≫ iZ` is a smooth connected solvable closed subgroup of `G`,
   so `BorelExistence.exists_isBorelSubgroup_containing` gives a Borel
   subgroup `i : B ⟶ G` and a factorization `f ≫ i = i' ≫ iZ`. Then the
   point `b' ≫ f` of `B` maps to `h ≫ iZ`. This is the hypothesis of
   Lemma A for `j = iZ`.

   `denseRange_conjugation_centralizer` gives the density hypothesis, and
   Lemma A (`exists_isBorelSubgroup_of_denseRange`) gives the conclusion
   for `g`.

## Use of the hypotheses

- `IsAlgClosed k`: rational points correspond to closed points, and
  Jacobson density is used (Lemma A). Algebraically closed fields are
  infinite (generic point of `𝔾_m`). Maximal tori are split (central case).
  `borelConjugacy` and `someBorelQuotientProper` require it.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`, `ConnectedSpace G.X.left`:
  required by the induction principle, the Borel conjugacy and quotient
  theorems, the irreducibility of `G` and the connectedness of the dynamic
  centralizer.

No reductivity is assumed. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## Comparison with the literature

The target is the first sentence of Milne, *Algebraic Groups* (2022
corrected reprint, registered source `milne-2022-algebraic-groups`),
Corollary 17.34, printed p.362 (PDF p.373), for affine `G`. Milne deduces it
from Theorem 17.33(b), `|G| = ⋃ g|B|g⁻¹`. That theorem combines the closedness
in Lemma 17.32(a) with the density of the conjugates of `C_G(T)`
(Theorem 17.33(a), via Lemma 17.32(b) and a dimension count).

The Lean proof keeps the closedness argument (Lemma A, see
`BorelPointContainmentDensity.md`) but obtains density differently. It
replaces `C_G(T)` by the dynamic centralizer `Z_G(χ)` of a noncentral
cocharacter and proves density of its conjugates by tangent surjectivity.
Instead of Milne's appeal to the structure of `C_G(T)`, it then applies the
induction hypothesis to `Z_G(χ)`, which has smaller dimension. When every
cocharacter is central, `G` is nilpotent and is its own Borel subgroup.
