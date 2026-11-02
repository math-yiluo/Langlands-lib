# Maximal tori, normalizing points and the Weyl action

Worker 274.

This module defines maximal tori of group schemes over a field, normalizing and
centralizing base points of a homomorphism `i : T ⟶ G` from a commutative group
scheme, the Weyl action of the normalizer on characters, and its image. It
proves that normalizing points carry weight spaces onto weight spaces through
the adjoint representation, so the Weyl action permutes the roots.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- Corollary 17.84, printed p.379 (PDF 395), and Example 17.88, printed p.380
  (PDF 396). Milne's maximal tori are tori not properly contained in a larger
  torus. Corollary 17.84 characterises them in a reductive group by
  `C_G(T) = T`, and Example 17.88 shows that the diagonal torus `D_n` is
  maximal in `GL_n`.
- §21.a with Proposition 21.1, printed p.424 (PDF 440): the Weyl group
  `W(G, T) = N_G(T)/C_G(T)` with `W(G, T)(k) = N(k)/T(k)`, acting on `X(T)`.
- Proposition 21.2 and its proof, printed p.425 (PDF 441): for `n ∈ N_G(T)(k)`
  representing `s`, `(sχ)(t) = χ(n⁻¹ t n)`, and `g_{sα} = s g_α`, so `s`
  permutes the roots.

Milne works with algebraic groups over a field and with subgroups. Here
normalizers and centralizers are subgroups of the base points
`G(S) = (Over.mk (𝟙 S) ⟶ G.X)` attached to a homomorphism `i` over an arbitrary
base scheme `S`. The weight-space lemma is stated over an arbitrary affine base
`Spec R`. These generalisations are **derived**.

## Maximal tori

For a field `k` and `S = Spec k`, `IsMaximalTorus i` for `i : T.toGrp ⟶ G`, with
`T : CommGroupScheme S` and `G : GroupScheme S`, says three things:

- `IsTorus T.toGrp`;
- `IsClosedSubgroup i`, the published closed-immersion condition;
- for every commutative `T'` with `IsTorus T'.toGrp`, every `i' : T'.toGrp ⟶ G`
  with `IsClosedSubgroup i'`, and every `f : T.toGrp ⟶ T'.toGrp` with
  `f ≫ i' = i`, the map `f` is an isomorphism (`IsIso f`).

This is Milne's notion of a torus not properly contained in a larger torus,
expressed through homomorphisms.

## Inner automorphisms by base points

The group laws of inner automorphisms come from the imported module
`Langlands.GroupScheme.InnerAutomorphismHom`: `innerIso_one_hom`,
`innerIso_mul_hom` (`int(g h) = int(h) ≫ int(g)` in diagrammatic order) and
`innerIso_inv_hom`, together with `constantPoint_inv`.

## Normalizing points and the Weyl action

Over any base scheme `S`, take `i : T.toGrp ⟶ G` with `T : CommGroupScheme S`.

- `IsNormalizingPoint i n σ`, for `n : Over.mk (𝟙 S) ⟶ G.X` and `σ : T ≅ T`, is
  `i ≫ (innerIso G n).hom = σ ≫ i`, where `σ` is read as a group-scheme
  homomorphism through `CommGroupScheme.groupHom`. On points this says
  `n i(t) n⁻¹ = i(σ t)`. It is closed under products (`IsNormalizingPoint.mul`,
  with `τ ≪≫ σ`) and inverses (`IsNormalizingPoint.inv`, with `σ.symm`), and
  `1` normalizes through `Iso.refl` (`IsNormalizingPoint.one`).
- `normalizerPoints i` is the subgroup of `G(S)` of the `n` that normalize
  through some `σ`. `centralizerPoints i` is the subgroup of the `n` that
  normalize through `σ = Iso.refl T`. Equivalently (`mem_centralizerPoints`),
  `i ≫ (innerIso G n).hom = i`. Also
  `centralizerPoints_le_normalizerPoints`.
- `normalizingAut i n` is a chosen `σ` for `n ∈ normalizerPoints i`. If the
  underlying morphism of schemes `i.hom.hom.left` is a monomorphism, `σ` is
  unique (`IsNormalizingPoint.unique`).
- `characterAut σ : characterLattice T ≃ₗ[ℤ] characterLattice T` is
  `χ ↦ σ⁻¹ ≫ χ`.
- `weylAction i : normalizerPoints i →* (characterLattice T ≃ₗ[ℤ] characterLattice T)`,
  for `[Mono i.hom.hom.left]`, sends `n` to `χ ↦ σ⁻¹ ≫ χ`, where `σ` is the
  unique automorphism through which `n` normalizes `i` (`weylAction_apply`,
  `weylAction_eq`). It is a homomorphism by uniqueness of `σ` and
  `IsNormalizingPoint.mul`. On points `(σ⁻¹ ≫ χ)(t) = χ(σ⁻¹ t) = χ(n⁻¹ i(t) n)`,
  which is Milne's rule `(sχ)(t) = χ(n⁻¹ t n)`.
- `weylImage i := (weylAction i).range`.

## Normalizing points permute weight spaces and roots

Over an affine base `Spec R` with `IsAffineHom G.X.hom`:

- `basePointAdjoint n` is `adjoint G R` applied to the `R`-point given by
  `constantPoint n`, an `R`-linear endomorphism of `Lie(G)(R)`. The lemmas
  `basePointAdjoint_inv_mul` and `basePointAdjoint_mul_inv` say that the actions
  of `n⁻¹` and `n` are inverse to each other.
- `IsNormalizingPoint.adjoint_mem_weightSpace`: if `n` normalizes `i` through
  `σ` and `X ∈ weightSpace i χ`, then `Ad(n) X ∈ weightSpace i (σ⁻¹ ≫ χ)`. The
  proof works over each test algebra `A`. It uses naturality of `adjoint` in
  `A` and the point identity `i(t) = n_A i(σ⁻¹ t) n_A⁻¹`, which comes from
  `comp_innerIso_hom`. Then `Ad(i(t)) Ad(n_A) X_A = Ad(n_A) Ad(i(σ⁻¹ t)) X_A =
  χ(σ⁻¹ t) Ad(n_A) X_A`.
- `IsNormalizingPoint.map_weightSpace`: `Ad(n)` maps `weightSpace i χ` onto
  `weightSpace i (σ⁻¹ ≫ χ)`. The reverse inclusion applies the previous lemma
  to `n⁻¹` and `σ.symm`.
- `weightSpace_eq_bot_iff_of_isNormalizingPoint`: one of these weight spaces is
  zero if and only if the other is, because `Ad(n)` is injective.
- `map_weightSpace_weylAction`: for `[Mono i.hom.hom.left]` and
  `n ∈ normalizerPoints i`, `Ad(n)` maps `weightSpace i χ` onto
  `weightSpace i (weylAction i n χ)` (Milne 21.2, `g_{sα} = s g_α`).
- `weylAction_mem_roots_iff`: `weylAction i n χ ∈ roots i ↔ χ ∈ roots i`, so
  the Weyl action permutes the roots.
