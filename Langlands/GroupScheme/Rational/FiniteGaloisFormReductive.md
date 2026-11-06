# Connected reductivity of finite-Galois forms

Lean module: `Langlands.GroupScheme.Rational.FiniteGaloisFormReductive`, namespace
`Langlands.GroupScheme`.

This module proves `FiniteGaloisFormConnectedReductiveStatement` from
`Langlands.GroupScheme.Rational.FiniteGaloisFormReductiveStatement`. Let `L/K` be a finite
Galois extension, and let `G` and `H` be group schemes over `Spec K` with natural local group
isomorphisms `e : LocalGroupIso G H (Over.mk (Spec L → Spec K))`. If `G` is connected
reductive, then so is `H`.

## Declarations

Here `S, S'` are schemes, `G, H` are group schemes over `S`, and `U` is a scheme over `S`.

- `LocalGroupIso.basePoint b p T`: given `b : S' ⟶ S`, a point `p : Over.mk b ⟶ U` of the
  cover over `b`, and a scheme `T` over `S'`, this is the point
  `(Over.map b).obj T ⟶ U` of the cover over `T → S' → S`. It is the composite of
  `Over.homMk T.hom` with `p`.
- `LocalGroupIso.basePoint_naturality`: for `a : T' ⟶ T` over `S'`,
  `(Over.map b).map a ≫ basePoint b p T = basePoint b p T'`.
- `LocalGroupIso.baseChangeIso e b p`: the isomorphism
  `(GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H` defined by the local
  isomorphisms at the points `basePoint b p T`. On `T`-points over `S'` it is the composite
  of the pullback adjunction `baseChangePointsEquiv b G T`, which identifies `T`-points of
  `G_{S'}` with `(T → S' → S)`-points of `G`, then `e.toFun (basePoint b p T)`, then the
  inverse of `baseChangePointsEquiv b H T`. Naturality in `T` follows from
  `baseChangePointsEquiv_naturality`, `basePoint_naturality` and the naturality of `e`.
  The Library's `isoOfPoints` turns this natural family of multiplicative bijections into
  the isomorphism.
- `finiteGaloisFormConnectedReductive : FiniteGaloisFormConnectedReductiveStatement.{u}`.

## Proof of `finiteGaloisFormConnectedReductive`

Let `b : Spec L ⟶ Spec K` be the morphism `Spec.map (algebraMap K L)`. By
`fieldExtension_fpqc` it is surjective, flat and quasi-compact. Let
`eL := e.baseChangeIso b (𝟙 _)`, the isomorphism `G_L ≅ H_L` at the tautological point of the
cover. By `isIso_left_of_iso`, its underlying scheme morphism `H_L → G_L` is an isomorphism.
The structure morphism of `H_L` equals this isomorphism followed by the structure morphism
of `G_L` (`Over.w`). The four fields of `IsConnectedReductive H` are proved as follows.

1. **Smooth.** `G_L → Spec L` is the base change `pullback.snd G.X.hom b` of the smooth
   morphism `G.X.hom`, so it is smooth. Composing with the isomorphism shows that
   `pullback.snd H.X.hom b` is smooth. Mathlib's
   `MorphismProperty.of_pullback_snd_of_descendsAlong` descends smoothness along the
   surjective, flat, quasi-compact `b` (the `DescendsAlong` instance comes from
   `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`), so `H.X.hom` is smooth.
2. **Affine.** Since `G.X.hom` is affine and `Spec K` is affine, `G.X.left` is affine, and
   so is the pullback `G_L`. Hence `H_L = pullback H.X.hom b` is affine, by
   `IsAffine.of_isIso`. The Library theorem
   `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent` (affineness descends along
   field extensions) gives `IsAffine H.X.left`. A morphism between affine schemes is affine
   (Mathlib instance `isAffineHom_of_isAffine`).
3. **Connected.** `G` is smooth, affine and connected, so `G_L` is connected by
   `connectedSpace_baseChange_of_smooth_affine`. The homeomorphism
   `Scheme.homeoOfIso` of the isomorphism shows that `H_L` is connected. The projection
   `pullback.fst H.X.hom b : H_L → H` is surjective, as a base change of the surjective
   `b`. A continuous surjective image of a connected space is connected
   (`Function.Surjective.connectedSpace`), so `H.X.left` is connected.
4. **Trivial geometric unipotent radical.** `L/K` is algebraic, so `IsAlgClosed.lift` gives
   a `K`-algebra map `κ : L →ₐ[K] AlgebraicClosure K`. The morphism
   `Spec.map κ : Spec K̄ ⟶ Spec L` lies over `Spec K`, because `κ` commutes with the
   algebra maps (`κ.commutes`). So it is a point
   `p : Over.mk (toAlgebraicClosure K) ⟶ Over.mk b` of the cover over the geometric base
   change. Then `e.baseChangeIso (toAlgebraicClosure K) p : G_{K̄} ≅ H_{K̄}`. Applying
   `HasTrivialUnipotentRadical.of_iso` to its inverse and to the trivial radical of
   `G_{K̄}` gives the trivial radical of `H_{K̄}`.

Only the existence of a finite (hence algebraic) extension is used. The Galois hypothesis
`IsGalois K L` of the statement is not needed by the proof.

## Provenance

This is the descent argument named in the provenance of the statement: smoothness and
affineness descend along the fpqc cover `Spec L → Spec K`, connectedness passes from
`H_L ≅ G_L` to its image `H`, and an embedding of `L` into an algebraic closure identifies
the geometric unipotent radicals. The underlying definitions are those of Milne,
*Algebraic Groups* (2017): forms in Section 3.k, reductive groups in 6.46 and connectedness
in Summary 1.36. Steinberg (1965), Section 10, uses this fact when he applies 2.15 to a
twisted group. `LocalGroupIso.basePoint` and `LocalGroupIso.baseChangeIso` are internal
constructions written for this proof.
