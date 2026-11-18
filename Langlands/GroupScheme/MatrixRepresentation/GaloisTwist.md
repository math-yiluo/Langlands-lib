# Galois twists of representations of a scalar-extended group

This internal module defines the Galois twist of a finite free matrix
representation of `G_K = G ×_k K`, where `G` is a group scheme over a field
`k` and `K` is a `k`-algebra field. It also computes the twist on the test
points that come from points of `G` itself. The notation `ρ^σ` for the twist
is this module's own. The module is infrastructure for the Tits algebra of a
highest-weight representation. The motivation is the Galois descent of
representations in the proof of Theorem 3.3 of Tits, *Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*,
J. reine angew. Math. 247 (1971), pp. 203–204. Tits works with a projective
cocycle attached to a splitting isomorphism; the scheme-level twist and the
point formula below are this module's own constructions, not formulas from
that paper.

## Transport along an endomorphism of the base

Section `Transport` works over arbitrary schemes. It uses a morphism
`b : Spec R ⟶ B`, an endomorphism `a` of `Spec R` with `a ≫ b = b`, and a
group scheme `G` over `B`.

- `transport b a ha G ρ` moves a representation `ρ` of `G_R` along `a`. It is the
  composite of three morphisms. The first is the inverse of the published
  descent identification `descentBaseChangeIso b a ha G : a^*(G_R) ≅ G_R`. The
  second is the pullback `a^*ρ`. The third is the published identification
  `GeneralLinear.baseChangeIso n a : a^*GL_{n,R} ≅ GL_{n,R}`.
- `pointMatrix_transport` describes points. On a test scheme `T` over `Spec R`,
  the matrix of the transported representation at `y` is the matrix of `ρ` at
  the published `descentPoint b a ha G T y`, which lives over the test scheme
  `T` with its structure map composed with `a`. The proof writes `y` through
  the inverse descent isomorphism. It then uses the published compatibility
  `baseChangePointsEquiv_descent` together with
  `GeneralLinear.pointsEquiv_comp_baseChangeIso_hom` and
  `baseChangePointsEquiv_comp`.
- `descentPoint_eq_comp` gives a sufficient condition for a descended point to
  be the precomposite `Θ ≫ y`. Here `Θ : a_*T ⟶ T` is a morphism over
  `Spec R`. The condition is that both have the same underlying point of `G`
  over `B`. The proof uses injectivity of the published pullback-point
  equivalence and its naturality.
- `affineMatrix_transport_of_descentPoint` treats affine test algebras `S`. If
  the descended point is `Θ ≫ y` with `Θ.left = Spec θ`, then every entry of
  the transported representation's affine matrix at `y` is `θ` applied to the
  corresponding entry of `ρ`'s affine matrix. The proof compares the point and
  affine coordinates with the published `pointMatrix_eq_affineMatrix`. It then
  uses `pointMatrix_naturality` and Mathlib's
  `Scheme.ΓSpecIso_inv_naturality`, and cancels the injective inverse
  `Γ(Spec S) ≅ S` isomorphism.

## Galois twist

Fix fields `k ⊆ K`, `σ ∈ Aut_k(K)` and a group scheme `G` over `Spec k`.

- `galoisTwist σ ρ` is `transport` along the published `galoisBaseMap k K σ = Spec σ`,
  which lies over `Spec k` by `galoisBaseMap_over`. It is a representation of the
  same group `G_K` on the same coordinate space `K^n`.
- `scalarPoint R g` is defined for a commutative `k`-algebra `R` and a point
  `g ∈ G(R)`. It is the point of `G_K` over the `K`-algebra `K ⊗[k] R` obtained
  from `g` through the right tensor factor `R → K ⊗[k] R`, using the published
  `scalarExtensionPoint`.
- `galoisTensor R σ` is the `k`-algebra automorphism `σ ⊗ id` of `K ⊗[k] R`.
  `galoisTensorHom R σ` is `Spec (σ ⊗ id)`, a morphism of schemes over `Spec K`
  from the twisted test scheme `(Spec σ)_* Spec(K ⊗ R)` to `Spec(K ⊗ R)`.
  Its compatibility with structure maps is `(σ ⊗ id)(c ⊗ 1) = σ(c) ⊗ 1`.
- `descentPoint_scalarPoint` states that the descended scalar point is the
  scalar point precomposed with `Spec (σ ⊗ id)`. By `descentPoint_eq_comp`
  this reduces to an equality of morphisms over `Spec k`. That equality is
  checked on underlying schemes, where it is `(σ ⊗ id) ∘ includeRight =
  includeRight`.
- `affineMatrix_galoisTwist_scalarPoint` is the main formula:

  `(ρ^σ)(g)_{ij} = (σ ⊗ id)(ρ(g)_{ij})` in `K ⊗[k] R`,

  for every `k`-algebra `R` and `g ∈ G(R)` seen as a scalar point. On points
  that come from `G`, the twist thus acts on matrix entries by `σ ⊗ id`.
- `galoisTwist_eq_transport` and `galoisTensor_toRingHom_apply` are the
  definitional unfoldings that the last proof rewrites with. They keep the
  kernel from unfolding the large point coordinates.

The module has no hypotheses on `k`, `K` or `G`: no separability, Galois,
finiteness, smoothness or reducedness assumption.
