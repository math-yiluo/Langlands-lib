# The limit homomorphism, its kernel and the Levi decomposition as morphisms of schemes

Let `G` be a group scheme over a scheme `S` whose structure morphism is separated, and let
`χ : 𝔾_{m,S} ⟶ G` be a cocharacter. Suppose the published dynamic subgroup functors
`P_G(χ)`, `Z_G(χ)` and `U_G(χ)` (`Dynamic.parabolic`, `Dynamic.centralizer`,
`Dynamic.unipotent`) are represented by group schemes `P`, `Z` and `U`. That is, there are
homomorphisms `iP : P ⟶ G`, `iZ : Z ⟶ G` and `iU : U ⟶ G` with the published
`SubgroupFunctor.IsRepresentedBy`. Representability holds, for example, for affine `G` over an
affine base (`Dynamic.Representability`) and for the diagonal cocharacters of `GL_n`.

Under these hypotheses the module proves the scheme-level structure:

1. The limit at zero is a homomorphism of group schemes `P ⟶ Z`. The inclusion `Z ⟶ P` is a
   section of it.
2. `U` is the scheme-theoretic kernel of this homomorphism, in the sense of the published
   group-scheme kernel `kernel` of `Langlands.AbelianScheme.Kernel`.
3. Multiplication `U ×_S Z ⟶ P`, `(u, z) ↦ u z`, is an isomorphism of schemes over `S`.

The published `Dynamic.LimitMap` proves the corresponding facts on the points over each test
scheme separately. This module assembles them into morphisms of schemes through the Yoneda lemma
of [`RepresentedSubgroup`](../RepresentedSubgroup.md).

## Sources

- Conrad, *Reductive group schemes* (2014), Theorem 4.1.7, p. 112, with proof on p. 113.
  - Part (1): `P_G(λ)`, `U_G(λ)` and `Z_G(λ)` are closed subgroups, with `U_G(λ)` normalized by
    `Z_G(λ)`. The proof (p. 113) describes `U_G(λ)` as "the fiber over 1 for the limit morphism
    `P_G(λ) → G` defined by `g ↦ lim_{t→0} t.g`".
  - Part (3): "The multiplication map `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an isomorphism."
- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015).
  - Lemma 2.1.5 and proof, printed pp. 50–51 (PDF pp. 76–77): `g ↦ lim_{t→0} t.g` is a
    multiplicative map `P_G(λ) → G`, "necessarily a `k`-group homomorphism, and its
    scheme-theoretic kernel is exactly the desired `U_G(λ)`".
  - Proposition 2.1.8(2), printed p. 53 (PDF p. 79): the multiplication map
    `Z_G(λ) ⋉ U_G(λ) → P_G(λ)` is an isomorphism of `k`-groups.

Differences from the sources:

- The sources state these results for affine groups over a ring (Conrad, and CGP 2.1.8 assumes
  finite presentation). Here `G` is a separated group scheme over any base. Representability of
  `P`, `Z` and `U` is a hypothesis; it is proved elsewhere for the affine case.
- The limit homomorphism lands in `Z`, using the published fact that limits lie in `Z_G(χ)`.
- The multiplication isomorphism is stated in the order `U ×_S Z`, matching the published
  `Dynamic.semidirectEquiv : U(T) ⋊ Z(T) ≃* P(T)` (Mathlib's `N ⋊ H` puts the normal factor
  first). It is proved as an isomorphism of schemes over `S`. The group structure on `U ⋊ Z` is
  not constructed as a group scheme; on points it is the published semidirect product.

## The limit homomorphism

Fix `hP` and `hZ`, the representability hypotheses of `P_G(χ)` and `Z_G(χ)`.

- `limitGroupHom hP hZ : P ⟶ Z` is `IsRepresentedBy.lift` of the published limit
  homomorphisms `Dynamic.limitHom χ T`. These are natural in `T` by `limitHom_comp`.
  `limitGroupHom_comp`: for a point `x` of `P`, `(x ≫ limitGroupHom) ≫ iZ` is the limit
  `Dynamic.limit χ` of the corresponding point of `P_G(χ)`.
- `centralizerToParabolic hP hZ : Z ⟶ P` is the inclusion, the `lift` of the inclusions
  `Z_G(χ)(T) ≤ P_G(χ)(T)`. `centralizerToParabolic_comp`: it commutes with the inclusions into
  `G`.
- `centralizerToParabolic_comp_limitGroupHom`: `Z ⟶ P ⟶ Z` is the identity. On the universal
  point of `Z`, the limit of a point of `Z_G(χ)` is itself (published
  `hasLimit_of_mem_centralizer` and `limit_eq`).

## The kernel

- `grp_comp_hom_hom`, `kernelι_comp_eq_one` and `exists_kernel_point` are small lemmas on the
  published kernel. A point of the kernel, followed by the inclusion, is killed by the
  homomorphism. Conversely, a point killed by the homomorphism factors through the kernel.
- `isRepresentedBy_kernel_limitGroupHom`: `U_G(χ)` is represented by
  `kernelι (limitGroupHom hP hZ) ≫ iP`. That is, a point of `G` lies in `U_G(χ)` exactly when
  it is a point of `P` whose limit is `1`. This uses the published `limit_eq_one_iff`
  (CGP Lemma 2.1.5 on points). The inclusion is a monomorphism as a composite of monomorphisms.
- `unipotentIsoKernel hU : U ≅ kernel (limitGroupHom hP hZ)`, for any group scheme `U`
  representing `U_G(χ)`. `unipotentIsoKernel_hom_comp`: it is compatible with the inclusions into
  `G`. This is `IsRepresentedBy.isoOfIsRepresentedBy`.

## The multiplication isomorphism

Fix also `hU`, the representability hypothesis of `U_G(χ)`.

- `multiplication hP hZ hU : U.X ⊗ Z.X ⟶ P.X` is the morphism over `S` corresponding to the point
  `(pr₁ ≫ iU) * (pr₂ ≫ iZ)` of `P_G(χ)` over `U ×_S Z`. `multiplication_comp` records this.
- `pointsEquiv_comp_multiplication`: on points over `T`, `w ↦ w ≫ multiplication` is the
  published `Dynamic.semidirectEquiv χ T` applied to the two components of `w`.
- `isIso_multiplication`: `multiplication` is an isomorphism. By Mathlib's
  `isIso_of_yoneda_map_bijective`, it suffices that composition with it is bijective on points
  over every `T`. That map is the bijective `semidirectEquiv`, composed with the point
  identifications of `U`, `Z` and `P` and with the pairing of maps into a product.
- `multiplicationIso : U.X ⊗ Z.X ≅ P.X` is the resulting isomorphism of schemes over `S`.

## Scope

Representability of `P_G(χ)`, `Z_G(χ)` and `U_G(χ)` is a hypothesis. Normality of `U` in `P` as
group schemes, finite presentation, smoothness and the opposite open cell (CGP 2.1.8(3)) are not
treated.
