# Conjugacy of maximal tori in triangular solvable groups

This module proves conditional forms of two results of Milne 2017 about a
smooth connected solvable group `H` over an algebraically closed field `k`:

- conjugacy of maximal tori, compare Theorem 16.27(b);
- the semidirect product decomposition `H = U ⋊ T` for a maximal torus `T`,
  Theorem 16.33(d), in the form of the published
  `SolvableMaximalTorusSemidirectStatement`.

Both final theorems assume two published propositions: the split torus
quotient `SolvableTorusQuotientStatement` (Milne 16.33(a),(c)) and its
homomorphic section `SolvableSplitExtensionStatement` (Milne 16.26(a)). They
do not assume any conjugacy statement. The module does not prove either
premise.

The core is a matrix result (`TriangularLayer.exists_conj_of_hom`). Two
natural families of upper triangular homomorphisms from the points of a
split torus that agree modulo unitriangular matrices are conjugate. The
conjugating matrix can be chosen in any subgroup `𝒱 ⊆ GL_N(k)` that contains
their quotients at the rational points and is normalized by one of them. The
proof is the layer-by-layer averaging of the published
`Absolute/TriangularTorusLift`, with each correction chosen inside `𝒱`.

## Matrix conjugacy

In the namespace `Langlands.GroupScheme.TriangularLayer`, for a field `k`, a
type `I` and `N : ℕ`. The notation is that of the published modules
`Absolute/TriangularLayerFiltration` and `Absolute/TriangularTorusLift`:
`W A N a` is the `a`-th term of the superdiagonal filtration of `GL_N(A)`
(`W A N 0` is the upper unitriangular group), `upper A N` is the upper
triangular group, `layer`, `layerGroup`, `Rel` and `Approx` are the layer
calculus, and `TorusLift` is a natural family of triangular lifts of the
points of `𝔾ₘ^I` with its `correction` and `deviation`.

- `approx_bot_iff`: `Approx ⊥ a g` holds exactly when `g ∈ W A N a`.
- `layer_map_coeff`: taking the constant Laurent coefficient of each entry
  commutes with taking the `a`-th layer of a matrix over
  `AddMonoidAlgebra k (I → ℤ)`.
- **`TorusLift.ofHom k I N S hnat hup : TorusLift k I N`** (a `def`): a
  family `S A : (I → Aˣ) →* GL_N(A)` of monoid homomorphisms, natural in the
  `k`-algebra `A` (`hnat`) and upper triangular (`hup`), viewed as a lift
  with trivial kernel `⊥`. The `TorusLift` axioms hold because `S A` is
  multiplicative.
- `TorusLift.correction_mul_right`: the correction by `x * v` is the
  correction by `x` conjugated by the image of `v`.
- `TorusLift.approx_succ_of_layer`: one induction step along the filtration.
  Assume `k` is algebraically closed, `I` is finite, `x ∈ W k N 0`, the
  deviation of the lift at `x` is in `kernel · W a` at every point, and `C`
  is related to the deviation at the universal Laurent family `laurentVar`.
  If `z ∈ W k N a` has the same `a`-th layer as the constant coefficients of
  `C`, then the deviation at `x * z` is in `kernel · W (a + 1)` at every
  point. The proof is that of the published `TorusLift.exists_approx_succ`,
  for a correction `z` that is prescribed only through its layer.
- **`exists_conj_of_hom`**: assume `k` is algebraically closed and `I` is
  finite. Let `S, P` be two families `S A, P A : (I → Aˣ) →* GL_N(A)`, both
  natural in `A`, with `P A t` upper triangular and `(P A t)⁻¹ * S A t`
  unitriangular for all `A` and `t`. Let `𝒱` be a subgroup of `GL_N(k)` with
  `(P k t)⁻¹ * S k t ∈ 𝒱` and `(P k t)⁻¹ * v * P k t ∈ 𝒱` for all
  `t : I → kˣ` and `v ∈ 𝒱`. Then there is `v ∈ 𝒱` with
  `S A t = v⁻¹ * P A t * v` for all `A` and `t`, where `v` acts through
  `algebraMap k A`.

  Proof: `S` is upper triangular too. Apply the published
  `TorusLift.exists_deviation_mem` to `TorusLift.ofHom P`. It gives a
  unitriangular `y` whose correction of `P` is `P` itself; since `S` and `P`
  have the same diagonal part, the correction of `S` by `y` is also `P`. So
  the deviation of `S` at `y * v` is `(v⁻¹ P v)⁻¹ S`. At the rational points
  it lies in `𝒱` when `v ∈ 𝒱`, by the two hypotheses on `𝒱`. By induction on
  `a`, there is `v ∈ 𝒱 ∩ W k N 0` whose deviation lies in `W A N a` at every
  point. The step takes the deviation `C` at the universal family. The
  constant coefficients of its `a`-th layer lie in `layerGroup 𝒱 a`, by the
  published `splitTorus.map_coeff_zero_mem` (every evaluation is the layer of
  a deviation at a rational point, which lies in `𝒱 ∩ W k N a`). So they are
  the layer of some `z ∈ 𝒱 ∩ W k N a`, and `approx_succ_of_layer` gives the
  step for `v * z`. At `a = N` the deviation is `1`
  (`eq_one_of_mem_W_top`), which is the conclusion.

## Scheme adapter

Still in `TriangularLayer`, with `matrixOf`, `torusPoint` and `upperScheme`
from the published `Absolute/TriangularSplitExtension`. Write
`𝔻 = splitTorus (Spec k) I`, and let `i : U ⟶ H` and
`j : H ⟶ upperScheme k N` be homomorphisms of group schemes over `Spec k`.

- `specOf_self_hom`, `specOf_self_hom_ext`: `Spec k`, as the affine test
  scheme `specOf k`, has the identity structure morphism and is terminal
  over the base.
- `baseTest` (a `def`): the morphism from the base `Over.mk (𝟙 (Spec k))` to
  `specOf k`. `constantPoint_baseTest`: for a rational point `g` of `H`, the
  constant point of `baseTest ≫ g` over `Spec A` is the image of `g` under
  `Algebra.ofId k A`.
- `pointMatrix I j ρ A` (a `def`): for `ρ : 𝔻 ⟶ H`, the homomorphism
  `t ↦ matrixOf j A (torusPoint I A t ≫ ρ)` from `I → Aˣ` to `GL_N(A)`.
  `pointMatrix_naturality` and `pointMatrix_mem_upper` say that it is natural
  in `A` and upper triangular.
- `matrixOf_mem_W_of_mem_range`: if `U` is unipotent, the matrix of a point
  of the range of `i` is unitriangular. The composite of `i ≫ j` with the
  published diagonal map `GeneralLinear.blockLimitHom` onto a split torus is
  trivial, by the published `IsUnipotent.comp_eq_one_of_isSplitTorus`.
- **`exists_innerIso_of_triangular`**: assume `k` is algebraically closed,
  `I` is finite, `Mono j.hom.hom`, `U` is unipotent and the range of `i` is
  normal. Let `ρ, ρ' : 𝔻 ⟶ H` be such that `(x ≫ ρ)⁻¹ * (x ≫ ρ')` lies in
  the range of `i` for every point `x` of `𝔻` over every test scheme. Then
  there is a rational point `g` of `H` with `ρ ≫ (H.innerIso g).hom = ρ'`.

  Proof: apply `exists_conj_of_hom` to `S = pointMatrix ρ'` and
  `P = pointMatrix ρ`, with `𝒱` the image under `matrixOf j k` of the
  rational points of the range of `i`. The hypotheses on `𝒱` come from the
  hypothesis on `ρ, ρ'` and from normality of the range. The resulting `v`
  is the matrix of a rational point `g₀` of the range, and `g = g₀⁻¹`. Both
  sides of the claimed equation are homomorphisms out of the affine group
  `𝔻`. They agree on affine points, by injectivity of `matrixOf j`
  (`Mono j.hom.hom`) and the published `comp_innerIso_hom`. So they are
  equal, by `Grp.hom_ext` and the published `affine_hom_ext`.

## Maximal tori

In the namespace `Langlands.GroupScheme`. Let `k` be algebraically closed,
`H` a smooth connected affine group scheme over `Spec k`,
`i : U ⟶ H` and `q : H ⟶ D` homomorphisms. The hypothesis
`hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i` says that
the scheme kernel of `q` and the range of `i` have the same points.

- `subgroupConjugate_of_comp_eq_of_isUnipotent`: assume `H` is solvable, `U`
  is unipotent, the range of `i` is normal and `hq`. Let `T` be a torus and
  `s, s' : T ⟶ H` with `s ≫ q = s' ≫ q`. Then `SubgroupConjugate s s'`: `s'`
  is `s` followed by an inner automorphism of `H` by a rational point.
  Proof: the published `solvableTriangularEmbeddingStatement` (Lie–Kolchin)
  gives a closed immersion `j : H ⟶ upperScheme k N`. `T` is split over the
  algebraically closed `k`, by `IsTorus.isSplitTorus_of_finiteGaloisSplitting`
  with the published `torusFiniteGaloisSplitting`, so `T ≅ 𝔻` for a finite
  `I`. The quotient of the two points lies in the scheme kernel of `q`, hence
  in the range of `i` by `hq`; `exists_innerIso_of_triangular` concludes.
- `isIso_comp_of_section_of_isUnipotent`: under the same hypotheses, if `D`
  is a split torus and `σ : D ⟶ H` satisfies `σ ≫ q = 𝟙 D`, then `s ≫ q` is
  an isomorphism for every maximal torus `s : T ⟶ H`. This is the published
  `IsMaximalTorus.isIso_comp_of_torus_section`, whose equal-composite
  conjugacy input is the previous theorem.
- `maximalToriAreConjugate_of_section_of_isUnipotent`: under the hypotheses
  of the previous item, `MaximalToriAreConjugate H`. For maximal tori `s, s'`,
  both `s ≫ q` and `s' ≫ q` are isomorphisms, so
  `s' ∘ (s' ≫ q)⁻¹ ∘ (s ≫ q)` has the same composite with `q` as `s`, and
  the first theorem applies to it.
- **`maximalToriAreConjugate_of_solvableTorusQuotient`**: from
  `SolvableTorusQuotientStatement.{u}` and
  `SolvableSplitExtensionStatement.{u}`, every smooth connected affine
  solvable group `B` over an algebraically closed field `k : Type u`
  satisfies `MaximalToriAreConjugate B`. The conclusion is exactly the
  premise `hsolvable` of the published
  `maximalTorusConjugacyStatement_of_borelConjugacy`. The first premise gives
  `U`, `D`, `i`, `q`; the second gives the section `σ`; `hq` is part of the
  fppf quotient hypothesis.
- **`solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient`**:
  `SolvableTorusQuotientStatement.{u} → SolvableSplitExtensionStatement.{u} →
  SolvableMaximalTorusSemidirectStatement.{u}`. For a maximal torus `s`, the
  same `U` and `i` are the unipotent part. `s ≫ q` is an isomorphism by
  `isIso_comp_of_section_of_isUnipotent`, so the multiplication map is an
  isomorphism by the published `isIso_subgroupMultiplication_of_isIso_comp`
  and `isIso_subgroupMultiplication_reverse_iff`. Every unipotent closed
  subgroup lies in the range of `i`, by the published
  `range_le_of_isUnipotent_of_isSplitTorus`.

## Provenance

The module is derived. Its targets correspond to Milne, *Algebraic Groups*
(2017), source `milne-2017-algebraic-groups`:

- Theorem 16.27(a),(b), printed p. 333 (zero-based PDF page 348): for a
  trigonalizable group `G` over an algebraically closed field with quotient
  `q : G → D` by `G_u`, any two homomorphic sections of `q` are conjugate by
  an element of `G_u(k)`, and the maximal diagonalizable subgroups are the
  images of sections, all conjugate. `subgroupConjugate_of_comp_eq_of_isUnipotent`
  is a form of 16.27(a) for homomorphisms from a torus with the same
  composite with `q`, and `maximalToriAreConjugate_of_solvableTorusQuotient`
  is the torus case of 16.27(b) for smooth connected solvable groups.
- Theorem 16.33(d), printed pp. 335–336 (PDF pages 350–351): for `k`
  algebraically closed and `T` a maximal torus, `G = G_u ⋊ T`. The published
  statement `SolvableMaximalTorusSemidirectStatement` records this part.
- Theorem 16.26(a), printed p. 332 (PDF page 347), is used only through the
  premise `SolvableSplitExtensionStatement`.

The route differs from Milne's. Milne proves 16.27(a) by induction along the
normal series of `G_u` of Theorem 16.21, using `H¹(D, N) = 0` for its last
term `N` (15.3). He deduces 16.27(b) from 16.27(a) and Theorem 16.26. Here `H` is
embedded in the upper triangular group by Lie–Kolchin. The homomorphisms are
compared at the level of matrices, and the induction runs along the
superdiagonal filtration of the unitriangular group. Each layer is corrected
by torus averaging, the constant Laurent coefficient of the deviation at the
universal family. The correction is constrained to the matrices of rational
points of the unipotent subgroup. The conjugating matrix is the matrix of a
rational point of the range of `i`, as in Milne; the Lean statements assert
only a rational point of `H` (`SubgroupConjugate`).
