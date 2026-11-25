# Reducing the closed embedding of the normalizer quotient to universal closedness

This module defines the descended conjugacy map
`Langlands.GroupScheme.SelfCentralizingConjugacyClosedEmbeddingReduction.conjugacyQuotientMap`.
It also proves
`Langlands.GroupScheme.SelfCentralizingConjugacyClosedEmbeddingReduction.selfCentralizingConjugacyClosedEmbedding_of_universallyClosed`:

> `SelfCentralizingConjugacyUniversallyClosedStatement.{u}` implies
> `SelfCentralizingConjugacyClosedEmbeddingStatement.{u}`.

The two statements have the same hypotheses. The closed-embedding statement
asserts that the conjugacy map `f : G.X ⟶ M`, `g ↦ ρ(g) e(D) ρ(g)⁻¹`, factors
through the normalizer quotient `p : G.X ⟶ Y` as a closed immersion. The
universal-closedness statement asserts only that every factorization
`φ : Y ⟶ M` of `f` through `p` is universally closed. The module supplies the
rest: the descent of `f`, and the monomorphism property and local finite type
of the descended map. It adds no geometric input. It uses the Library's descent
along effective epimorphisms (`HomogeneousQuotientComparison.desc`), Mathlib's
instance making fppf morphisms effective epimorphisms
(`Mathlib.AlgebraicGeometry.Sites.Fpqc`), the Library's descent of local finite
type along fppf morphisms of the source
(`Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`,
Stacks Project, Tag 02KL), and Mathlib's
`IsClosedImmersion.iff_isProper_and_mono`.

## Descent along fppf morphisms

Throughout, "fppf" means that the underlying scheme morphism is flat,
surjective and locally of finite presentation. All morphisms live in `Over S`.

- `epi_of_fppf`: an fppf morphism is an epimorphism (Mathlib's `EffectiveEpi`
  instance and `Over.epi_of_epi_left`).
- `exists_factor_of_fppf`: let `c : V ⟶ U` be fppf and `m : Z ⟶ X` a
  monomorphism. If `c ≫ y` factors through `m` as `z ≫ m`, then `y` factors
  through `m`. The map `z` is constant on the fibres of `c`, because `m` is a
  monomorphism, so `HomogeneousQuotientComparison.desc c z` exists. Cancelling
  the epimorphism `c` gives the factorization.
- `exists_fppf_lift`: a point `d : U ⟶ B` lifts through an fppf map
  `q : A ⟶ B` after the fppf base change `pullback.fst d.left q.left`.
- `exists_factor_of_lift`: to factor `y : U ⟶ X` through a monomorphism `m`, it
  suffices to do so after every base change `c` along which `d` lifts through
  `q`. This combines the two previous lemmas.
- `hom_ext_of_fppf_lift`: two maps out of `T` are equal if they agree after the
  base change along which a point `T ⟶ Q` lifts through an fppf map `X ⟶ Q`.
- `mono_desc_of_fppf_fiber_iff`: let `q : X ⟶ Q` be fppf and `r : X ⟶ R`. If
  `a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r` on every test object, then the underlying
  morphism of the descended map `desc q r` is a monomorphism of schemes. Given
  `a, b : T ⟶ Q` with `a ≫ desc q r = b ≫ desc q r`, lift `a` and then `b`
  through `q` after two fppf base changes. The lifts have the same image under
  `r`, hence under `q`. Apply `hom_ext_of_fppf_lift` twice. Finally
  `Over.mono_left_of_mono` passes from `Over S` to schemes.

## The normalizer of `T` and the normalizer of the image torus

Let `ρ : G ⟶ L` be a homomorphism of group schemes over `S` with central
kernel. Let `t : T ⟶ G` represent its own centralizer, and let
`π ≫ e = t ≫ ρ` with `π : T ⟶ D` fppf and `e : D ⟶ L` a monomorphism.

- `exists_torus_point_of_comp_eq` (preimage of the image torus): if a point
  `y` of `G` satisfies `ρ(y) = e(d)` for a point `d` of `D`, then `y` is a point
  of `T`. By `exists_factor_of_lift`, it suffices to work after lifting `d` to a
  point `a` of `T` with `π(a) = d`. Then `k = y · t(a)⁻¹` lies in the kernel of
  `ρ`. Being central, `k` centralizes `T`, so `k = t(τ₁)` because `t`
  represents the centralizer. Hence `y = t(τ₁ · a)`.
- `comp_mem_normalizer_of_mem_torusNormalizer`: if `x` normalizes `T`, then
  `ρ(x)` normalizes `e(D)`. Given a point `e(d)`, lift `d` to `T` after an fppf
  base change. Conjugation by `x` preserves `T`, so `ρ(x) e(d) ρ(x)⁻¹` lies in
  `e(π(T)) ⊂ e(D)` there, and `exists_factor_of_lift` descends this. The same
  argument applies to `ρ(x)⁻¹ e(d) ρ(x)`.
- `mem_torusNormalizer_of_comp_mem_normalizer`: conversely, if `ρ(x)`
  normalizes `e(D)`, then `x` normalizes `T`. For a point `τ` of `T`, the
  conjugate `x t(τ) x⁻¹` maps under `ρ` into `e(D)`. By
  `exists_torus_point_of_comp_eq` it is a point of `T`, and similarly for
  `x⁻¹ t(τ) x`.
- `comp_eq_iff_mem_torusNormalizer` (fibres of the conjugacy map): let
  `j : K ⟶ L_M` be a universal family of closed subtori of `L` and let
  `f : G.X ⟶ M` classify the family `g ↦ ρ(g) e(D) ρ(g)⁻¹`. Then
  `g ≫ f = h ≫ f ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U`. Two points of `M`
  are equal exactly when their evaluated families are, by the uniqueness clause
  of `TorusSubgroupModuli.IsUniversal` with
  `TorusSubgroupModuli.isAdmissible_evaluate`. The family evaluated at `g ≫ f` is
  `ρ(g) e(D) ρ(g)⁻¹`, by `TorusSubgroupModuli.evaluate_comp`,
  `TorusSubgroupModuli.evaluate_eq_of_range_eq` and
  `SubgroupFunctor.evaluate_conjugateFamily`. By
  `SubgroupFunctor.range_conjugateFamily_eq_iff`, two such families are equal
  exactly when `ρ(g⁻¹ h)` normalizes `e(D)`. The two previous lemmas identify
  this with `g⁻¹ h` normalizing `T`.

## The definition

`conjugacyQuotientMap ρ t π e hρ hcent he hπe j hj hK huni f hf p hp : Y ⟶ M`
takes the data of `comp_eq_iff_mem_torusNormalizer` together with an fppf
`p : G.X ⟶ Y` whose fibres are exactly the cosets of the normalizer of `T`
(`hp`). It is `HomogeneousQuotientComparison.desc p f`. The map `f` is constant
on the fibres of `p`, because `hp` and `comp_eq_iff_mem_torusNormalizer` both
describe them as normalizer cosets. The map sends the class of `g` to the
parameter of `ρ(g) e(D) ρ(g)⁻¹`, and `p ≫ conjugacyQuotientMap … = f`
(`HomogeneousQuotientComparison.fac_desc`).

## The main theorem

`selfCentralizingConjugacyClosedEmbedding_of_universallyClosed` takes the
universal-closedness statement `hP` and the hypotheses of the closed-embedding
statement.

1. `e` is a closed immersion, so `e.hom.hom` is a monomorphism
   (`Over.mono_of_mono_left`).
2. `hp` and `comp_eq_iff_mem_torusNormalizer` show that `p` and `f` have the same
   fibres on every test object.
3. `φ = conjugacyQuotientMap …` satisfies `p ≫ φ = f`.
4. `φ.left` is a monomorphism by `mono_desc_of_fppf_fiber_iff`, hence
   separated (Mathlib's instance `isSeparated_of_mono`).
5. `φ.left` is universally closed by `hP`, applied to `φ`.
6. `φ.left` is locally of finite type. `G.X.hom` is smooth, hence locally of
   finite type, and `f.left ≫ M.hom = G.X.hom`, so `f.left` is locally of finite
   type (`locallyOfFiniteType_of_comp`). Since `p.left ≫ φ.left = f.left` and
   `p.left` is fppf, the Library's
   `locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`
   applies.
7. So `φ.left` is proper, and `IsClosedImmersion.iff_isProper_and_mono` shows
   that it is a closed immersion, which is the conclusion.

## Provenance

This is an internal assembly step of the proof
`selfCentralizingTorusConjugacyQuotientAffine` of
`SelfCentralizingTorusConjugacyQuotientAffineStatement` and follows no particular source.
The descent of `f` and the identification of its fibres with normalizer cosets
correspond to the identification `G/N ≅ TM_G` in the proof of SGA 3, Exposé XVI,
Theorem 4.1(d). The step "proper monomorphism ⇒ closed immersion" is Stacks Project, Tag 04XV,
available in Mathlib as `IsClosedImmersion.iff_isProper_and_mono`.
