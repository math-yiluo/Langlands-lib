# Descent of ample line-bundle existence along finite field extensions

This module proves the descent of the existence of an ample line bundle along a
finite field extension, the Library proposition
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement.{u}`
from module
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentStatement`.
Let `K` be a field, `L` a finite extension of `K`, and `X` a scheme over `K`.
Write `Y` for the actual Mathlib pullback of `p : X ⟶ Spec K` along
`Spec L ⟶ Spec K`, and `π : Y ⟶ X` for its first projection
`pullback.fst`. If some `M : LineBundle Y` satisfies `M.IsAmple`, then some
`N : LineBundle X` satisfies `N.IsAmple`.

The final theorem is `finiteFieldExtensionAmpleExistenceDescent`, in namespace
`Langlands.AlgebraicGeometry.Picard`. Its type is exactly the published
proposition, with universe `u` kept, and it has no hypotheses. It applies the
structural theorem `descent_of_statements` to three published proofs.

## Published proofs used

`descent_of_statements` takes the following three propositions as hypotheses.
`finiteFieldExtensionAmpleExistenceDescent` supplies them by the published
proofs `finiteFieldExtensionNorm` (module
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof`),
`cocycleLineBundle` (module
`Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof`) and
`ampleFiniteSetSection` (module
`Langlands.AlgebraicGeometry.Picard.AmpleFiniteSetSectionProof`).

- `h1 : FiniteFieldExtensionNormStatement.{u}`. For every open `U` of `X`
  there is a monoid homomorphism `Nm U : Γ(Y, π ⁻¹ᵁ U) →* Γ(X, U)`. These maps
  commute with restriction. They satisfy `Nm U (π.app U g) = g ^ finrank K L`,
  and `X.basicOpen (Nm U f)` is the set of points of `U` whose whole fibre lies
  in `Y.basicOpen f`. The power clause is not used.
- `h2 : CocycleLineBundleStatement.{u}`. Let `T` be an open cover of `X` and
  `g i j` units on `T i ⊓ T j` satisfying the cocycle identity. Then some line
  bundle `N` has the following property. Every family `a i : Γ(X, T i)` with
  `a i = g i j * a j` on overlaps comes from a global section `t` of `N` with
  `T i ⊓ trivializationOpen N.obj t = X.basicOpen (a i)` for all `i`.
- `h3 : AmpleFiniteSetSectionStatement.{u}`. For an ample `M`, a finite set `E`
  inside an open `W` lies in `M.sectionOpen s` for a section `s` of a positive
  power of `M`, and `M.sectionOpen s ≤ W`.

The section-coefficient lemmas come from
[Modules.SectionCoefficients](../Modules/SectionCoefficients.md). The published
`affineGenerationLocusIntersection`, `tensorPowMulIso`,
`tensorPow_isLocallyFreeRankOne`, `trivializationOpen_mapIso` and
`trivializationOpen_sectionPow` are imported by name.
`trivializationOpen_mapIso` says that for every isomorphism `e : P ≅ Q` of
module sheaves and every global section `s` of `P`,
`trivializationOpen Q (e.hom.app ⊤ s) = trivializationOpen P s`.
`trivializationOpen_sectionPow` (the consumer form of the published
`positiveSectionPowerGenerationLocus`) says that for a line bundle `L`, a global
section `s` of `L.obj` and `0 < n`, the generation open of `sectionPow L.obj s n`
equals that of `s`.

## Implemented proof

### Gluing the norms of coefficients (namespace `NormDescent`)

Fix a morphism `π : Y ⟶ X`, a module sheaf `P` on `Y`, opens `T i` of `X` and
global sections `S i` of `P` with `π ⁻¹ᵁ T i ≤ trivializationOpen P (S i)`.

- `coeff i j : Γ(Y, π ⁻¹ᵁ T i)` is the coefficient of `S j` against `S i` on
  `π ⁻¹ᵁ T i`, chosen by `exists_smul_sectionRes_eq`. `coeff_spec` records
  `coeff i j • S i = S j` there. `coeffRes i j hW` is its restriction to
  `π ⁻¹ᵁ W` for `W ≤ T i`. The lemma `coeffRes_spec` restricts the relation,
  and `coeffRes_res` composes restrictions.
- `coeffRes_mul`: on `π ⁻¹ᵁ W` with `W ≤ T i ⊓ T j`, uniqueness of
  coefficients (`coeff_mul`) gives `c_ik = c_ij * c_jk`. Also
  `coeffRes_self` gives `c_ii = 1`.
- `basicOpen_coeff`: `Y.basicOpen (coeff i k) = π ⁻¹ᵁ T i ⊓
  trivializationOpen P (S k)`, by `basicOpen_coeff_eq`.

Let `Nm` be maps as in `h1` that commute with restriction (hypothesis `hNm`).

- `cocycle i j` is the unit of `Γ(X, T i ⊓ T j)` with value
  `Nm (coeffRes i j)` and inverse `Nm (coeffRes j i)`. The two products are `1`
  because `Nm` is multiplicative and `c_ij * c_ji = c_ii = 1`.
- `cocycle_cond`: the cocycle identity on triple overlaps. Both sides are norms
  of restricted coefficients (`norm_coeffRes_res`), and `coeffRes_mul` applies.
- `family_compatible`: for each `k` the family `a_i = Nm (T i) (coeff i k)`
  satisfies `a_i = cocycle i j * a_j` on `T i ⊓ T j`, by the same argument.
- `exists_lineBundle`: assume that the `T i` cover `X` and that
  `T i` is exactly the set of points whose fibre lies in
  `trivializationOpen P (S i)` (hypothesis `hTset`). Assume also the
  basic-open clause of `h1` (hypothesis `hNmBasic`). Then `h2` gives a line
  bundle `N` on `X` and, for each `k`, a global section `t` with
  `trivializationOpen N.obj t = T k`. Proof: `h2` applied to the family of
  `family_compatible` gives `t` with
  `T i ⊓ trivializationOpen N.obj t = X.basicOpen (Nm (coeff i k))`. By
  `hNmBasic`, `basicOpen_coeff` and `hTset k`, this basic open is the set of
  points of `T i` whose fibre lies in `trivializationOpen P (S k)`, that is,
  `T i ⊓ T k`. Since the `T i` cover `X`, `trivializationOpen N.obj t = T k`.

### A common degree (`exists_common_degree`)

Let `M` be a line bundle on `Y`, `ι` a finite type, and `s i` sections of
`tensorPow M.obj (n i)` with every `n i ≥ 1`. Let `m` be the product of the
`n i`. Then there are sections `S i` of `tensorPow M.obj m` with
`M.sectionOpen (S i) = M.sectionOpen (s i)`. The section `S i` is the image of
`sectionPow (tensorPow M.obj (n i)) (s i) (m / n i)` under
`tensorPowMulIso M.obj (n i) (m / n i)` followed by the `eqToIso` for
`n i * (m / n i) = m`. Two applications of `trivializationOpen_mapIso` and one
of `trivializationOpen_sectionPow` show that the generation open is unchanged.
`trivializationOpen_sectionPow` is applied to the line bundle
`tensorPow M.obj (n i)`, which has local rank one by
`tensorPow_isLocallyFreeRankOne`.

### The descent (`exists_isAmple_of_norm`)

This theorem works for any morphism `π : Y ⟶ X` whose underlying map is
surjective and closed with finite fibres, together with maps `Nm` satisfying
`hNm` and `hNmBasic`, and the hypotheses `h2` and `h3`. Let `M` be ample on
`Y`.

1. Every point `x` of `X` has an affine open neighbourhood `V x`
   (`isBasis_affineOpens`).
2. The fibre over `x` is finite and lies in `π ⁻¹ᵁ V x`. So `h3` gives
   `n x ≥ 1` and a section `s x` of `tensorPow M.obj (n x)` whose generation
   open contains the fibre and lies in `π ⁻¹ᵁ V x`.
3. `T x` is the complement of the image of the closed complement of
   `M.sectionOpen (s x)`. It is open because `π` is closed. It is the set of
   points whose whole fibre lies in `M.sectionOpen (s x)` (`hTset`). It
   contains `x`, and surjectivity of `π` gives `T x ≤ V x`.
4. `Y` is quasi-compact (part of ampleness), so `X` is quasi-compact
   (`CompactSpace` of a continuous surjective image). Finitely many `T x`,
   indexed by a `Finset` `t`, cover `X`.
5. `exists_common_degree` replaces the sections `s x` for `x ∈ t` by sections
   `S x` of one power `tensorPow M.obj m` with the same generation opens. Then
   `π ⁻¹ᵁ T x ≤ trivializationOpen (tensorPow M.obj m) (S x)`.
6. `NormDescent.exists_lineBundle` gives a line bundle `N` on `X` and, for each
   `x ∈ t`, a global section `r` with `trivializationOpen N.obj r = T x`.
7. `N` is ample. `X` is quasi-compact by step 4. Every point lies in some
   `T x` with `x ∈ t`. The section `sectionPow N.obj r 1` of
   `tensorPow N.obj 1` has generation open `T x`, by
   `trivializationOpen_sectionPow` with `n = 1`. This
   open is affine: `affineGenerationLocusIntersection` shows that
   `V x ⊓ trivializationOpen N.obj r` is affine, and this intersection is
   `T x` because `T x ≤ V x`.

### The target (`descent_of_statements`, `finiteFieldExtensionAmpleExistenceDescent`)

Given `K`, `L`, `X`, `p` and an ample `M` on the pullback, take `Nm`, its
restriction clause and its basic-open clause from `h1`. The morphism
`Spec L ⟶ Spec K` is finite (`IsFinite.SpecMap_iff`, `RingHom.finite_algebraMap`).
It is surjective, because `Spec L` is nonempty and `Spec K` has one point.
Both properties are stable under base change, so `π` is finite and
surjective. Hence its underlying map is closed (`Scheme.Hom.isClosedMap`) and has
finite fibres (`Scheme.Hom.finite_preimage_singleton`). Then
`exists_isAmple_of_norm` applies.

`finiteFieldExtensionAmpleExistenceDescent` is `descent_of_statements`
applied to `finiteFieldExtensionNorm`, `cocycleLineBundle` and
`ampleFiniteSetSection`.

The proof keeps arbitrary fields, inseparable and trivial extensions, and
arbitrary schemes over `K`. It adds no finite-type, separatedness or
noetherian hypothesis.

## Provenance

The target is Stacks Project Proposition 31.18.9(1), proved there from Lemmas
31.18.6 and 31.18.4 (tag 0BCX, registered source
`stacks-norms-field-ample-descent-2026-10-26`, file `0BCX.html`). Lemma 31.18.6
supplies a norm of degree `[L : K]` for `π`. Here it is used through
`FiniteFieldExtensionNormStatement`, whose basic-open clause combines condition
(2) of the definition of a norm with the remark that norms send units to units.

The proof of Lemma 31.18.4 takes the norm `N = Norm_π(L)` of the ample bundle,
built in Lemma 31.18.2 from the norms of the transition units of generating
sections over a cover. It then shows that `Y_t` is affine for `t = Norm_π(s)`,
with `s` given by Properties, Lemma 28.30.6, using Lemma 31.18.3 and Properties,
Lemma 28.27.4. The Lean proof differs in one respect. It does not take the norm
of an arbitrary invertible module, and it does not use Lemma 31.18.1. Instead it
uses the sections from Lemma 28.30.6 themselves as generating sections, over
preimages of the opens `T x`, after passing to a common tensor power. So one
cocycle gives the norm bundle, and the norms of these sections are the glued
families `Nm (coeff i k)`. The transition convention is `S j = c_ij S i` on
`π ⁻¹ T i`; the source writes `s_j = u_jj' s_j'`. As a consequence the ample
bundle on `X` is the norm of a power of `M`, and its first power already has
the required sections.

`AmpleFiniteSetSectionStatement` is weaker than Properties, Lemma 28.30.6
(tag 09NV): it does not assert that `X_s` is affine. The Lean proof gets
affineness from `T x ≤ V x` and `affineGenerationLocusIntersection` (Properties,
Lemma 28.27.4, tag 01PV), as the source does for `Y_t ⊂ V`.
