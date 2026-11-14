# Finite-index enlargement of smooth integral group models: proof

Worker 33 and Worker 260, for task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018).

`Langlands.GroupScheme.IntegralModel.finiteIndexEnlargement` proves the Library proposition
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement.{u}` of module
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement`. The theorem's type is exactly that
proposition, for an arbitrary universe `u`, with no further premises. The statement module and
its Markdown are unchanged.

The target: let `R` be a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`. Let `G` be an affine smooth group scheme over `Spec K`,
`M : IntegralModel R K G` a smooth model, and `V` a subgroup of `rationalPoints G` with
`M.integralPoints ≤ V`, such that `M.integralPoints.subgroupOf V` is normal and of finite index.
Then there are `N : IntegralModel R K G` and `j : M.Hom N (𝟙 G)` with
`IsOpenEnlargement M N j V`.

## Route

The enlargement is built directly as the spectrum of a Hopf subalgebra of the coordinate ring
of `M`. It is affine by construction. So the proof needs neither the gluing of the source
(KP A.7.1) nor Prasad–Yu Proposition 3.1 for affineness.

## The implemented proof

After introducing the data, the proof does the following.

1. **Coordinates.** `M.group.X.left` is affine (`isAffine_of_isAffineHom`). Let
   `A := AffineCoordinates.hopfAlgebra M.group`, the Library's coordinate Hopf algebra, and
   `e := AffineCoordinates.hopfSpecIso M.group`, its Hopf-spectrum isomorphism with `M.group`.
   `A` is smooth over `R` by `coordinate_smooth M hM` (module `Bridge`).
2. **Evaluation.** Let `ev : rationalPoints G →* WithConv (A →ₐ[R] K)` be the multiplicative
   equivalence `evaluationEquiv M A e` (module `Bridge`). It sends a generic point to its
   `K`-valued coordinate map; the group law becomes the convolution product.
3. **Hypotheses of the core.**
   - `hU`: `x ∈ M.integralPoints` iff all coordinate values of `ev x` are integral. This is
     `mem_integralPoints_iff M A e`.
   - `hsurj`: every `σ : A →ₐ[R] R` is the coordinate map of an integral point. Take the
     section `(sectionEquiv M.group A e).symm σ`; by `evaluationEquiv_integralPointMap`, its
     generic point has `ev = ofId ∘ σ`.
4. **Algebraic core.** `exists_hopf_enlargement` (module `Core`) applies to
   `U := M.integralPoints`, using the normality and finite-index hypotheses. It gives
   `B : CommHopfAlgCat R` and a bialgebra map `iB : B →ₐc[R] A` such that:
   - `B` is smooth;
   - `K ⊗[R] B → K ⊗[R] A` is bijective;
   - `Spec.map iB` is an open immersion;
   - `x ∈ V` iff all values `ev x (iB b)` are integral.
5. **Reconstruction.** Put `N := reconstructedModel M A e B iB hbij hBsm` and
   `j := reconstructedHom M A e B iB hbij hBsm` (module `Bridge`). `N.group` is the Hopf spectrum
   of `B`. Its generic identification comes from the bijectivity of `K ⊗ B → K ⊗ A`. The model
   morphism `j` is `e⁻¹` followed by `Spec iB`, and extends the identity of `G`.
6. **The four clauses of `IsOpenEnlargement`.**
   - `N.IsSmooth`: `reconstructedModel_isSmooth`.
   - `N.integralPoints = V`: by extensionality.
     `reconstructedModel_mem_integralPoints_iff` turns membership into integrality of all
     `ev g (iB b)`, and the points clause of the core identifies this with `g ∈ V`.
   - `IsOpenImmersion j.hom.hom.hom.left`: `reconstructedHom_isOpenImmersion` with the
     open-immersion clause of the core.
   - Relative identity components: for `i : C ⟶ M.group` with
     `IsRelativeIdentityComponent M.group i`, apply
     `Langlands.GroupScheme.RelativeIdentityComponent.comp_open` to the open immersion `j.hom`
     into the smooth group `N.group`. Composing with an open subgroup inclusion into a smooth
     group preserves the predicate.

## Helper modules

The candidate adds the following modules.

Algebraic core (Worker 33), under `Langlands/GroupScheme/IntegralModel/FiniteIndexEnlargement/`:

- `IntegralPoints`: Hensel lifting; points detect `𝔪 A` and divisibility.
- `Translation`: integral criterion for `K ⊗ C`; left and right translations.
- `Separating`: the separating coordinate.
- `SubHopf`: Hopf subalgebras of flat Hopf algebras, adapted from Anthropic FLT under Apache
  2.0 with attribution.
- `Enlarged`: the enlarged Hopf algebra.
- `PointTranslation`: translations by integral points.
- `Cover`: the covering lemma.
- `Core`: smoothness, generic fibre, open immersion and points.

Schemes and identity components (Worker 260):

- `Bridge` and `OpenImmersionCriterion`, in the same directory: the Hopf-coordinate bridge to
  schemes and the open-immersion criterion from principal localizations.
- `Langlands/GroupScheme/RelativeIdentityComponent/OpenSubgroup`: `comp_open`.

Each module has its own Markdown.

## Provenance

The theorem formalizes the finite-index, perfect-residue specialization of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, Proposition A.7.1(1)–(4). The source comparison is in the
statement's Markdown. The proof route is derived for this formalization, as described above.
