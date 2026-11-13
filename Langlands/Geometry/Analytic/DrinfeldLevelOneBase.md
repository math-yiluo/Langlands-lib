# The level-one space `Ω × Δ` for the matrix factor `GL_{d+1}(F)`

Author: Worker 21.

This module constructs the analogue of Harris's level-one space
`ℳ_1 = Ω × Δ` for the matrix group `GL_{d+1}(F)`. It is one copy of
Drinfeld's upper half space `Ω` for each element of an index set `Δ`, and
`g ∈ GL_{d+1}(F)` acts on `Ω` while it moves the copies through
`|det g|`. In Berkovich's language it is the space `X_Σ` of the `G`-space
`X = Ω` and a `G`-set `Σ`. The module also gives the inclusions of the copies,
the projection to `Ω`, Harris's domains `U(e, 1, δ) = U(e) × {δ}` as
equivariant maps, and `Ω × Δ` as a `GL_{d+1}(F)`-space given continuity of the
action on `Ω` and the published statement
`SetInducedSpace.ContinuityStatement`. All declarations lie in
`Langlands.Analytic.DrinfeldUpperHalfSpace`. Everything stated in the module is
proved.

The ingredients are constructed in earlier modules. `omegaAction F K d`
(module `DrinfeldGroupAction`) is the action of `GL_{d+1}(F)` on `Ω`.
`SetInducedSpace.setInduced X S`, its copies and its projection (module
`SetInducedSpace`) form Berkovich's space `X_Σ`.
`facetAction`, `facetInclusion`, `facetStabilizerNormOne` and `omegaGSpace`
come from `DrinfeldFacetSpaces` and `DrinfeldFacetGSpaces`. The statement
`SetInducedSpace.ContinuityStatement` is in module
`SetInducedSpaceContinuityStatement`.

## Original sources

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed p.303 (PDF p.5):

> More generally, for every integer N ≥ 1, Drinfeld has constructed rigid
> analytic spaces ℳ_N admitting finite étale coverings ℳ_N → ℳ_{N−1}, with
> ℳ_1 = Ω × Δ, Δ the finitely generated free abelian group of algebraic
> characters of GJ. For each δ ∈ Δ, the inverse image of U(e) × δ in ℳ_N is
> denoted U(e, N, δ)

On the same page, Harris's group is `G_J = (∏_j B(F_j)^×) × ℚ_p^×`, where
`F = F_1` and `B(F)` is the matrix algebra. Harris 1999 does not write out how
`G_J` acts on `Δ`. For the group `J_v = GL(n, F)` it is written out in
Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, Appendix,
printed p.115 (PDF p.41). There the level-`N` space is
`Σ_N ×_F F^nr × Δ_v` (A.5), and:

> We identify J_v with GL(n, F) and define v : J_v → ℤ by
> v(j) = ord_v(det(j)), where ord_v is the v-adic valuation. In terms of the
> factorization (A.1), (A.2), the action is then
>
> (A.6) j(x, (d, d′)(mod C_p)) = (j(x), (dΠ^{−v(j)}, d′Π^{v(j)})(mod C_p)).

So `j` acts on the discrete factor only through `ord_v(det j)`.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.2,
printed p.4:

> For a G-set Σ, let X_Σ denote the disjoint union ∐_{σ∈Σ} X_σ (X_σ are
> copies of X) provided with the following action of G: an element g ∈ G
> takes X_σ to X_{gσ} by the action of g on X.

## Derived choices

1. **Matrix factor only.** The group is `GL_{d+1}(F)`, the factor `B(F)^×`
   of Harris's `G_J`, not `G_J` itself. Neither `G_J`, nor its action on `Ω`
   or on Harris's `Δ`, is constructed, and the module makes no comparison with
   them. The space built here is the analogue of `ℳ_1 = Ω × Δ` for this
   factor.
2. **The index set.** The algebraic characters of `GL_{d+1}` over `F` are the
   powers `det^n`, `n ∈ ℤ`, so the analogue of `Δ` for `GL_{d+1}(F)` is a
   free abelian group of rank one, and by (A.6) `g` moves it through the
   valuation of `det g`. The module does not choose a uniformizer or an
   identification with `ℤ`. It uses the canonical transitive `G`-set
   `LevelOneIndex F d = GL_{d+1}(F) ⧸ detNormOne F d`, where `detNormOne` is
   the kernel of `g ↦ ‖det g‖`, with `g` acting by left multiplication. The
   map `levelOneIndexNorm : γ ↦ ‖det γ‖` is injective, its image is the value
   group `{‖x‖ : x ∈ F^×}`, and it turns the action of `g` into
   multiplication by `‖det g‖` (all proved here). When `F` is discretely
   valued with `‖π‖ = q^{−1}`, `−log_q ‖det γ‖ = ord(det γ)`, so this index set
   is `ℤ` with `g` acting by `n ↦ n + ord(det g)`. That identification is not
   formalized. The model also makes sense for the Library's generality, a
   nontrivially normed field `F` whose value group may not be discrete.
3. **Sign.** Harris's (A.6) multiplies `d` by `Π^{−v(j)}`, and whether that is
   a translation by `+v(j)` or `−v(j)` depends on the identification of `Δ_v`
   with `ℤ`. The `G`-sets `ℤ` with `n ↦ n + ord(det g)` and with
   `n ↦ n − ord(det g)` are isomorphic through `n ↦ −n`, so the spaces `X_Σ`
   they give are isomorphic. The module uses left multiplication on
   `GL_{d+1}(F) ⧸ detNormOne F d`.
4. **`U(e, 1, δ)`.** For `N = 1`, Harris's `U(e, 1, δ)` is `U(e) × {δ}`. Here
   it is the composite of the inclusion `U(f) → Ω` with the inclusion of the
   copy indexed by `δ`, as a map of `H`-objects for `H` inside
   `facetStabilizerNormOne S`. Such `H` fix every index, because they lie in
   `detNormOne`. As in `DrinfeldFacetGSpaces`, `f` is a finite set of
   vertices of the Library's building of norm classes, and
   `facetStabilizerNormOne` is the analogue in `GL_{d+1}(F)` of Harris's
   `S(ê)`, not a statement about `S(ê)`.

## Declarations

The index set:

- `detNormOne F d`: the normal subgroup of `γ ∈ GL_{d+1}(F)` with
  `‖det γ‖ = 1`, the kernel of `γ ↦ ‖det γ‖` as a homomorphism to `ℝ^×`.
  `mem_detNormOne` characterizes membership. `facetStabilizerNormOne_eq` says
  `facetStabilizerNormOne S = facetStabilizer S ⊓ detNormOne F d`, and
  `facetStabilizerNormOne_le_detNormOne` follows.
- `LevelOneIndex F d`: the quotient `GL_{d+1}(F) ⧸ detNormOne F d`, with
  Mathlib's left action of `GL_{d+1}(F)`.
- `levelOneIndexNorm δ`: the value `‖det γ‖` for `δ` the class of `γ`
  (`levelOneIndexNorm_mk`). `levelOneIndexNorm_injective`,
  `range_levelOneIndexNorm` (the image is `{‖x‖ : x ∈ F^×}`) and
  `levelOneIndexNorm_smul`
  (`levelOneIndexNorm (g • δ) = ‖det g‖ * levelOneIndexNorm δ`).
- `smul_levelOneIndex_of_mem`: elements of `detNormOne` fix every index.
  `stabilizer_levelOneIndex`: the stabilizer of every index is exactly
  `detNormOne F d`.
- `isOpen_detNormOne` and `isOpen_stabilizer_levelOneIndex`: for ultrametric
  `F`, `detNormOne F d` is open in `GL_{d+1}(F)`, so all stabilizers of the
  index set are open. (The norm is locally constant away from `0`, and the
  determinant is continuous.)

The space:

- `levelOneBase K`: `SetInducedSpace.setInduced (omegaAction F K d)
  (LevelOneIndex F d)`, Berkovich's `X_Σ` for `X = Ω` and
  `Σ = LevelOneIndex F d`, as an object of
  `Action (LocalizedCategory.{u, u, u}) GL_{d+1}(F)`.
- `levelOneCopy K δ`: the inclusion of the copy `Ω × {δ}`. `levelOneCopy_ρ`:
  `levelOneCopy K δ ≫ ρ g = (omegaAction F K d).ρ g ≫ levelOneCopy K (g • δ)`.
- `levelOneProjection K`: the projection `Ω × Δ → Ω` as a morphism of
  `GL_{d+1}(F)`-objects, with `levelOneCopy_projection` (identity on each
  copy).
- `levelOneCopyHom K H hH δ`: for a subgroup `H ≤ detNormOne F d`, the
  inclusion of the copy `δ` as a morphism of `H`-objects (restriction along
  `H.subtype`), with `levelOneCopyHom_hom`.
- `facetLevelOneInclusion K hS ε H hH δ`: for `H ≤ facetStabilizerNormOne S`,
  the inclusion `U(f) → Ω × {δ} ⊂ Ω × Δ` as a morphism from `facetAction` to
  the restriction of `levelOneBase K` to `H`. `facetLevelOneInclusion_hom`
  gives its underlying morphism.
- `levelOneGSpace K hΩ hSI`: for ultrametric `F`, `Ω × Δ` as a
  `GL_{d+1}(F)`-space (an object of `GSpace K GL_{d+1}(F)`), given
  `hΩ : IsContinuousAction (omegaAction F K d).ρAut` and
  `hSI : SetInducedSpace.ContinuityStatement.{u, u, u}`. It applies `hSI` to
  `omegaGSpace K hΩ` and the index set, whose stabilizers are open.
  `levelOneGSpace_obj`: its underlying object is `levelOneBase K`.
- `levelOneGSpaceProjection K hΩ hSI`: the projection as a morphism of
  `GL_{d+1}(F)`-spaces to `omegaGSpace K hΩ`.

Assumptions: `F`, `K` and the group all live in one universe `u`, as
`SetInducedSpace.ContinuityStatement.{u, u, u}` requires. `F` is a nontrivially
normed field with `ProperSpace F`; `IsUltrametricDist F` is assumed only for the
openness results, `levelOneGSpace` and `levelOneGSpaceProjection`. `K` is a complete ultrametric nontrivially
normed field and a normed `F`-algebra, and `d ≥ 1` (`NeZero d`), as for
`omegaAction`. The topology on `GL_{d+1}(F)` is Mathlib's topology on the
units of the matrix ring.

## Scope

- Continuity of the action on `Ω` and the statement
  `SetInducedSpace.ContinuityStatement` are hypotheses of `levelOneGSpace`;
  both are published statements that are still unproved
  (`OmegaActionContinuityStatement` gives `hΩ`).
- The higher levels `ℳ_N` for `N ≥ 2`, their domains `U(e, N, δ)`, Harris's
  `G_J`, its action on `Δ` and `S(ê)` are not constructed. The identification
  of `LevelOneIndex F d` with `ℤ` for discretely valued `F` is described above
  but not formalized.
