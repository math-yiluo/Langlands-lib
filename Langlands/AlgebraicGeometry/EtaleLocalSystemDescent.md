# Descent of trivializations of étale local systems

This module compares trivializations of an étale local system on different members of an
étale cover. It contains five parts:

1. transition isomorphisms between two trivializations;
2. the pointwise *label* of a morphism of constant sheaves;
3. gluing: trivial transitions on a cover make the sheaf constant;
4. monodromy: over a base with a generic point, transitions congruent to the identity
   modulo `n ≥ 3` can be made trivial, assuming
   `Langlands.FiniteOrderCongruenceDetectionStatement`;
5. refinement: the monodromy result applies on every irreducible scheme whose stalks are
   integrally closed domains.

All declarations are in the namespace `Langlands.AlgebraicGeometry.EtaleLocalSystem`. They
use the published definitions `restrict`, `constant`, `constantSections` and
`IsEtaleSheaf` of `Langlands.AlgebraicGeometry.EtaleLocalSystem`, and `constantCongr` of
`Langlands.AlgebraicGeometry.EtaleLocalSystemBasics`. Schemes are in universe `u`.
Coefficient groups `M N P : AddCommGrpCat.{v}` are in universe `v`. Presheaves
`F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}` live on the category of all `S`-schemes. A
*trivialization* of `F` over `f : X ⟶ S` is an isomorphism
`ef : restrict f F ≅ constant X M`.

This is an internal derived module of the proof that groups of multiplicative type over
normal bases are locally isotrivial (Conrad, *Reductive group schemes*,
Corollary B.3.6; `multiplicativeTypeNormalIsotrivial` in `Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialProof`). Its role in Conrad's proof is explained in "Correspondence with the
source" below.

## 1. Transition isomorphisms

### Definitions

- `overIsoOfEq w`: for equal morphisms `g = h : Y ⟶ T`, the isomorphism
  `Over.mk g ≅ Over.mk h` in `Over T` whose underlying morphism is the identity of `Y`.
- `congrIso w F`: for equal `g = h : T ⟶ S`, the isomorphism
  `restrict g F ≅ restrict h F`. On an object `V` it is `F` applied to `overIsoOfEq`.
- `fromRestrict ef a`: a trivialization `ef` over `f : X ⟶ S`, pulled back along
  `a : W ⟶ X`. It is an isomorphism `restrict (a ≫ f) F ≅ constant W M`. On `V` over `W`
  it is `F` of the reassociation isomorphism, followed by `ef` at `(Over.map a).obj V`.
- `transition ef eg a b h`: for trivializations `ef` over `f : X ⟶ S` (group `M`) and `eg`
  over `g : Y ⟶ S` (group `N`), and `a : W ⟶ X`, `b : W ⟶ Y` with `h : a ≫ f = b ≫ g`, the
  isomorphism `constant W M ≅ constant W N` given by
  `(fromRestrict ef a).symm ≪≫ congrIso h F ≪≫ fromRestrict eg b`.

### Statements

- `transition_trans` (cocycle identity): for three trivializations and maps `a`, `b`, `c`
  to their sources with `a ≫ f = b ≫ g` and `b ≫ g = c ≫ k`, the composite of the two
  transitions is the transition from the first to the third trivialization.
- `transition_self`: `transition ef ef a a rfl = Iso.refl _`.
- `transition_symm`: swapping the two trivializations inverts the transition.
- `transition_comp_app` (naturality): pulling back along `k : W' ⟶ W`, the transition along
  `k ≫ a`, `k ≫ b` agrees on each object `V` over `W'` with the transition along `a`, `b` on
  `(Over.map k).obj V`.
- Simp and component lemmas: `overIsoOfEq_hom_left`, `overIsoOfEq_inv_left`,
  `congrIso_hom_app`, `congrIso_inv_app`, `fromRestrict_hom_app`, `fromRestrict_inv_app`,
  `congrIso_rfl` (identity along `rfl`), `congrIso_trans`,
  `constant_map_overIsoOfEq_hom`, `inv_app_overIsoOfEq`, `hom_app_overIsoOfEq`,
  `restrict_map_eq`.

## 2. Labels

Let `W` be a scheme and `φ : constant W M ⟶ constant W N`.

### Definitions

- `evalAt φ V s x`: for `V` over `W`, a locally constant `s : V.left → M` and a point `x`
  of `V`, the value at `x` of the image of `s` under `φ`. Sections of the constant sheaf are
  read as locally constant functions through `constantSections`.
- `label φ w : M →+ N`: the *label* of `φ` at the point `w : W`. It sends `m` to
  `evalAt φ (Over.mk (𝟙 W)) (const m) w`, the value at `w` of the image of the constant
  function `m`.
- `labelEquiv τ w : M ≃+ M`, for an automorphism `τ : constant W M ≅ constant W M`: the
  label of `τ.hom` at `w`, with inverse the label of `τ.inv` (in part 4).

### Statements

- `evalAt_eq_label` (**evaluation formula**): for every `V`, `s` and `x`,
  `evalAt φ V s x = label φ (V.hom x) (s x)`. So `φ` acts pointwise through its labels.
- `label_comp`, `label_id`, `label_apply`, `evalAt_comp`, `evalAt_comap`,
  `constantSections_symm_map`, `evalAt_of_subsingleton`: functoriality and naturality.
- `ext_of_label`: a morphism of constant sheaves is determined by its labels.
- `isLocallyConstant_label φ m`: `w ↦ label φ w m` is locally constant.
- `label_transition_comp`: the label of a transition along `k ≫ a`, `k ≫ b` at `w` is the
  label of the transition along `a`, `b` at `k w`.
- `label_eq_of_specializes`: labels agree at a point and its specializations.
- `label_constantCongr`, `label_constantCongr_inv`: the labels of `constantCongr W c` are
  `c` and `c.symm`.
- `label_transition_trans_apply`: the cocycle identity for labels at a point.
- `label_transition_eq_lift`: the label of the transition along `a`, `b` at `w` equals the
  label of the transition on `X ×_S Y` at the point `pullback.lift a b h w`.
- `transition_trans_constantCongr`, `constantCongr_transition`: changing a trivialization
  by an automorphism `c` of the group composes the transition with `constantCongr c`.

## 3. Gluing

### Definitions

- `trivHom f a U c hc`: the morphism in `Over S` from `W` (over `S` by `a ≫ f`) to `U`
  given by `c : W ⟶ U.left`, where `hc : c ≫ U.hom = a ≫ f`.
- `triv ef a c hc s`: a section `s` of `F` over `U`, pulled back to `W` along `c` and
  trivialized by `ef` along `a`. It is a section of `constant W M` over `W`.
- In the gluing section, `f i : X i ⟶ S` is a family with trivializations
  `e i : restrict (f i) F ≅ constant (X i) M`, jointly surjective:
  `hcov : ∀ x, ∃ i y, f i y = x`.
  - `trivFun e i s`: the trivialization of `s` over `U ×_S X i`, as a locally constant
    function.
  - `glueValue e hcov s y`: the value at `y : U.left` obtained from a chosen point of some
    `U ×_S X i` over `y`.
  - `glueAddHom`, `glueHom e hcov htriv : F ⟶ constant S M`: these values assembled into a
    morphism of presheaves.
  - `coverObj f U i`, `coverArrow f U i`: the pulled-back cover `U ×_S X i ⟶ U` in
    `Over S`.
  - `localPreimage e U t i`: a preimage over `U ×_S X i` of a section `t` of the constant
    sheaf.

### Statements

- `transition_hom_triv`, `triv_apply_eq_of_label`, `triv_comp_apply`, `triv_congr`,
  `triv_congr_a`, `triv_map`, `triv_add`, `transition_congr`, `label_transition_eq_id`:
  bookkeeping for trivialized sections. Transitions carry `triv ef` to `triv eg`, and where
  the label is trivial the two trivializations agree.
- `triv_pullback_eq` (**well-definedness**): if the transition between `ef` and `eg` on
  `X ×_S Y` has trivial labels, then for points `z ∈ U ×_S X` and `z' ∈ U ×_S Y` over the
  same point of `U`, the trivializations of `s` take the same value at `z` and `z'`.
- `glueValue_eq`, `isLocallyConstant_glueValue`, `glueValue_add`, `glueValue_zero`,
  `glueValue_map`, `exists_pullback_point`, `glueValue_localPreimage`: properties of the
  glued values.
- `ofArrows_coverArrow_mem`, `isSheafFor_coverArrow`: if all `f i` are étale, the
  pulled-back cover is a covering sieve for `topology S`, and an étale sheaf satisfies the
  sheaf condition for it.
- `glueHom_app_injective`, `glueHom_app_surjective`, `isIso_glueHom`.
- `nonempty_iso_constant_of_label_eq_id [∀ i, Etale (f i)] htriv hF` (**gluing theorem**):
  let `F` be an étale sheaf (`IsEtaleSheaf F`) and let the `f i` be étale and jointly
  surjective. If every transition `transition (e i) (e j)` on `X i ×_S X j` has label
  `AddMonoidHom.id M` at every point, then `F ≅ constant S M`.

## 4. Monodromy

- `eq_refl_of_finite_of_trans_mem hFOC hn htors hfin hmul hcong ha`: let `M` be a finitely
  generated abelian group and `n ≥ 3` with `n • x = 0` for every torsion element `x`. Let
  `Φ` be a finite set of automorphisms of `M` that is closed under composition, and whose
  elements `a` satisfy `∀ x, ∃ y, a x = x + n • y` (congruent to the identity modulo `n`).
  Assuming `hFOC : FiniteOrderCongruenceDetectionStatement`, every element of `Φ` is the
  identity.

In the rest of this part `T` is a scheme, `F` a presheaf on `Over T`, and
`e i : restrict (f i) F ≅ constant (V i) M` trivializations over étale `f i : V i ⟶ T`.
The *level hypothesis* `hlevel` says that every transition on `V i ×_T V j` has labels
congruent to the identity modulo `n`:
`label (transition (e i) (e j) _ _ _).hom z m = m + n • y` for some `y`. The point
`η : T` is a generic point: `hη : ∀ t, η ⤳ t`. The hypothesis
`hsub : ∀ i v v', f i v = η → f i v' = η → v = v'` says each member has at most one
point over `η`.

- `exists_generization_over`: every point of `V i ×_T V j` specializes from a point
  lying over `η`. Étale maps are flat, hence generalizing.
- `label_self_eq_id` (**step A**): under `hlevel`, `hsub` and finiteness `hfin` of the set
  of labels on `V i₀ ×_T V i₀`, these labels are all the identity.
- `label_overlap_eq` (**step B**): under the same hypotheses, the labels of the
  transition on `V i₀ ×_T V i` are all equal, for each `i`.
- `nonempty_iso_constant_of_level` (**monodromy theorem**): assume further `hcov`,
  `IsEtaleSheaf F` and a point `v₀ : V i₀` over `η`. Then `F ≅ constant T M`.

## 5. Refinement over irreducible normal bases

- `eq_of_specializes_of_etale`: within a fibre of an étale morphism there are no
  nontrivial specializations.
- `eq_of_apply_eq_of_etale_of_irreducible`: an irreducible scheme étale over `T` has at
  most one point over a generic point `η` of `T`.
- `isAffine_pullback_comp_ι`: if `V` is affine and `a : V ⟶ U.toScheme` for an affine open
  `U` of `T`, then `V ×_T V` (along `a ≫ U.ι`) is affine.
- `finite_range_label`: on a compact scheme, a morphism of constant sheaves with finitely
  generated source group has only finitely many labels.
- `transition_fromRestrict`: transitions of restricted trivializations
  `fromRestrict ef a'`, `fromRestrict eg b'` are transitions of `ef`, `eg` along composites.
- `nonempty_iso_constant_of_level_of_irreducible hFOC hT hF hn htors hcov e hlevel`
  (**constancy over irreducible normal bases**): let `T` be irreducible with
  `∀ t, IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)`, and let
  `F` be an étale sheaf on `Over T`. Let `M` be finitely generated, `3 ≤ n`, and let
  `n` kill the torsion of `M` (`htors`). Let `e i` be trivializations over a jointly
  surjective family of étale `f i : V i ⟶ T` satisfying the level hypothesis `hlevel`.
  Assuming `hFOC`, `F ≅ constant T M`.

## Correspondence with the source

Brian Conrad, *Reductive group schemes* (2014), `conrad-2014-reductive-group-schemes`,
proof of Corollary B.3.6, pp.294-295. Conrad fixes `n ≥ 3` divisible by the exponent of
`M_tor`, passes to a cover over which `F/nF` is constant, and shows that `F` is then
constant. His argument has three steps:

- over a field, the Galois action on `M` factors through a finite subgroup of
  `Γ = ker(Aut(M) → Aut(M/nM))`, which is torsion-free;
- over an integrally closed local domain, a generic isomorphism `f_η` extends;
- over a general irreducible `S`, local isomorphisms normalized at the generic point glue.

Part 4 is a direct version of this argument on an étale cover, without Galois groups or
geometric stalks. The labels on the self-overlap `V i₀ ×_T V i₀` form a finite set closed
under composition (step A), contained in `Γ`. The torsion-freeness of `Γ` is the published
statement `Langlands.FiniteOrderCongruenceDetectionStatement`, used as the hypothesis
`hFOC`. Conrad's normalization at the generic point is the choice of the constants `c i`
in the monodromy theorem (labels at `η`), and his gluing is part 3. Parts 1-3 and 5 are
derived infrastructure. They formalize "descent of an isomorphism" and "labels at the
generic point determine everything" in the big-site language of the published
`EtaleLocalSystem` definitions.

## Proofs

**Transitions.** `transition_trans` cancels `fromRestrict eg b` against its inverse and
composes the two `congrIso`s (`congrIso_trans`). `transition_symm` follows from
`transition_trans` and `transition_self`. The component lemmas reduce to functoriality of
`F` on morphisms in `Over S` whose underlying morphisms are identities.

**Labels.** `evalAt_comap` is naturality of `φ`. For `evalAt_eq_label`, pull back along
`Spec κ(x) ⟶ V.left` (`fromSpecResidueField`). Its source has one point, so the section is
the pullback of a constant function (`evalAt_of_subsingleton`). `label_comp` and
`ext_of_label` then follow. Local constancy of labels holds because `label φ · m` is the
image of a constant section, a locally constant function.

**Gluing.** `glueValue` takes at `y` the value of the trivialized section at a chosen
point of some `U ×_S X i` over `y`. `triv_pullback_eq` makes this independent of the
choice: two such points have a common preimage in the fibre product of the two
pullbacks (`Scheme.Pullback.exists_preimage_pullback`), and the trivial labels identify the
two trivializations there (`triv_apply_eq_of_label`). The glued function is locally
constant because the projections `U ×_S X i ⟶ U` are étale, hence open. This gives
`glueHom`. It is injective on sections by the sheaf condition for the pulled-back étale
cover (`isSheafFor_coverArrow`, via `Presheaf.isSheaf_comp_of_isSheaf` with the forgetful
functor). It is surjective because the local preimages `localPreimage` are compatible and
glue. A morphism of presheaves that is bijective on all objects is an isomorphism.

**Finite congruence sets.** In `eq_refl_of_finite_of_trans_mem`, the powers `a^(k+1)` lie
in the finite set `Φ`. So two of them coincide, and `a` has finite order. `hFOC` then
gives `a = id`.

**Monodromy.** Step A: the label set `Φ` on `V i₀ ×_T V i₀` is closed under composition.
Given points `z₁`, `z₂`, replace them by generizations `z₁'`, `z₂'` over `η`
(`exists_generization_over`, `label_eq_of_specializes`). By `hsub` the second coordinate
of `z₁'` equals the first coordinate of `z₂'`. A point `ζ` of the triple overlap over both
exists by `exists_preimage_pullback`. The cocycle identity at `ζ` shows that the
composite of the two labels is the label at a point of `V i₀ ×_T V i₀`. Now apply
`eq_refl_of_finite_of_trans_mem`. Step B: two points of `V i₀ ×_T V i` have generizations
over `η` with the same second coordinate (`hsub`). The cocycle identity with step A shows
that their labels agree. Theorem: let `c i` be the common label on `V i₀ ×_T V i` (the
identity if this overlap is empty). Replace `e i` by `e i ≪≫ constantCongr (c i).symm`. For
a point of `V i ×_T V j`, take a generization over `η` and a point `v₀` of `V i₀` over `η`.
The cocycle identity through `V i₀` shows that the new transition has trivial label.
Conclude with the gluing theorem.

**Refinement.** Étale morphisms are locally quasi-finite
(`Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale`), so their fibres are discrete
(`isDiscrete_preimage_singleton`). A specialization inside a discrete fibre is an equality.
An irreducible `V` étale over `T` has its generic point over `η`, because a specialization
`f(ξ) ⤳ η` from a point specializing from `η` is an equality. Every point of `V` over `η`
is a specialization of `ξ` in the same fibre, hence equals `ξ`. For
`nonempty_iso_constant_of_level_of_irreducible`, refine the cover. The new members are the
affine opens `W` of the `V i` that are irreducible and map into an affine open of `T`.
Such opens exist around every point. Indeed, the connected component of a point of `V i`
is open and irreducible by
`EtaleNormalLocallyIrreducible.isIrreducible_connectedComponent_of_etale`, and affine opens
form a basis. The trivializations restrict (`fromRestrict`, `transition_fromRestrict`), and
the level hypothesis is preserved (`label_transition_eq_lift`). Each member has at most one
point over the generic point of `T` (`eq_of_apply_eq_of_etale_of_irreducible`). The
self-overlap of the member through the generic point is affine
(`isAffine_pullback_comp_ι`), hence compact, so its labels are finite
(`finite_range_label`). Then apply the monodromy theorem.
