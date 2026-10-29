# Proof of uniqueness of actual rigidified abelian-scheme isomorphisms

`Langlands.AbelianScheme.rigidifiedIsoUniqueness` proves the published
proposition `Langlands.AbelianScheme.RigidifiedIsoUniquenessStatement.{u}`,
from module `Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessStatement`,
which is imported unchanged. For every scheme `S`, abelian scheme `A` over `S`,
test scheme `T : Over S` and pair `L M : RigidifiedFamily A T`, any two
isomorphisms `L ≅ M` are equal. The proof adds no hypothesis. The scalar
classification of line-bundle endomorphisms is proved in this file and not
assumed. The global-functions input is the published theorem
`Langlands.AbelianScheme.universalGlobalFunctions`.

The proof follows the source argument recalled in the statement's Markdown
(Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter VI, (6.2)).
It proves the stronger fact that every rigidified endomorphism is the
identity, not only every automorphism. It has four steps.

## 1. Endomorphisms of a line bundle are global scalars (section `Classification`)

The main new result is
`Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne`. For a
scheme `X`, a module sheaf `M` with `IsLocallyFreeRankOne M`, and any
endomorphism `φ : M ⟶ M`, it gives a global function `c : Γ(X, ⊤)` with
`φ = c • 𝟙 M`. The action `•` is the published action of global functions on
morphisms (`globalHomSMul`, in `Langlands.AlgebraicGeometry.ModuleLinear`).
On sections over `U` it multiplies by the restriction `restrictScalar U c`.

The proof uses the published local frames of
`Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation`. A
trivialization `t : M.restrict W.ι ≅ unit` over an open `W` gives, for every
open `V ⊆ W`, the generator `trivGen t i : Γ(M, V)` and the dual generator
`trivDualGen t`. Here `i : V ⟶ W` is the inclusion.

- `trivCoord t i` is the coordinate map `Γ(M, V) → Γ(X, V)`, evaluation of
  the restricted dual generator. `trivCoord_smul_trivGen` (from the published
  `trivGen_expansion`) says that every section `m` equals
  `trivCoord t i m • trivGen t i`. `trivCoord_trivGen` (from
  `trivDualGen_eval`) says that the coordinate of the generator is `1`.
- `smul_trivGen_injective`: if `a • trivGen t i = b • trivGen t i`, then
  `a = b`. Apply the coordinate map to both sides.
- `localScalar t φ : Γ(X, W)` is the coordinate of `φ` applied to the
  generator over `W`.
- `app_eq_localScalar_smul`: over every `V ⊆ W`, `φ` multiplies each section
  by the restriction of `localScalar t φ`. The generator over `V` is the
  restriction of the generator over `W` (`trivGen_restrict`). Naturality of
  `φ` gives the claim on the generator. Linearity of `φ` and the expansion of
  an arbitrary section give the general case.

For the theorem, choose for each point `x` a trivializing open `W x`
containing `x`, a trivialization, and the local scalar `d x`. On an overlap
`W x ⊓ W y`, both restricted scalars multiply the same generator to the same
section `φ(generator)`, by `app_eq_localScalar_smul` for each of the two
trivializations. So they agree, by `smul_trivGen_injective`. The family is
therefore compatible. The structure sheaf's gluing
`X.sheaf.existsUnique_gluing'` produces `c : Γ(X, ⊤)` restricting to `d x`
on each `W x`. Finally, `φ.app U m = restrictScalar U c • m` for every open
`U` and section `m`. Both sides have the same restriction to each
`U ⊓ W x`, by naturality of `φ`, `app_eq_localScalar_smul`, and
`restrictScalar_map`. Sheaf locality of `M`
(`TopCat.Sheaf.eq_of_locally_eq'`) concludes.

## 2. Pullback of a scalar endomorphism

No new lemma is needed here. The published
`Langlands.Scheme.Modules.pullback_map_smul`, from
`Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs`, states
`(Scheme.Modules.pullback f).map (r • φ) = f.appTop r • (pullback f).map φ`.

## 3. Rigidified endomorphisms are identities (`RigidifiedLineBundle.endo_eq_id`)

`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.endo_eq_id` works
for an arbitrary morphism `ε : S ⟶ X` such that `ε.appTop` is injective. It
proves that every endomorphism `φ` of an object `L` of
`RigidifiedLineBundle ε` is `𝟙 L`. Write `α = L.obj.rigidification`.

By step 1, the underlying module morphism is `c • 𝟙` for some
`c : Γ(X, ⊤)`. The rigidification condition `α.hom ≫ ε^*(φ) = α.hom`
becomes `ε.appTop c • α.hom = α.hom`, by step 2, `Functor.map_id` and
bilinearity of composition (`Linear.comp_smul`). Composing with `α.inv` gives
`ε.appTop c • 𝟙 = 𝟙` on `structureModule S`. Evaluating at the global
section `1` gives `ε.appTop c = 1`. This uses `restrictScalar_top`:
restriction from `⊤` to `⊤` is the identity. Injectivity of `ε.appTop`
gives `c = 1`. Then `φ` and `𝟙 L` have the same underlying module morphism,
so they are equal (`ObjectProperty.hom_ext`, `Subtype.ext`).

## 4. Abelian schemes (`relativeSection_appTop_injective`, `rigidifiedIsoUniqueness`)

`Langlands.AbelianScheme.relativeSection_appTop_injective` proves that the
rigidifying section
`ε_T = (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T`
is injective on global functions. Write `π_T` for the projection
`(relativeProjection A.X.hom).app T`. The published
`relativeSection_projection` gives `ε_T ≫ π_T = 𝟙`, so
`π_T.appTop ≫ ε_T.appTop = 𝟙`. `universalGlobalFunctions A T` makes
`π_T.appTop` an isomorphism. Hence `ε_T.appTop = inv π_T.appTop`
(`IsIso.eq_inv_of_hom_inv_id`), and `π_T.appTop` is a left inverse of
`ε_T.appTop`.

For the theorem, let `e e' : L ≅ M`. Step 3, with this injectivity, applies
to the endomorphism `e.hom ≫ e'.inv` of `L` and shows that it is `𝟙 L`.
Then `e.hom = (e.hom ≫ e'.inv) ≫ e'.hom = e'.hom`, and `Iso.ext` gives
`e = e'`.

## Scope

The new helper results are stated in general and may be reused. They are the
classification of step 1 for any scheme, and step 3 for any rigidifying
morphism injective on global functions. Step 1 gives existence of the scalar
for endomorphisms. It does not state uniqueness of the scalar or the
corresponding statement about units for automorphisms. The file proves
nothing about gluing, separatedness, Picard functors, or comparison between
ordinary and rigidified classes.
