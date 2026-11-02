# Full fpqc stack descent for actual line bundles: statement

`LineBundleFpqcStackStatement.{u}` is a proposition. Nothing in this module proves it.
It is the conjunction of two assertions about the published groupoids of actual line
bundles from `Langlands.AlgebraicGeometry.Picard.Groupoid`:

1. `PicardGroupoid.pseudofunctor.{u}.IsStack Scheme.fpqcTopology`: the pseudofunctor
   `X ↦ PicardGroupoid X` on `Scheme.{u}` is a stack for the fpqc topology;
2. for all `S X : Scheme.{u}` and every morphism `f : X ⟶ S`,
   `(PicardGroupoid.relative f).IsStack (Scheme.fpqcTopology.over S)`: the relative
   pseudofunctor `T ↦ PicardGroupoid (T ×_S X)` on the slice category `Over S` is a stack
   for the fpqc topology induced on `Over S`.

The only parameter is the universe `u`. The second assertion has no hypotheses on `S`,
`X` or `f`. In particular, `S` is not assumed to be a field, and `f` is not assumed to be
of finite type, quasi-compact, separated, flat or proper.

## The objects: actual line bundles and their isomorphisms

`PicardGroupoid X` is `Core (LineBundle X)`. `LineBundle X` is the full subcategory of
`X.Modules` on the sheaves `M` with `IsLocallyFreeRankOne M`: every point has an open
neighbourhood `U` such that `M.restrict U.ι` is isomorphic to the structure sheaf of `U`.
Taking the core keeps all of these sheaves as objects, with only their isomorphisms as
arrows. The pseudofunctor sends `g : Y ⟶ Z` to the core of the ordinary module pullback
`g^*`. Its unit and composition comparisons come from the ordinary pullback comparisons
`PicardGroupoid.pullbackId` and `PicardGroupoid.pullbackComp`. So the statement is about
the sheaves themselves and their isomorphisms. It does not concern isomorphism classes,
scalar cocycles or chosen trivializations.

## What `IsStack` requires

Mathlib's `CategoryTheory.Pseudofunctor.IsStack F J` (Stacks tag 026F in Mathlib's
attribution) extends `IsPrestack F J` and adds the field `essSurj_of_sieve`. Let `R` be a
`J`-covering sieve on an object `S`, and regard it as the family of all its arrows
`Y ⟶ S`. The category `F.DescentData` for this family has the following objects:

- an object `obj i` of `F` over the source of each arrow `i` of `R`;
- for every test object `Y` with a map `q : Y ⟶ S` and maps `f₁, f₂` from `Y` to the
  sources of two arrows of `R` that agree over `S`, a morphism `hom q f₁ f₂` from
  `f₁^* (obj i₁)` to `f₂^* (obj i₂)`.

These must satisfy three conditions. `pullHom_hom` says the `hom` maps are compatible
with further pullback along any `Y' ⟶ Y`. `hom_self` says the map is the identity when
`f₁ = f₂`. `hom_comp` is the cocycle condition. Every test object `Y` over `S` is allowed,
not only fibre products. A morphism of descent data is a family of morphisms
`obj i ⟶ obj' i` that commutes with every `hom`. The functor
`F.toDescentData : F(S) ⥤ F.DescentData` sends an object to its pullbacks, with the
canonical comparison isomorphisms.

- **Morphism descent (full faithfulness).** `IsPrestack F J` requires, for every `S` and
  all objects `M N` of `F(S)`, that the presheaf of morphisms `F.presheafHom M N` be a
  sheaf for `J.over S`. Its value at `p : T ⟶ S` is the type of morphisms
  `p^* M ⟶ p^* N`. By Mathlib's `isPrestackFor_iff_isSheafFor` and
  `IsPrestackFor.fullyFaithful`, this is equivalent to `F.toDescentData` being fully
  faithful for every covering sieve.
- **Effective descent (essential surjectivity).** `essSurj_of_sieve` requires
  `F.toDescentData` to be essentially surjective for every covering sieve `R`. In other
  words, every descent datum is isomorphic, as a descent datum, to the canonical datum
  of an object on `S`.

Together these make every such functor an equivalence of categories. For a family
`f i : X i ⟶ S` whose generated sieve covers, Mathlib's `isEquivalence_toDescentData`
gives the same equivalence.

For `F = PicardGroupoid.pseudofunctor`, all fibres are groupoids, so this reads as
follows. A morphism of descent data is a family of isomorphisms of line bundles compatible
over all test schemes. Full faithfulness says that any such compatible family between the
pullbacks of two line bundles `M` and `N` on `S` comes from exactly one isomorphism
`M ≅ N`. Essential surjectivity says that any family of line bundles on the members of
the covering, glued by compatible isomorphisms satisfying the cocycle condition, comes
from a line bundle on `S`, up to an isomorphism of descent data.

## Covering sieves and fpqc covering families

`Scheme.fpqcTopology` is `fpqcPrecoverage.toGrothendieck`, where
`fpqcPrecoverage = propQCPrecoverage @Flat = qcPrecoverage ⊓ Scheme.precoverage @Flat`.
Its covering families are jointly surjective families of flat morphisms that are also
quasi-compact covers (`QuasiCompactCover`, attributed in Mathlib to Stacks tag 022B):
every affine open of the target is covered by finitely many images of quasi-compact opens
of the members. This is the notion of fpqc covering used in Stacks, Topologies,
Definition 9.1, which Descent Proposition 5.2 refers to. Mathlib derives `HasIsos`,
`IsStableUnderBaseChange` and `IsStableUnderComposition` for `fpqcPrecoverage`.

In the generated topology, a sieve covers exactly when it contains a covering family.
Descent along a presieve depends only on the sieve it generates
(`isStackFor_iff_of_sieve_eq`, `IsStackFor_generate_iff`). With the three stability
properties, Mathlib's `IsStack.of_precoverage` shows that `IsStack` for the generated
topology follows from `IsStackFor` along every fpqc covering family. Conversely, `isStackFor`
applies `IsStack` to the covering sieve generated by any such family. So the first
conjunct is equivalent to effective descent with full faithfulness along every fpqc
covering family `{Uᵢ → S}`, for every scheme `S`. That is the form in the source. Mathlib's
descent data use all test objects `Y` rather than only the fibre products `Uᵢ ×_S Uⱼ`
and `Uᵢ ×_S Uⱼ ×_S Uₖ`. Schemes have fibre products, and Mathlib's
`DescentData'.descentDataEquivalence` identifies the two descriptions as equivalent
categories.

## Source route

The source is The Stacks Project, *Descent*, version ed88ff78 compiled 14 July 2026
(`stacks-descent-ed88ff78-2026`). Printed page numbers coincide with PDF page numbers.

- **Proposition 5.2 (Tag 023T), pp.18–19.** Let `S` be a scheme and `{φᵢ : Uᵢ → S}` an
  fpqc covering. Then any descent datum on quasi-coherent sheaves for the covering is
  effective, and the functor from quasi-coherent `𝒪_S`-modules to descent data is fully
  faithful. The proof establishes faithfulness, fullness and essential surjectivity in
  turn. It reduces to Lemma 5.1 (Tag 023S, pp.17–18), the case of a standard fpqc
  covering of an affine scheme, which restates Proposition 3.9 for a faithfully flat
  ring map.
- **Line bundles are quasi-coherent.** An `IsLocallyFreeRankOne` sheaf is locally
  isomorphic to the structure sheaf, so it is quasi-coherent. The descent datum of a
  family of line bundles, whose `hom` maps are isomorphisms of module pullbacks, is
  therefore a descent datum of quasi-coherent sheaves.
- **Morphisms.** By the full faithfulness in Proposition 5.2, a compatible family of
  isomorphisms `φᵢ^* M ≅ φᵢ^* N` comes from a unique module map `M → N`. The inverse
  family is also compatible, so it descends too. By uniqueness the two descended maps are
  mutually inverse, so the map `M → N` is an isomorphism. This is full faithfulness on
  the cores.
- **Objects.** By the effectivity in Proposition 5.2, a descent datum of line bundles is
  isomorphic to the canonical datum of a quasi-coherent sheaf `ℱ` on `S`. Then each
  `φᵢ^* ℱ` is isomorphic to a line bundle, so it is finite locally free. By **Lemma 7.6
  (Tag 05B2), p.22**, `ℱ` is a finite locally free `𝒪_S`-module. The proof there uses
  Lemma 7.5 (flatness descends) and Lemma 7.3 (finite presentation descends). Lemma 7.6
  does not itself assert that a fixed rank descends.
- **Rank one (derived step).** The proof of **Lemma 7.4 (Tag 082U), p.22** uses the
  equality `dim_{κ(x)} ℱ_x ⊗ κ(x) = dim_{κ(xᵢ)} (φᵢ^* ℱ)_{xᵢ} ⊗ κ(xᵢ)` for a point `xᵢ`
  of `Uᵢ` over `x`. It holds because the right-hand fibre is the base change of the
  left-hand one along the residue field extension `κ(x) → κ(xᵢ)`. For a finite locally
  free `ℱ`, the left side is the rank of `ℱ` near `x`. The right side is the rank of
  `φᵢ^* ℱ` at `xᵢ`, which is `1`. A covering is jointly surjective, so every `x ∈ S` has
  such a point `xᵢ`. Hence `ℱ` has rank one everywhere, which means it is locally
  isomorphic to `𝒪_S`, i.e. `IsLocallyFreeRankOne ℱ`. This combination of Lemma 7.6 with
  the fibre-dimension equality is derived here; the source does not state it as a single
  result. The isomorphism of descent data from Proposition 5.2 is then an isomorphism of
  line-bundle descent data, which gives essential surjectivity on the cores.

## The relative assertion as base change

`PicardGroupoid.relative f` is
`(relativeSpace f).op.toPseudofunctor.comp PicardGroupoid.pseudofunctor`, where
`relativeSpace f = Over.pullback f ⋙ Over.forget X` sends `T : Over S` to Mathlib's
chosen fibre product `pullback T.hom f`, i.e. `T ×_S X`. A morphism `T ⟶ T'` over `S`
goes to the induced map `T ×_S X ⟶ T' ×_S X`. The relative pseudofunctor pulls back along
these maps, with comparisons given by the same ordinary pullback comparisons
`pullbackId` and `pullbackComp`. Its fibre over `T` is `PicardGroupoid (T ×_S X)`, the
actual line bundles on the actual fibre product.

By `GrothendieckTopology.mem_over_iff`, a sieve on `T` in `Over S` covers for
`Scheme.fpqcTopology.over S` exactly when its image under `Sieve.overEquiv` is an fpqc
covering sieve on the scheme `T.left`. The statement quantifies over the whole slice
category `Over S`: all `T`, all covering sieves, all test objects over `S` and all
compatible descent data. An fpqc covering family `{Tᵢ → T}` over `S` base changes to
`{Tᵢ ×_S X → T ×_S X}`. This is again an fpqc covering because fpqc coverings are stable
under base change (Mathlib's `IsStableUnderBaseChange` for `fpqcPrecoverage`). The functor
`T ↦ T ×_S X` preserves the fibre products over `T` that appear in descent data. So
relative descent data for `{Tᵢ → T}` amount to line-bundle descent data for the
base-changed covering of `T ×_S X`. Mathematically, the second conjunct therefore follows
from the first. The Lean statement nevertheless asserts it explicitly, as a separate
conjunct, for every `f`.

## Provenance and scope

This is a statement of standard results from the cited source. The groupoid it concerns
is the published internal construction `PicardGroupoid`, which implements the underlying
groupoid-valued pseudofunctor in Artin, *Versal deformations and algebraic stacks* (1974),
Appendix item 2, printed pages 186–187 (`artin-1974-versal-deformations-algebraic-stacks`).
No proof is given or claimed. The Library has narrower results in
`Langlands.AlgebraicGeometry.Modules`. `LineBundleFlatDescentStatements` states descent
along a single quasi-compact (for isomorphisms) or affine (for objects) flat surjection.
`UnitCocycleDescentStatements`, `UnitCocycleDescentEffectiveProof` and
`UnitCocycleDescentUniquenessProof` concern unit cocycles along affine flat surjections.
`TrivialIsoDescentStatement` and `TrivialIsoDescentProof` concern isomorphisms of globally
trivial modules. None of them is an `IsStack` assertion for arbitrary fpqc covering
sieves, so they do not establish this proposition.
