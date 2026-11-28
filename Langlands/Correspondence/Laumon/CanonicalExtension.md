# The Katz–Gabber canonical extension: the bridge (b4)

Laumon (1987), Théorème (2.2.2.2), p. 157, after Katz (1986). Write `ξ` for the punctured
henselian trait at `0`, `ξ → 𝔾_{m,k}` for its map to the punctured line, and
`ξ^{mod ∞} : π₁(ξ, ξ̄) → π₁(𝔾_m, ξ̄)^{mod ∞}` for the map into the quotient classifying the covers
tamely ramified at `∞`. Then `ξ^{mod ∞}` and its geometric version
`ξ̄^{mod ∞} : π₁(ξ ⊗ k̄, ξ̄) → π₁(𝔾_m ⊗ k̄, ξ̄)^{mod ∞}` are injective. `ξ̄^{mod ∞}` has a unique
continuous retraction `r̄`, and `ξ^{mod ∞}` has a unique continuous retraction `r` extending `r̄`.
For a `π₁(ξ, ξ̄)`-module `V` (in the sense of (2.1.2)), the *canonical extension* of `V` is the
lisse `ℚ̄_ℓ`-sheaf `F` on `𝔾_m`, tamely ramified at `∞`, with `F_ξ̄ = V` and with
`π₁(𝔾_m, ξ̄)^{mod ∞}` acting on `F_ξ̄` through `r` and the action of `π₁(ξ, ξ̄)` on `V`. Laumon
records that if `V` has finite geometric monodromy, so does `F`, and that the canonical
extension is functorial in `V` and exact.

Katz's Corollary (1.4.7), p. 81, identifies the arithmetic local group
`Gal(K((T⁻¹))^sep/K((T⁻¹)))` with the arithmetic quotient `π₁(𝔾_{m,K})(special)` by Main
Theorem (1.4.1). In the diagram of short exact sequences in (1.4.9), p. 82, the arithmetic
isomorphism is in the middle and the geometric isomorphism between
`π₁(Spec K^sep((T⁻¹)))` and `π₁(𝔾_{m,K^sep})(special)` is on the left. The right-hand map is the
identity of `Gal(K^sep/K)`. Corollary (1.4.10), pp. 82–83, gives uniqueness of the retractions on
the tame-at-zero quotients using the unique `p`-Sylow subgroup of local inertia. Corollary
(1.4.11), p. 83, gives a retraction on the full arithmetic fundamental group by composing
with the projection onto the special quotient.

Lemmas (1.5.3)–(1.5.4), p. 84, Theorem (1.5.6), p. 85, and Corollary (1.5.7), pp. 85–86,
pass to lisse sheaves of modules over finite and profinite adic rings. They give the canonical
extension, an exact `Λ`-linear quasi-inverse of restriction compatible with linear algebra,
change of coefficients, extension of the ground field, `[N]^*`, `[N]_*` and translations. Its
monodromy is that of `V` composed with the inverse of the arithmetic special-quotient
isomorphism.

This module states these facts for a finite field `k`, the ends `e : FourierEnd` and the
henselian end traits of `Langlands.Correspondence.Laumon.Traits`. The fundamental groups and the
quotients by kernels follow the conventions of `Langlands.Correspondence.Laumon.TameCovers`.

## The retraction

`IsKatzGabberRetraction k e r`, for a homomorphism
`r : π₁(𝔾_m, gmEndPoint k e) → Gal(Ω/endField k)` (`Ω = endGenericClosure k`), says:

- `r` is continuous for the profinite topology of `Aut (fiber _)` and the Krull topology.
- `r` is trivial on `coverKernel (gmEndPoint k e) (IsTameCoverAt k e.opposite)`, so it is defined
  on the quotient classifying the covers tame at the opposite end (Laumon's `π₁^{mod ∞}` for
  `e = 0`, Katz's `π₁(tame at 0)` for `e = ∞`).
- `r ∘ gmLocalMonodromy k e` is the identity.
- `r` maps the geometric fundamental group `gmGeometricSubgroup k (gmEndPoint k e)` into the
  inertia group, the automorphisms fixing `endUnramifiedField k`.

The last condition is Katz's "maps `π₁(𝔾_m ⊗ K^sep)(tame at 0)` to
`π₁(Spec K^sep((T⁻¹)))`" in (1.4.10)(2). By the geometric clause of
`KatzGabberRetractionStatement` below, it is equivalent to Laumon's "`r` extends `r̄`".
It also makes `r` descend to the constant-field quotients. Since `gmLocalMonodromy k e`
induces the identity on `Gal(k̄/k)` and `r ∘ gmLocalMonodromy k e` is the identity,
the descended map of `r` is the identity on `Gal(k̄/k)` as well.

### `KatzGabberRetractionStatement`

For a finite field `k` and every end `e`, with `N` the kernel of the quotient classifying the
covers tame at `e.opposite`:

1. if `gmLocalMonodromy k e σ ∈ N` then `σ = 1`. This is the injectivity of `ξ^{mod ∞}`, and
   with it of `ξ̄^{mod ∞}`;
2. there is exactly one Katz–Gabber retraction `r`;
3. the kernel of `r` is `coverKernel (gmEndPoint k e) (specialCover k e)`, the kernel of the
   special quotient. Since `r` retracts `gmLocalMonodromy k e`, `r` thus induces the inverse of
   the isomorphism from the Galois group of the end field onto the special quotient of
   `π₁(𝔾_m)` (Katz (1.4.9));
4. the restriction of `r` to the geometric fundamental group is the unique continuous
   homomorphism `r'` from the geometric fundamental group to the inertia group that is trivial on
   `N` and satisfies `r'(gmLocalMonodromy k e σ) = σ` for inertia elements `σ`. This is `r̄`,
   unique by (1.4.10)(1), since the inertia group has a unique pro-`p` Sylow subgroup.

### The retraction as a parameter

The canonical extension takes a retraction as a parameter.
`CanonicalExtensionMonodromyStatement` quantifies over every `r` with
`IsKatzGabberRetraction k e r`. By clause 2 of `KatzGabberRetractionStatement` there is exactly
one.

## The canonical extension

- `gmMonodromy k ℓ e F` is the monodromy representation of `π₁(𝔾_m, gmEndPoint k e)` on the stalk
  of a lisse sheaf `F` on `𝔾_m` at `gmEndPoint k e`, for weil-conjectures's
  `ProEtale.universalLisseMonodromy`. `gmStalkMap k ℓ e φ` is the stalk map of a morphism.
- `continuous_dual_apply_comp` shows that the matrix coefficients `g ↦ φ(V(r g) v)` are
  continuous for a continuous `r` and a representation `V` with `IsLadicContinuous`.
- `exists_lisse_monodromy_comp` gives, for a continuous homomorphism `r` and a continuous
  representation `V` (carrier in the universe of the stalks), a lisse sheaf on `𝔾_m` with a
  linear isomorphism of its stalk at `gmEndPoint k e` onto `V` carrying `gmMonodromy` to `V ∘ r`.
  The monodromy of `universalLisseMonodromy` is an equivalence at every geometric point
  (`ProEtale.universalLisseMonodromy_isEquivalenceAt`), whose hypotheses on `𝔾_m` are the
  instances of `TameCovers`.
- `canonicalExtension k ℓ e r hr V hV` is the lisse sheaf chosen by `exists_lisse_monodromy_comp`.
  `canonicalExtensionStalkEquiv` is its stalk identification with `V`, and
  `canonicalExtensionStalkEquiv_monodromy` and `canonicalExtensionStalkEquiv_symm_monodromy`
  say that it carries `π₁(𝔾_m)` to `V ∘ r`.
- `canonicalExtensionMap k ℓ e r hr hV hW f` is the morphism of canonical extensions whose stalk
  map is the intertwiner `f : V → W` under the stalk identifications. It is chosen by the
  fullness of the monodromy at `gmEndPoint k e`.

The construction takes the homomorphism `r` and its continuity as parameters: the canonical
extension is the construction from a given retraction. With the Katz–Gabber retraction it is
Laumon's canonical extension, as its stalk at `gmEndPoint k e` is `V` with `π₁(𝔾_m)` acting
through `r`. The construction needs only the continuity of `r`, so it can be formed without the
retraction theorem. The properties below are those of the Katz–Gabber retraction. The input is a
`Langlands.FiniteRepresentation` of the Galois group of the end field with `IsLadicContinuous`.
Laumon's finite coefficient field condition ((2.1.2), p. 152) follows here from continuity.
In a basis of the representation, `PadicAlgCl.exists_finiteDimensional_forall_mem` puts all
matrix entries of the compact Galois group's action in one finite extension of `ℚ_ℓ`. The
span of that basis over this extension gives the model.

**From Katz's completed formulation to the henselian one.** Katz's equivalence and retraction
concern the punctured formal neighbourhood `Spec K((T⁻¹))`. Laumon (2.2.2.2) uses the henselian
trait `ξ`. Here the local Galois group is that of the henselian end field `endField k`, and the
local monodromy of a lisse sheaf is the field monodromy (bridge (b1),
`Langlands.Correspondence.Laumon.FieldMonodromy`) of its pullback along
`puncturedEndToGm k e`. In bridge (b2),
`Langlands.Henniart.Laumon.henselianCompletionGalois` proves
`HenselianCompletionGaloisStatement` of `Langlands.Correspondence.Laumon.Completion`.
Restriction from the Galois group of the completion `LaurentSeries k = k((t))` to that of
`endField k` is an isomorphism of topological groups. `HenselianCompletionRamificationStatement`
states the corresponding compatibility of inertia and wild inertia. Katz (1.4.8), pp. 81–82,
uses the same completion principle for the geometric field `K^sep ⊗_K K((T⁻¹))`. This field is
the union of the `K'((T⁻¹))` over finite Galois constant extensions `K'/K`, with completion
`K^sep((T⁻¹))`. These comparisons transport Katz's retractions and the corresponding
representations to the henselian end trait. The end `e = ∞` uses the coordinate `1/x`, as Katz
does, and `e = 0` uses `x`, as Laumon does.

### `CanonicalExtensionMonodromyStatement`

Let `k` be a finite field, `ℓ` a prime distinct from `ringChar k` as in Laumon (0.1), p. 134,
`e` an end and `r` a Katz–Gabber retraction at `e`. Write `F_V` for
`canonicalExtension k ℓ e r _ V _` for a continuous representation `V` of `Gal(Ω/endField k)`
whose carrier is in the universe of the stalks.

1. **Local monodromy.** The field monodromy of the pullback of `F_V` to `η_e` is isomorphic to `V`
   (Laumon: `F_ξ̄ = V`).
2. **Tameness.** `F_V` is tame at `e.opposite` (`IsTameLisseAt`).
3. **Speciality.** The kernel of the special quotient acts trivially on the stalk of `F_V`
   (Katz (1.5.2), (1.5.5)).
4. **Uniqueness.** Every lisse sheaf on `𝔾_m` on whose stalk the kernel of the special quotient
   acts trivially, and whose local monodromy at `e` is isomorphic to `V`, is isomorphic to `F_V`
   (Katz (1.5.6): restriction is fully faithful and essentially surjective on special sheaves).
5. **Finite geometric monodromy.** If the inertia group acts on `V` through a finite set of
   operators, the geometric fundamental group of `𝔾_m` acts on the stalk of `F_V` through a finite
   set of operators. This is the property Laumon records after (2.2.2.2).
6. **Functoriality.** For an intertwiner `f : V → W`, the stalk map of `canonicalExtensionMap f` is
   `f` under the stalk identifications, and it is the only morphism `F_V → F_W` with this
   property. Hence `V ↦ F_V`, `f ↦ canonicalExtensionMap f` preserves identities and composition
   and is fully faithful.
7. **Exactness.** For intertwiners `f : V₁ → V₂`, `g : V₂ → V₃` with `f` injective, `g`
   surjective and `range f = ker g`, the composite of `canonicalExtensionMap f` and
   `canonicalExtensionMap g` vanishes, and the resulting short complex of adic sheaves on `𝔾_m` is
   short exact.
8. **Tensor products.** For continuous `V` and `W`, the tensor representation `V ⊗ W` is
   continuous, and the tensor product of `F_V` and `F_W` is lisse. The canonical extension of
   `V ⊗ W` is isomorphic to that tensor product, formed with `CategoryTheory.Mod.tensorLeft`
   as in `LadicFieldMonodromyStatement`.
9. **Constant twists.** For every lisse sheaf `L` on `Spec k`, the local monodromy of its pullback
   to `η_e` along `puncturedEndToBase k e` is continuous. Its canonical extension is isomorphic
   to the pullback of `L` to `𝔾_m` along `gmStructure k`. With clause 8 this identifies the
   canonical extension of `V` tensored with that local monodromy with `F_V` tensored with the
   pullback of `L` to `𝔾_m`. Taking `L = unramifiedLine k ℓ χ` from
   `Langlands.Correspondence.Laumon.UnramifiedLines` gives the twist by an unramified character
   `χ`.
10. **Base change.** For every finite extension `k₁/k` there are compatible data `j`, `ι`, `res`
    with `IsEndGaloisBaseChange k k₁ j ι res`. For every such choice the restriction of a
    continuous `V` along `res` is continuous. Along any Katz–Gabber retraction `r₁` over `k₁`,
    its canonical extension is isomorphic to the pullback of `F_V` along `gmBaseChange k k₁`
    (Katz (1.5.6)(3), extension of the ground field).

`IsEndGaloisBaseChange k k₁ j ι res` requires the following four conditions on the maps of end
fields and separable closures and the homomorphism of their Galois groups.

1. The ring map `j` acts coefficientwise via `algebraMap k k₁` under the inclusions of both end
   fields in their Laurent-series fields.
2. The ring map `ι` of separable closures extends `j` along the algebra maps from the two end
   fields.
3. For each automorphism `τ` of the separable generic closure over `endField k₁`, its
   restriction `res τ` satisfies `ι ∘ res τ = τ ∘ ι`.
4. `res` is continuous for the Krull topologies.

`lineBaseChange k k₁ : 𝔸¹_{k₁} → 𝔸¹_k` is the base change map of affine lines (Mathlib's
`AffineSpace.map`). `gmBaseChange k k₁` is its restriction to `𝔾_m`, which exists by
`range_gmBaseChange_subset`.

Clauses 1–5 are Laumon's description of the canonical extension. Clauses 6–8 and 10 are the
properties of Katz (1.5.6)–(1.5.7) that Laumon uses ("fonctoriel en `V`", "foncteur exact"). They
appear in the bridge (b4) of the design note
`notes/henniart/laumon-local-fourier-weil-conjectures-design.md` as "base change, exactness and
commutation with pullback of constant twists". Clause 9 is the special case of the uniqueness for
sheaves pulled back from `Spec k`. These sheaves are special because the special quotient of
`π₁(𝔾_m)` maps onto `Gal(k̄/k)` compatibly with `r`.

The proof route is that of Katz. For finite coefficients, (1.4.1) and Lemmas (1.5.3)–(1.5.4) give
the equivalence of special lisse sheaves with local ones. Since the canonical extension is
defined here directly from the monodromy equivalence of weil-conjectures at `gmEndPoint k e`,
the remaining inputs are the comparison of `gmMonodromy` with the field monodromy of pullbacks
(`ProEtale.isCompatible_universalLisseMonodromy`) and clause 3 of
`KatzGabberRetractionStatement`.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.SpecialCovers` and
`Langlands.Correspondence.Laumon.UnramifiedLines` (for `puncturedEndToBase`). From the Library it
also uses `fieldMonodromyRepresentation` of `Langlands.Correspondence.Laumon.FieldMonodromy`,
`IsLadicContinuous` of `Langlands.Correspondence.HenniartLadicClasses`, and
`Langlands.FiniteRepresentation.restrict`. From weil-conjectures it uses
`AlgebraicGeometry.ProEtale.universalLisseMonodromy`,
`AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt`,
`AlgebraicGeometry.ProEtale.LisseMonodromy.rep`,
`AlgebraicGeometry.ProEtale.LisseMonodromy.StalkSpace`, `AlgebraicGeometry.ProEtale.lisseStalk`,
`AlgebraicGeometry.WeilCoefficients.toModuleCat`, `AlgebraicGeometry.ProEtale.LisseSheaf`,
`AlgebraicGeometry.ProEtale.LisseSheaf.upperStar`, `AlgebraicGeometry.ProEtale.AdicSheaf`,
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf`, `AlgebraicGeometry.Scheme.FiniteEtale.fiber` and
`AlgebraicGeometry.affineLine` and `CategoryTheory.Mod.tensorLeft`. The cited
`AlgebraicGeometry.ProEtale.isCompatible_universalLisseMonodromy` and
`PadicAlgCl.exists_finiteDimensional_forall_mem` are also from weil-conjectures.
Under `#print axioms`, these declarations, every declaration of this module, and the cited
Library theorem `Langlands.Henniart.Laumon.henselianCompletionGalois` depend only on `propext`,
`Classical.choice` and `Quot.sound`.
