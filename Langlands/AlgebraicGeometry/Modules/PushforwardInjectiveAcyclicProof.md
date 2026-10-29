# Pushforwards of injective scheme modules are acyclic: proof

Author: Worker 727.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement`,
which it imports unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.pushforwardInjectiveAcyclic` is the theorem

```lean
theorem pushforwardInjectiveAcyclic : PushforwardInjectiveAcyclicStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says: for all schemes `X Y : Scheme.{u}`, every
morphism `h : X ⟶ Y` (no hypothesis on `h`), every `J : X.Modules` with `Injective J` and
every `n : ℕ`,

```lean
IsZero ((DerivedSections.cohomology Y (n + 1)).obj ((Scheme.Modules.pushforward h).obj J)) ∧
  ∀ (R : CommRingCat.{u}) (g : Y ⟶ Spec R),
    IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj
      ((Scheme.Modules.pushforward h).obj J))
```

The theorem uses no hypothesis beyond the statement's. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Route of the proof

The proof follows the Stacks route: an injective module is flasque, a pushforward of a
flasque module is flasque, and a flasque module has no higher cohomology. Two steps use
different arguments than Stacks.

1. **Injective modules are flasque** (`isFlasque_of_injective`). Stacks 01EA uses the
   extension by zero `j_! 𝒪_U`, which Mathlib does not have. The Lean proof works on an
   arbitrary site instead (`surjective_map_of_injective`). Let `f : U ⟶ V` be a
   monomorphism of the site and `t` a section of `M` over `U`. Let `F_U` be the free
   presheaf of modules on the representable presheaf `yoneda.obj U`. Then `t` corresponds to
   a map `F_U ⟶ M` (`PresheafOfModules.freeYonedaEquiv`). The map `F_U ⟶ F_V` induced by
   `f` is a monomorphism, because `Finsupp.mapDomain` along an injective map is injective.
   Sheafification preserves this monomorphism, since it preserves finite limits. By the
   sheafification adjunction, `t` gives a map from the sheafification of `F_U` to `M`. By
   injectivity of `M` it extends along the monomorphism to the sheafification of `F_V`.
   The extension corresponds to a section `s` of `M` over `V`. Naturality of
   `freeYonedaEquiv` in the representing object then shows that `s` restricts to `t`. For a
   scheme, an inclusion of opens is a monomorphism, so every restriction map of an injective
   `𝒪_X`-module is surjective.
2. **Pushforwards of flasque modules are flasque** (`isFlasque_pushforward`). The
   restriction maps of `h_* M` are restriction maps of `M` between preimage opens, which is
   the argument used in Stacks 0FKS.
3. **Flasque modules are acyclic** (`isZero_cohomology_succ_of_isFlasque`). Stacks 09SY
   uses Zorn's lemma to show two facts: global sections are exact on short exact sequences
   whose first term is flasque, and in such a sequence the third term is flasque when the
   first two are. Lean takes both facts from Mathlib's `Topology.Sheaves.Flasque`, which
   states them for sheaves of abelian groups (`TopCat.Sheaf.IsFlasque.epi_of_shortExact`,
   `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`). The proof transfers them to
   `𝒪_X`-modules through the forgetful functor `toAbSheaf X`, which is exact: Mathlib shows
   that it preserves finite limits, and the Library's
   `ClosedImmersionHigherDirectImageVanishing.toSheaf_preservesFiniteColimits` shows that it
   preserves finite colimits. Then a dimension shift proves vanishing in each degree
   `n + 1`, by induction on `n`. Embed a flasque `F` in its chosen injective object `I` with
   cokernel `Q`. Then `Q` is flasque, and `R^{m+1} Γ(I) = 0` for all `m`
   (`Functor.isZero_rightDerived_obj_injective_succ`). The Library's connecting morphism
   `Langlands.Cohomology.DerivedPlus.rightDerivedδ` for `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` is therefore
   an epimorphism `R^m Γ(Q) ⟶ R^{m+1} Γ(F)` (`epi_rightDerivedδ_of_isZero`).
   - For `n = 0`: `R^0 Γ(I) ⟶ R^0 Γ(Q)` is an epimorphism, because it is identified with
     `Γ(I) ⟶ Γ(Q)` (`Functor.rightDerivedZeroIsoSelf`) and global sections are exact here.
     Its composite with `rightDerivedδ` is zero (`rightDerived_map_comp_δ`). So `rightDerivedδ`
     is a zero epimorphism, and its target `H^1(F)` is zero.
   - For `n + 1`: the target of the epimorphism `rightDerivedδ : H^{n+1}(Q) ⟶ H^{n+2}(F)` is
     zero because `H^{n+1}(Q) = 0` by the induction hypothesis applied to the flasque `Q`.

   The connecting morphism is built from Mathlib's derived category, so the proof locally
   installs `HasDerivedCategory.standard` for `X.Modules` and `ModuleCat Γ(X, ⊤)`. This
   choice does not occur in the statement, whose `cohomology` uses injective resolutions.
4. **Conclusion** (`pushforwardInjectiveAcyclic`). Steps 1-3 give the first conjunct. For
   the second, the Library's `DerivedSections.relativeCohomologyRestrictScalarsIso g (n + 1)`
   identifies `relativeCohomology g (n + 1)` with `cohomology Y (n + 1)` followed by
   restriction of scalars along `DerivedSections.structureRingHom g`. Restriction of scalars
   sends zero modules to zero modules (`Functor.map_isZero`).

## Auxiliary results

All helpers are in namespace
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic`.

- `mono_free_map R₀ φ`: for a presheaf of rings `R₀` on a category `C` and a monomorphism
  `φ : F ⟶ G` of presheaves of types, `(PresheafOfModules.free R₀).map φ` is a monomorphism.
- `freeYonedaEquiv_apply g`: `freeYonedaEquiv g` is `g` evaluated at `freeMk (𝟙 U)`
  (definitional).
- `freeYonedaEquiv_free_map_yoneda_map_comp f g`: for `f : U ⟶ V` and
  `g : free (yoneda V) ⟶ M`, `freeYonedaEquiv (free.map (yoneda.map f) ≫ g)` equals
  `M.map f.op (freeYonedaEquiv g)`. The proof uses naturality of the free-module adjunction
  and Mathlib's `yonedaEquiv_naturality`.
- `surjective_map_of_injective R M f`: for a site `(C, J)` with
  `[HasSheafify J AddCommGrpCat.{v}]` and `[J.WEqualsLocallyBijective AddCommGrpCat.{v}]`, a
  sheaf of rings `R`, an injective `M : SheafOfModules R` and a monomorphism `f : U ⟶ V`,
  the map `M.val.map f.op` is surjective (step 1).
- `toAbSheaf X` (abbreviation): `SheafOfModules.toSheaf X.ringCatSheaf`, typed as a functor
  `X.Modules ⥤ TopCat.Sheaf AddCommGrpCat X`. Three instances record that it preserves zero
  morphisms, finite limits and finite colimits. The abbreviation is needed because the
  category instances on `X.Modules` and `TopCat.Sheaf` do not match the generic ones
  syntactically, so instance search would otherwise fail.
- `isFlasque_of_injective I`: an injective `I : X.Modules` has flasque underlying presheaf.
- `isFlasque_pushforward h M`: if `M` is flasque, then so is `(Scheme.Modules.pushforward
  h).obj M`.
- `injectiveSc F`: the short complex `F ⟶ Injective.under F ⟶ cokernel (Injective.ι F)`.
  `injectiveSc_shortExact F` proves that it is short exact, and
  `toSheaf_injectiveSc_shortExact F` proves that its image under `toAbSheaf X` is short exact.
- `isFlasque_cokernel F`: for flasque `F`, the cokernel `cokernel (Injective.ι F)` is
  flasque.
- `epi_globalSections_map F`: for flasque `F`, the global-sections map of
  `Injective.under F ⟶ cokernel (Injective.ι F)` is an epimorphism.
- `isZero_cohomology_succ_of_isFlasque n F`: for flasque `F : X.Modules`,
  `IsZero ((DerivedSections.cohomology X (n + 1)).obj F)` (step 3).

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered
source `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`), file `cohomology.tex`:

- Lemma 01EA (`lemma-injective-restriction-surjective`, lines 714-725): restriction maps
  of an injective `𝒪_X`-module are surjective. Lean proves this with free presheaves of
  modules on representables and sheafification instead of `j_! 𝒪_U` (step 1).
- Lemma 09SX (`lemma-injective-flasque`, lines 1902-1910): injective modules are flasque,
  a reformulation of 01EA.
- Lemma 09SY (`lemma-flasque-acyclic`, lines 1912-1958): flasque modules are acyclic. Lean
  replaces the Zorn argument by Mathlib's flasque lemmas for abelian sheaves, and the
  appeal to the acyclic-subcategory lemma by the dimension shift of step 3.
- The proof of Lemma 0FKS (`lemma-godement-resolution`, lines 7049-7050) notes that
  pushforwards of flasque sheaves are flasque (step 2).

The statement's Markdown records the errata check for these sources. No comment changes a
statement used here.
