# The dual pullback comparison is invertible for finite local bases

Lean module: `Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree`.

## Main result

For a morphism of schemes `f : X ⟶ Y` and a module sheaf `M` on `Y` with local
generating data `q : SheafOfModules.LocalGeneratorsData.{u} M` such that
`q.IsLocallyFreeData` and `q.IsFiniteType` hold, the theorem
`Langlands.Scheme.Modules.isIso_dualPullbackComparison_of_localGeneratorsData`
proves

`IsIso (Langlands.Scheme.Modules.dualPullbackComparison f M)`.

Here `dualPullbackComparison f M : f^*(M^∨) ⟶ (f^*M)^∨` is the canonical
comparison that the Library defines in `Langlands.AlgebraicGeometry.ModuleDualPullback`,
and `M^∨ = Langlands.Scheme.Modules.dual M` is the internal-hom dual into the
structure module. The data `q` gives an open cover `q.X` of `Y`. On each member
`q.X i`, the restriction of `M` is free on a finite set of generators. So the result
is the standard fact that pullback commutes with dualisation for finite locally free
modules. The registered Stacks Project snapshot
`stacks-relative-differentials-internal-hom-2026-10-21` (page `01CM`, Section 17.22)
contains the related Lemma 17.22.5. That lemma needs a flat morphism and a finitely
presented module, and treats an arbitrary second module. Here the morphism `f` is
arbitrary, the module is finite locally free, and the second module is the structure
module. The Lean proof below is self-contained and does not follow the Stacks stalk
argument.

## Proof structure

The Lean proof is local on the source, then on the target, and then reduces to the
free case.

1. **Locality on the source** (`isIso_of_isIso_restrict`). A morphism of module
   sheaves on `X` is invertible if each point has an open neighbourhood `U` on which
   its restriction `restrictFunctor U.ι` is invertible. The proof turns the morphism
   into a morphism of abelian sheaves. Mathlib's `restrictStalkNatIso` identifies each
   stalk with a stalk of the restriction, and
   `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` finishes the proof. The forgetful
   functor to presheaves reflects isomorphisms.

2. **Finite retracts and isomorphisms** (`isIso_dualPullbackComparison_of_sum`,
   `isIso_dualPullbackComparison_of_iso`). Suppose `P` has maps `ι k : N k ⟶ P` and
   `π k : P ⟶ N k`, for a finite index type, with `∑ π k ≫ ι k = 𝟙 P`. If each
   comparison for `N k` is invertible, then so is the comparison for `P`. The inverse
   is written down explicitly. The proof uses the Library naturality lemma
   `dualPullbackComparison_naturality` and additivity of `dualMap` and of pullback.
   The instance `isIso_dualMap` shows that `dualMap` preserves isomorphisms.

3. **Section-level identities** (`internalHomSectionsEquiv_id`, `_comp`, `_sum`,
   `localHomPullback_id`). Under the Library's identification
   `internalHomSectionsEquiv`, local identities, composites and finite sums of local
   homomorphisms correspond to the same operations on the restricted modules.
   The finite-sum proof reuses `internalHomSectionsEquiv_zero` and
   `internalHomSectionsEquiv_add` from `ModuleDual`.
   Local functional pullback `localHomPullback` sends identities to identities.

4. **The structure module** (`unitToDual`, `isIso_unitToDual`,
   `pullback_unitToDual_comp`, `isIso_dualPullbackComparison_unit`). The map
   `unitToDual X : 𝒪_X ⟶ 𝒪_X^∨` is the morphism out of the unit module (via
   `SheafOfModules.unitHomEquiv`) that corresponds to the global section given by the
   identity local endomorphisms. On sections over `U` it sends `r` to
   `r • 𝟙`. It is invertible because it is bijective on every open:

   - **Injective:** evaluate at `1`.
   - **Surjective:** a local endomorphism `h` of the structure module equals
     multiplication by `h(1)`, by `Γ(X, V)`-linearity and compatibility with
     restriction (`internalHomEval_restrict`).

   The proof of `pullback_unitToDual_comp` passes through the pullback–pushforward
   adjunction, the Library lemmas `homEquiv_dualPullbackComparison` and
   `pullbackUnitAdjunction`, and injectivity of `unitHomEquiv`. It shows

   `g^*(unitToDual Y) ≫ dualPullbackComparison g 𝒪_Y =
     pullbackUnitIso.hom ≫ unitToDual X ≫ dualMap pullbackUnitIso.hom`.

   Every map in this identity other than the comparison is invertible. So the
   comparison for `𝒪_Y` is invertible for every `g`.

5. **Open immersions** (`pullbackFullyFaithfulOfIsIso`,
   `localDualPullback_bijective`, `isIso_morphismRestrict_image`,
   `isIso_dualPullbackComparison_of_isOpenImmersion`).

   - Pullback along an isomorphism of schemes is an equivalence, because
     `pullbackComp`, `pullbackCongr` and `pullbackId` assemble the inverse.
   - Suppose `f ∣_ U` is an isomorphism. Then the Library local dual pullback
     `localDualPullback f M U` is a composite of equivalences, so it is bijective.
     The equivalences are `internalHomSectionsEquiv`, the full faithfulness of
     pullback along `f ∣_ U`, conjugation by the Library `restrictPullbackNatIso`,
     and composition with `pullbackUnitIso`.
   - For an open immersion `j` and an open `W` of the source, `j ∣_ (j ''ᵁ W)` is an
     isomorphism. It is an open immersion with surjective underlying map.

   It follows that the restriction along `j` of the Library map
   `dualPushforwardComparison j N` is invertible on every open. The proof then uses
   the canonical isomorphism between restriction and pullback,
   `(restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)`, and
   the counit of `restrictAdjunction j`, which is invertible for an open immersion.
   Together they show that `dualPullbackComparison j N` is invertible for every
   module `N`.

6. **The free case** (`isIso_dualPullbackComparison_restrict_of_free`). Let `e`
   identify the free module on a finite type `I` with `M.over U`. Then the
   restriction of `M` to `U` is a finite retract-sum of copies of the restricted
   structure module. The inclusions are the images of `ιFree k ≫ e.hom` under
   `internalHomSectionsEquiv`, and the projections are the images of
   `e.inv ≫ freeCoordinate U I k`. Their sum is the identity by the Library lemma
   `freeCoordinate_total`. Step 2 then applies, together with step 4 transported
   along `restrictUnitIso`.

7. **Locality on the target** (`isIso_dualPullbackComparison_of_local`). Suppose
   each point of `Y` lies in an open `U` such that the comparison for the restriction
   of `M` to `U` is invertible along every morphism into `U`. Then the comparison for
   `f` is invertible. Over `f ⁻¹ᵁ U`, the proof writes
   `(f ⁻¹ᵁ U).ι ≫ f = (f ∣_ U) ≫ U.ι` (`morphismRestrict_ι`). It expands both sides
   with the Library composition law `dualPullbackComparison_comp`. Steps 2 and 5
   provide the invertible factors, which leaves the pullback of the comparison for
   `f` to `f ⁻¹ᵁ U`. Step 1 concludes.

The main theorem combines steps 7 and 6. The cover `q.X` covers `Y` by Mathlib's
`Opens.coversTop_iff`. Over each `q.X i`, the generators `q.generators i` are finite,
and their defining map `π` is an isomorphism from a free module. This is exactly the
input to step 6.

## Dependencies

The module imports the Library modules `Langlands.AlgebraicGeometry.ModuleDualPullback`
and `Langlands.AlgebraicGeometry.ModuleDualLocalFree`. The first provides the
comparison, its naturality and composition law, and local dual pullback. The second
provides `freeCoordinate` and `freeCoordinate_total`. It also imports Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.IsIso` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`. It uses no new axioms and
has no proof holes.
