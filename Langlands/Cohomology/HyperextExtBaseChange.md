# Extension of scalars on `Ext` groups by dimension shifting

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextHomLocalization` (`homBaseChangeMap`,
`homBaseChangeMap_tmul`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(`projective_of_free_asModule`; Worker 61). Through these imports it also uses
`Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`extBaseChangeMap`, `extBaseChangeMap_tmul`, `repExtendScalars_isSemilinear`
and the instances `repExtendScalars_preservesFiniteLimits`,
`repExtendScalars_preservesFiniteColimits`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (`repExtendScalars`,
`repExtendScalars_additive`, `repExtendScalarsAdjunction`,
`repRestrictScalars`; Worker 61). From Mathlib it imports
`Mathlib.Algebra.FiveLemma`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear`,
`Mathlib.LinearAlgebra.TensorProduct.Pi` and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

The Library's `extBaseChangeMap F hF X Y n` is the `S`-linear map
`S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`, `s ⊗ e ↦ s • F(e)`, of an exact functor
`F` from an `R`-linear to an `S`-linear abelian category that is semilinear
along `algebraMap R S`. The Markdown file of `HyperextScalarExtension` notes
that it is in general not bijective. This module proves, for `S` flat over `R`,
that it is injective when `X` has a resolution `P_n → ⋯ → P_0 → X → 0` of
length `n`, and bijective when `X` has a resolution of length `n + 1`, by
objects in a class `Q` of projective objects `P` such that `F P` is projective
and `S ⊗[R] Hom(P, Y) → Hom(F P, F Y)` is bijective. The proof is by dimension
shifting. For extension of scalars of representations, the representations
that are free of finite rank over the monoid algebra `R[G]` form such a class.
The existence of the resolutions remains a hypothesis.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`.

## Conventions

`Ext^n(X, Y)` is Mathlib's `Abelian.Ext.{t} X Y n`. For
`α : Ext^a(X₁, X₂)` and `h : a + n = m`, `α^*` denotes Mathlib's
`α.precompOfLinear R Y h : Ext^n(X₂, Y) →ₗ[R] Ext^m(X₁, Y)`, `e ↦ α.comp e h`;
`Ext.mk₀ g ∈ Ext^0` is the class of a morphism `g`, `F(α)` is Mathlib's
`α.mapExactFunctor F`, and for a short exact sequence `hT : T.ShortExact`
(`0 → T.X₁ → T.X₂ → T.X₃ → 0`), `hT.extClass ∈ Ext^1(T.X₃, T.X₁)` is Mathlib's
extension class. For an `R`-linear map `f`, `S ⊗ f` is Mathlib's
`f.baseChange S`. A resolution "of length `n`" is an exact sequence
`P_n → ⋯ → P_0 → X → 0`, so it has `n + 1` terms `P_i`.

## Resolutions

Section `Resolution` takes a category `C : Type uC` with
`[Category.{vC} C] [HasZeroMorphisms C]` and `Q Q' : C → Prop` (implicit).
Section `ResolutionZero` takes `[Abelian C]` instead.

| Declaration | Statement |
| --- | --- |
| `HasResolutionBy Q n X` | A `def` (a `Prop`) by recursion on `n`. For `n = 0`: there are `P : C` and `p : P ⟶ X` with `Q P` and `Epi p`. For `n + 1`: there are `K P : C`, `i : K ⟶ P`, `p : P ⟶ X` and `w : i ≫ p = 0` such that `ShortComplex.mk i p w` is short exact, `Q P`, and `HasResolutionBy Q n K`. |
| `HasResolutionBy.of_succ` | `HasResolutionBy Q (n + 1) X → HasResolutionBy Q n X`. |
| `HasResolutionBy.of_le h hX` | For `h : m ≤ n` and `hX : HasResolutionBy Q n X`: `HasResolutionBy Q m X`. |
| `HasResolutionBy.mono h` | For `h : ∀ P, Q P → Q' P`: `HasResolutionBy Q n X → HasResolutionBy Q' n X`. |
| `HasResolutionBy.of_prop hZ hQZ n hP` | In an abelian category, for `hZ : IsZero Z`, `hQZ : Q Z` and `hP : Q P`: `HasResolutionBy Q n P`, for every `n : ℕ`. |

Unfolding the recursion, `HasResolutionBy Q n X` holds exactly when there is an
exact sequence `P_n → ⋯ → P_1 → P_0 → X → 0` with all `Q P_i`: the kernels
`K` of the successive epimorphisms are the syzygies.

Proofs.

- `of_succ`: induction on `n`. For `n = 0` the epimorphism is the second map of
  the short exact sequence (Mathlib's `ShortExact.epi_g`); for `n + 1` apply
  the induction hypothesis to the syzygy `K`.
- `of_le`: induction on `m ≤ n` with `of_succ`. `mono`: induction on `n`.
- `of_prop`: induction on `n`. For `n = 0` take `𝟙 P`. For `n + 1` take the
  sequence `0 → Z → P → P → 0` with maps `0` and `𝟙 P`: `0 : Z ⟶ P` is a
  monomorphism because `Z` is a zero object, `Z` is a kernel of the
  monomorphism `𝟙 P` (Mathlib's `KernelFork.IsLimit.ofMonoOfIsZero`), so the
  sequence is exact (`ShortComplex.exact_of_f_is_kernel`) and short exact, and
  the induction hypothesis applies to `Z` because `Q Z`.

## Long exact sequences

Section `Sequences` takes a commutative ring `R : Type uR` (explicit), an
`R`-linear abelian category `C` (`[Abelian C] [Linear R C] [HasExt.{t} C]`), a
short complex `T` (implicit) with `hT : T.ShortExact` and an object `Y : C`
(both explicit).

| Declaration | Statement |
| --- | --- |
| `exact_precompOfLinear_mk₀_g_f R hT Y n` | `Function.Exact (Ext.mk₀ T.g)^* (Ext.mk₀ T.f)^*` for the maps `Ext^n(T.X₃, Y) → Ext^n(T.X₂, Y) → Ext^n(T.X₁, Y)`. |
| `exact_precompOfLinear_mk₀_f_extClass R hT Y n` | `Function.Exact (Ext.mk₀ T.f)^* (hT.extClass)^*` for the maps `Ext^n(T.X₂, Y) → Ext^n(T.X₁, Y) → Ext^{n+1}(T.X₃, Y)` (with `h = add_comm 1 n`). |
| `precompOfLinear_extClass_surjective R hT Y n` | If `[Projective T.X₂]`: `(hT.extClass)^* : Ext^n(T.X₁, Y) → Ext^{n+1}(T.X₃, Y)` is surjective. |

Proofs. The first two are Mathlib's `Ext.contravariant_sequence_exact₂'` and
`Ext.contravariant_sequence_exact₁'`, converted from exactness of short
complexes of abelian groups to `Function.Exact`
(`ShortComplex.ab_exact_iff_function_exact`). For the third,
`Ext^{n+1}(T.X₂, Y)` is zero because `T.X₂` is projective
(`Ext.subsingleton_of_projective`), so every element of `Ext^{n+1}(T.X₃, Y)`
lies in the image of the connecting map (`Ext.contravariant_sequence_exact₃`).

## Dimension shifting

Section `Ext` takes commutative rings `R`, `S` with `[Algebra R S]` (implicit),
an `R`-linear abelian category `C` (`[Abelian C] [Linear R C]`), an `S`-linear
abelian category `D` (`[Abelian D] [Linear S D]`), a functor `F : C ⥤ D`
(explicit) with `[F.Additive] [PreservesFiniteLimits F]
[PreservesFiniteColimits F]`, `[HasExt.{t} C]`, `[HasExt.{t'} D]` and
`hF : IsSemilinear R S F` (explicit). Write `φ_X^n = extBaseChangeMap F hF X Y n`.
From `extBaseChangeMap_zero_injective_of_hasResolutionBy` on the section also
takes `Q : C → Prop` (implicit) and `Y : C` (explicit), and from
`extBaseChangeMap_surjective_of_prop` on the hypotheses

- `hproj : ∀ P, Q P → Projective P`,
- `hFproj : ∀ P, Q P → Projective (F.obj P)`,
- `hQ : ∀ P, Q P → Function.Bijective (extBaseChangeMap F hF P Y 0)`,

each passed only to the declarations whose statement names it.

| Declaration | Statement |
| --- | --- |
| `extBaseChangeMap_baseChange_precompOfLinear F hF Y α h z` | For `α : Ext^a(X₁, X₂)`, `h : a + n = m` and `z : S ⊗[R] Ext^n(X₂, Y)`: `φ_{X₁}^m ((S ⊗ α^*) z) = F(α).comp (φ_{X₂}^n z) h`. |
| `extBaseChangeMap_baseChange_precompOfLinear_mk₀ F hF Y g n z` | For `g : X₁ ⟶ X₂`: `φ_{X₁}^n ((S ⊗ (Ext.mk₀ g)^*) z) = (Ext.mk₀ (F.map g)).comp (φ_{X₂}^n z) (zero_add n)`. |
| `extBaseChangeMap_baseChange_precompOfLinear_extClass F hF hT Y n z` | For `hT : T.ShortExact` and `z : S ⊗[R] Ext^n(T.X₁, Y)`: `φ_{T.X₃}^{n+1} ((S ⊗ (hT.extClass)^*) z) = (hT.map_of_exact F).extClass.comp (φ_{T.X₁}^n z) (add_comm 1 n)`, where `hT.map_of_exact F` is the short exact image of `T` under `F`. |
| `extBaseChangeMap_zero_bijective_iff F hF X Y` | `φ_X^0` is bijective if and only if the Library's `homBaseChangeMap F hF X Y : S ⊗[R] (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is bijective. |
| `extBaseChangeMap_zero_injective_of_hasResolutionBy F hF Y hQ' hX` | For `[Module.Flat R S]`, `hQ' : ∀ P, Q P → Function.Injective (extBaseChangeMap F hF P Y 0)` and `hX : HasResolutionBy Q 0 X`: `φ_X^0` is injective. |
| `extBaseChangeMap_surjective_of_prop F hF Y hFproj hQ hP n` | For `hP : Q P`: `φ_P^n` is surjective, for every `n : ℕ`. |
| `extBaseChangeMap_injective_of_hasResolutionBy F hF Y hproj hFproj hQ n hX` | For `[Module.Flat R S]` and `hX : HasResolutionBy Q n X`: `φ_X^n` is injective. |
| `extBaseChangeMap_bijective_of_hasResolutionBy F hF Y hproj hFproj hQ n hX` | For `[Module.Flat R S]` and `hX : HasResolutionBy Q (n + 1) X`: `φ_X^n` is bijective. |
| `extBaseChangeEquivOfHasResolutionBy F hF Y hproj hFproj hQ n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n(X, Y) ≃ₗ[S] Ext^n(F X, F Y)` with underlying map `φ_X^n`. A `def`. |
| `extBaseChangeEquivOfHasResolutionBy_apply F hF Y hproj hFproj hQ n hX z` | Its value at `z` is `φ_X^n z` (a `simp` lemma, by definition). |

Proofs.

- `extBaseChangeMap_baseChange_precompOfLinear`: induction on `z`
  (`TensorProduct.inductionOn`). On `s ⊗ e` the left side is
  `s • F(α.comp e h)` and the right side `F(α).comp (s • F(e)) h`; they agree
  by Mathlib's `Ext.mapExactFunctor_comp` and `Ext.comp_smul`. Both sides are
  additive in `z`. The two special cases follow with
  `Ext.mapExactFunctor_mk₀` and `Ext.mapExactFunctor_extClass`.
- `extBaseChangeMap_zero_bijective_iff`: Mathlib's `Ext.linearEquiv₀`
  identifies `Ext^0` with `Hom`. On `s ⊗ f`, `φ_X^0 (s ⊗ Ext.mk₀ f) =
  s • Ext.mk₀ (F.map f) = Ext.mk₀ (s • F.map f)` (`Ext.mapExactFunctor_mk₀`,
  `Ext.mk₀_smul`), so `φ_X^0` composed with the base change of
  `Ext.linearEquiv₀.symm` equals `Ext.linearEquiv₀.symm` composed with
  `homBaseChangeMap F hF X Y`. Composition with bijections does not change
  bijectivity (`EquivLike.bijective_comp`, `EquivLike.comp_bijective`).
- `extBaseChangeMap_zero_injective_of_hasResolutionBy`: let `p : P ⟶ X` be
  the epimorphism with `Q P`. Precomposition `(Ext.mk₀ p)^*` on `Ext^0` is
  injective (`Ext.precomp_mk₀_injective_of_epi`), and stays injective after
  `S ⊗ −` because `S` is flat (`Module.Flat.lTensor_preserves_injective_linearMap`).
  By naturality (`_mk₀`), `φ_P^0 ∘ (S ⊗ (Ext.mk₀ p)^*)` is
  `φ_X^0` followed by precomposition with `Ext.mk₀ (F.map p)`; it is injective,
  hence so is `φ_X^0`.
- `extBaseChangeMap_surjective_of_prop`: in degree `0` this is `hQ`; in degree
  `n + 1` the target `Ext^{n+1}(F P, F Y)` is zero because `F P` is projective.
- `extBaseChangeMap_injective_of_hasResolutionBy`: induction on `n`. For
  `n = 0` this is the previous injectivity theorem. For `n + 1`, let
  `0 → K → P → X → 0` be the short exact sequence of the resolution, with
  `Q P` and `HasResolutionBy Q n K`. Its long exact sequences give the
  commutative diagram (naturality lemmas `_mk₀` and `_extClass`)

  ```
  S ⊗ Ext^n(P, Y)   → S ⊗ Ext^n(K, Y)   → S ⊗ Ext^{n+1}(X, Y) → 0
        ↓ φ_P^n            ↓ φ_K^n              ↓ φ_X^{n+1}
  Ext^n(F P, F Y)   → Ext^n(F K, F Y)   → Ext^{n+1}(F X, F Y)
  ```

  The upper row is exact: it is `S ⊗ −` of the exact sequence of
  `exact_precompOfLinear_mk₀_f_extClass`, whose last map is surjective by
  `precompOfLinear_extClass_surjective` (`P` is projective), and `S ⊗ −` is
  right exact (`lTensor_exact`, `LinearMap.lTensor_surjective`). The lower row
  is exact because `F` sends `T` to a short exact sequence
  (`ShortExact.map_of_exact`). `φ_P^n` is surjective
  (`extBaseChangeMap_surjective_of_prop`) and `φ_K^n` injective (induction),
  so `φ_X^{n+1}` is injective by Mathlib's four lemma
  `LinearMap.injective_of_surjective_of_injective_of_right_exact`.
- `extBaseChangeMap_bijective_of_hasResolutionBy`: induction on `n`. For
  `n = 0`, with `0 → K → P → X → 0` as above and `HasResolutionBy Q 0 K`, the
  rows
  `0 → S ⊗ Ext^0(X, Y) → S ⊗ Ext^0(P, Y) → S ⊗ Ext^0(K, Y)` and
  `0 → Ext^0(F X, F Y) → Ext^0(F P, F Y) → Ext^0(F K, F Y)` are exact
  (`exact_precompOfLinear_mk₀_g_f`, `Ext.precomp_mk₀_injective_of_epi` and
  flatness of `S`: `Module.Flat.lTensor_exact`,
  `Module.Flat.lTensor_preserves_injective_linearMap`); `φ_P^0` is bijective
  (`hQ`) and `φ_K^0` injective (the degree-`0` injectivity theorem), so
  `φ_X^0` is bijective (`LinearMap.bijective_of_bijective_of_injective_of_left_exact`).
  For `n + 1`, the diagram of the injectivity proof applies with
  `HasResolutionBy Q (n + 1) K`: `φ_P^n` is surjective, `φ_K^n` bijective
  (induction), and the last maps of both rows are surjective because `P` and
  `F P` are projective, so `φ_X^{n+1}` is bijective
  (`LinearMap.bijective_of_surjective_of_bijective_of_right_exact`).
- `extBaseChangeEquivOfHasResolutionBy`: Mathlib's `LinearEquiv.ofBijective`.

## Representations

Section `Rep` takes a commutative ring `R : Type uR` and a monoid
`G : Type uG` (both implicit unless stated). For `P : Rep.{w} R G`,
`P.ρ.asModule` is Mathlib's `MonoidAlgebra R G`-module of `P`, and
`P.ρ.asModuleEquiv : P.ρ.asModule ≃ₗ[R] P` Mathlib's identification of
underlying `R`-modules (by definition the identity). From `repRestrictScalars_preservesEpimorphisms` on the section
also takes a commutative ring `S : Type uS` with `[Algebra R S]`. Below
`E = repExtendScalars.{max uS w} R S G` is the Library's extension of scalars
`Rep.{max uS w} R G ⥤ Rep.{max uS w} S G`, `X ↦ S ⊗[R] X`, and
`hE = repExtendScalars_isSemilinear.{max uS w} R S G`. The universe
`max uS w` is that of the Library's adjunction
`repExtendScalarsAdjunction.{w} R S G : E ⊣ repRestrictScalars R S G`.

| Declaration | Statement |
| --- | --- |
| `HasFiniteBasis P` | For `P : Rep.{w} R G`: there are `n : ℕ` and a basis `Module.Basis (Fin n) (MonoidAlgebra R G) P.ρ.asModule`. A `def` (a `Prop`). |
| `HasFiniteBasis.projective hP` | For `hP : HasFiniteBasis P`: `Projective P` in `Rep.{w} R G`. |
| `hasFiniteBasis_of_isZero hZ` | For `hZ : IsZero Z`: `HasFiniteBasis Z`. |
| `HasFiniteBasis.hasResolutionBy hP n` | For `hP : HasFiniteBasis P`: `HasResolutionBy HasFiniteBasis n P`, for every `n : ℕ`. |
| `repHom_eval_basis_bijective b Y` | For a basis `b : Module.Basis ι (MonoidAlgebra R G) P.ρ.asModule` (any index type `ι`) and `Y : Rep.{w} R G`: the map `(P ⟶ Y) → (ι → Y)`, `f ↦ (i ↦ f.hom (P.ρ.asModuleEquiv (b i)))`, is bijective. |
| `repRestrictScalars_preservesEpimorphisms R S G` | Instance: the Library's restriction of scalars `repRestrictScalars.{w} R S G : Rep.{w} S G ⥤ Rep.{w} R G` preserves epimorphisms. |
| `HasFiniteBasis.projective_repExtendScalars S hP` | For `P : Rep.{max uS w} R G` and `hP : HasFiniteBasis P`: `Projective (E.obj P)`. |
| `repHomBaseChangeMap_bijective_of_hasFiniteBasis S hP Y` | For `P Y : Rep.{max uS w} R G` and `hP : HasFiniteBasis P`: the Library's `homBaseChangeMap E hE P Y : S ⊗[R] (P ⟶ Y) → (E.obj P ⟶ E.obj Y)` is bijective. No flatness is assumed. |

Its section `Ext` takes `[Module.Flat R S]`,
`[HasExt.{t} (Rep.{max uS w} R G)]`, `[HasExt.{t'} (Rep.{max uS w} S G)]` and
`Y : Rep.{max uS w} R G` (explicit); `X : Rep.{max uS w} R G` is implicit.

| Declaration | Statement |
| --- | --- |
| `repExtBaseChangeMap_injective_of_hasResolutionBy S Y n hX` | For `hX : HasResolutionBy HasFiniteBasis n X`: `extBaseChangeMap E hE X Y n : S ⊗[R] Ext^n(X, Y) → Ext^n(E.obj X, E.obj Y)` is injective. |
| `repExtBaseChangeMap_bijective_of_hasResolutionBy S Y n hX` | For `hX : HasResolutionBy HasFiniteBasis (n + 1) X`: `extBaseChangeMap E hE X Y n` is bijective. |
| `repExtBaseChangeEquivOfHasResolutionBy S Y n hX` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] Ext^n(X, Y) ≃ₗ[S] Ext^n(E.obj X, E.obj Y)` with underlying map `extBaseChangeMap E hE X Y n`. A `def`. |
| `repExtBaseChangeEquivOfHasResolutionBy_apply S Y n hX z` | Its value at `z` is `extBaseChangeMap E hE X Y n z` (a `simp` lemma, by definition). |

Proofs.

- `HasFiniteBasis.projective`: a basis makes `P.ρ.asModule` free
  (`Module.Free.of_basis`), and the Library's `projective_of_free_asModule`
  applies.
- `hasFiniteBasis_of_isZero`: the underlying module of `Z`, and hence
  `Z.ρ.asModule`, is a subsingleton (Mathlib's `Rep.isZero_iff`), so the empty
  family is a basis (`Module.Basis.empty`), with `n = 0`.
- `HasFiniteBasis.hasResolutionBy`: `HasResolutionBy.of_prop` with the zero
  object of `Rep.{w} R G`, which satisfies `HasFiniteBasis` by the previous
  lemma.
- `repHom_eval_basis_bijective`: Mathlib's
  `Representation.IntertwiningMap.equivLinearMapAsModule` identifies morphisms
  `P ⟶ Y` (`Rep.hom_ext`) with `MonoidAlgebra R G`-linear maps
  `P.ρ.asModule → Y.ρ.asModule`. Such a map is determined by its values on the
  basis (`Module.Basis.ext`), and for any family of values there is one taking
  them (`Module.Basis.constr`, `Module.Basis.constr_basis`).
- `repRestrictScalars_preservesEpimorphisms`: epimorphisms of representations
  are the morphisms with surjective underlying map (`Rep.epi_iff_surjective`),
  and restriction of scalars does not change the underlying map
  (`RestrictScalars.addEquiv`).
- `HasFiniteBasis.projective_repExtendScalars`: a left adjoint whose right
  adjoint preserves epimorphisms preserves projective objects (Mathlib's
  `Adjunction.map_projective`), applied to `repExtendScalarsAdjunction` and
  `HasFiniteBasis.projective`.
- `repHomBaseChangeMap_bijective_of_hasFiniteBasis`: let `b` be a basis indexed
  by `Fin n` and `x_i = P.ρ.asModuleEquiv (b i)`. By `repHom_eval_basis_bijective`,
  `f ↦ (f.hom x_i)_i` is an `R`-linear equivalence
  `(P ⟶ Y) ≃ (Fin n → Y)`; let `ψ` be its base change followed by Mathlib's
  `TensorProduct.piRight : S ⊗[R] (Fin n → Y) ≃ (Fin n → S ⊗[R] Y)`. The map
  `ev : (E.obj P ⟶ E.obj Y) → (Fin n → S ⊗[R] Y)`, `g ↦ (g.hom (1 ⊗ x_i))_i`, is
  injective: under `repExtendScalarsAdjunction`, `g` corresponds to a morphism
  `P ⟶ repRestrictScalars (E.obj Y)` whose value at `x_i` is `g.hom (1 ⊗ x_i)`,
  and that morphism is determined by these values (`repHom_eval_basis_bijective`
  again). On `s ⊗ f`, `ev (s • E.map f) = (s • (1 ⊗ f.hom x_i))_i =
  (s ⊗ f.hom x_i)_i = ψ (s ⊗ f)`; both sides are additive, so
  `ev ∘ homBaseChangeMap E hE P Y = ψ`. Hence `homBaseChangeMap E hE P Y` is
  injective, and for `g` with `ev g = ψ t`, injectivity of `ev` gives
  `homBaseChangeMap E hE P Y t = g`.
- `repExtBaseChangeMap_injective_of_hasResolutionBy`,
  `repExtBaseChangeMap_bijective_of_hasResolutionBy`,
  `repExtBaseChangeEquivOfHasResolutionBy`: the general
  `extBaseChangeMap_injective_of_hasResolutionBy`,
  `extBaseChangeMap_bijective_of_hasResolutionBy` and
  `extBaseChangeEquivOfHasResolutionBy` for `F = E` and `Q = HasFiniteBasis`,
  with `HasFiniteBasis.projective`, `HasFiniteBasis.projective_repExtendScalars`,
  and `extBaseChangeMap_zero_bijective_iff` combined with
  `repHomBaseChangeMap_bijective_of_hasFiniteBasis`. The exactness instances of
  `E` are the Library's `repExtendScalars_preservesFiniteLimits` and
  `repExtendScalars_preservesFiniteColimits`, which need `[Module.Flat R S]`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. That `S ⊗_R Ext^n_A(X, Y) → Ext^n_{S ⊗ A}(S ⊗ X, S ⊗ Y)` is an
isomorphism for a flat `R`-algebra `S` when `X` has a resolution by finitely
generated free modules is standard homological algebra; here it is proved by
dimension shifting along the resolution, so that only `Ext^0` and the vanishing
of `Ext` out of projective objects are needed.

The passage of Harris 1999 behind this module is quoted, from the rendered
scans, in the Markdown file of `Langlands.Cohomology.HyperextScalarExtension`:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in `W(L)`."
- §4, printed p.311 (one-based PDF page 13), Proposition 4.10: "There is a
  spectral sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, L_ℓ(n - 1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W̃)`.
  Here `Ext^i` denotes the i-th derived functor of `Hom` in the category of
  smooth `L_ℓ[GJ]`-modules."
- §4, printed p.312 (one-based PDF page 14), end of the proof of
  Proposition 4.10: "In fact, we have proved the stronger (integral)
  statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒ H^{i+j}(S̄_{K(N)}, 𝓛̃)`."

Interpretation (explanation only). The `E_2` terms of (4.10.4) are `Ext`
groups with `𝒪`-coefficients and those of (4.10.1) are `Ext` groups with
`L_ℓ`-coefficients. Passing from the first to the second is extension of
scalars along `𝒪 → L_ℓ`, which is flat (as explained in the Markdown file of
`HyperextScalarExtension`; the formalization does not prove it), and the
comparison map on `E_2` terms is `extBaseChangeMap`. This module shows that the
comparison map is an isomorphism in degree `i` when the first argument has a
resolution of length `i + 1` by finite free modules over the group algebra.
For example (explanation only, not formalized), if `R[G]` is noetherian, as for
a finite group `G` and a noetherian ring `R`, every finitely generated
`R[G]`-module has resolutions of every length by finite free modules. The
module treats representations of an abstract monoid `G`, not Harris's smooth
`GJ`-modules, and does not identify `G`, the first argument or the coefficient
module with Harris's objects.

## Scope

- Smooth representations are not treated: a free `R[G]`-module of finite rank
  is not a smooth representation of a non-discrete group, and this module
  provides no class of projective smooth representations with `𝒪`-coefficients
  to which the general theorems apply. The general theorems apply to any class
  `Q` satisfying their hypotheses, but no such class of smooth representations
  is constructed.
- The existence of resolutions by finite free representations is a hypothesis;
  it is not verified for any representation, and whether Harris's cohomology
  groups have such resolutions is not addressed.
- Without finiteness the conclusion fails already in degree `0` for the trivial
  group, by the example `ℚ ⊗_ℤ ℤ^ℕ → ℚ^ℕ` of the Markdown file of
  `HyperextScalarExtension` (explanation only, not formalized).
- Only `Ext` groups between objects are treated. The maps on hyperext groups
  `Hom(K, W₀⟦n⟧)` for complexes `K`, on invariants and on isotypic parts are not
  proved bijective here, and the compatibility of the comparison maps with the
  differentials of Harris's spectral sequences is not treated.
- `HasExt` is a hypothesis; the results hold for each such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307, 311 and 312 (rendered scans) as quoted in
`Langlands.Cohomology.HyperextScalarExtension`.

Dependencies: `Langlands.Cohomology.HyperextHomLocalization`,
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`,
`Mathlib.Algebra.FiveLemma`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`,
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear`,
`Mathlib.LinearAlgebra.TensorProduct.Pi` and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
