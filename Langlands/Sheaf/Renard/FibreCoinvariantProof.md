# Proof: Renard III.3.1, the stalk of the coinvariant sheaf is the fibre coinvariants

Worker 136 implemented this proof for Task 5593. The entry theorem is

```
Langlands.Sheaf.Renard.CoinvariantStatements.fibreCoinvariantStatement :
  FibreCoinvariantStatement
```

It proves the published statement
`Langlands.Sheaf.Renard.CoinvariantStatements.FibreCoinvariantStatement` from
`Langlands/Sheaf/Renard/CoinvariantStatements.lean`, unchanged. The statement
fixes a locally profinite group `G`, locally profinite `X` and `Y` with a jointly
continuous action of `G` on `X`, an invariant continuous map `q : C(X, Y)` and a
point `y : Y`. It asks for a natural isomorphism between two functors
`ActionSheaf G X ⥤ ModuleCat ℂ`:

- `CoinvariantSheaf.functor hX q hq hY`, then the sheaf forgetful functor, then
  Mathlib's `stalkFunctor` at `y`. It sends `F` to the stalk `F′_y`.
- `InvariantFibres.coinvariants q hq y`. It sends `F` to the coinvariants of the
  compact-section representation of the restriction of `F` to the fibre
  `Z = {x // q x = y}`.

The proof adds no hypothesis. It does not use the unproved II.2.5 module
comparison (`ModuleComparisonIsIso`) or the companion statement
`CompactComparisonStatement`.

The proof uses two helper modules, documented in their own Markdown:
`FibreCoinvariantStalk` (the stalk map of Renard's vector sheaf of a
nondegenerate test module, its surjectivity and its kernel) and
`FibreCoinvariantRestriction` (restriction of compact sections along an
equivariant closed embedding, its equivariance, naturality and surjectivity).

## Idea

Write `A = F_c(X)` for the compactly supported global sections of `F`, with
their natural complex structure (`Sections F`). The proof builds two surjective
linear maps out of `A`:

- `α : A → F′_y`, the germ at `y` of the coinvariant class of `a`;
- `β : A → F_c(Z)_G`, the coinvariant class of the restriction of `a` to the
  fibre.

It shows that they have the same kernel. Hence there is a unique linear
isomorphism `F′_y ≃ F_c(Z)_G` sending `α a` to `β a`. Naturality in `F` only
needs to be checked on elements `α a`, because `α` is surjective.

## Declarations in `FibreCoinvariantProof.lean`

Prefix `Langlands.Sheaf.Renard.FibreCoinvariantProof`, except for the final
theorem.

### Identifications of complex structures

- `smul_of_module_eq`: equal `Module ℂ` structures give equal scalar
  multiplication.
- `Sections F`, `testAction hX F` (the published
  `CompactSectionActions.compatibleObject hX F`) and `sectionsEquiv`. The
  identity is a linear equivalence from `Sections F` to the module of the test
  action, by the published `CompactSectionActions.canonicalScalar_eq`.
- `coinvariantModule` abbreviates `(CoinvariantSheaf.modules hX q hq hY).obj F`.
  `coinvariantEquiv` is the identity of the Mathlib coinvariants
  `Representation.Coinvariants (testAction hX F).action`, viewed as a linear
  equivalence onto that module with Renard's recovered complex structure
  `ProjectorVectorSheaf.originalModule`. It uses the published
  `CoinvariantTestModule.canonicalComplex_eq`.
- `stalkY F` is the ordinary stalk at `y` of
  `ProjectorVectorSheaf.presheaf hY (coinvariantModule F).property`. This is the
  object of the left functor at `F`.

### The stalk side `α`

- `alpha F` is `FibreCoinvariantStalk.stalkGerm` composed with
  `coinvariantEquiv`, `Coinvariants.mk` and `sectionsEquiv`. `alpha_apply`
  records this by `rfl`.
- `germ_multiplier`: the germ at `x` of the target-test multiple
  `CoinvariantTestModule.multiplier q (testAction hX F) f a` is `f (q x)` times
  the germ of `a`. Proof: the published `PointwiseTestModule.smul_eq` writes the
  multiple via a characteristic function `χ_U` fixing `a`. The published
  `CompactSectionTestModule.Γgerm_testSmul` computes germs of test multiples.
  The two cases are `x ∈ U` and `x ∉ U`; in the second, the germ of `a` at `x`
  is zero.
- `alpha_eq_zero_iff`: `α a = 0` if and only if some compact open `K ∋ y` has
  `χ_K · a` in the coinvariant kernel `Coinvariants.ker`. This combines
  `FibreCoinvariantStalk.stalkGerm_eq_zero_iff` with Mathlib's
  `Coinvariants.mk_eq_zero`.
- `exists_multiplier_eq_zero`: if `a` has zero germ at every point of the fibre,
  there is a compact open `K ∋ y` with `χ_K · a = 0`. The image `q(Supp a)` is
  compact, hence closed in the Hausdorff space `Y`, and it does not contain `y`.
  Take a compact open `K ∋ y` in its complement (`exists_compactOpen_le`). By
  `germ_multiplier`, every germ of `χ_K · a` is `χ_K(q x)` times the germ of `a`
  at `x`. This vanishes both on and off the support. This is the step of
  Renard's proof that covers `q(Supp φ)` by a compact open avoiding `y`.

### The fibre side `β`

- `inclusion_isClosedEmbedding`: the fibre inclusion is a closed embedding, since
  the fibre is closed (`InvariantFibres.fibre_closed`, `Y` Hausdorff).
- `fibreRep F` is the compact-section representation of the fibre restriction
  `(InvariantFibres.restriction q hq y).obj F`, with the published fibre action
  instances `InvariantFibres.fibreAction` and `fibreContinuousSMul`. Its
  coinvariants are `(InvariantFibres.coinvariants q hq y).obj F`.
- `rFib F` is `FibreCoinvariantRestriction.compactRestrict` for the fibre
  inclusion. Since `InvariantFibres.restriction` is defined as the equivariant
  inverse image along this inclusion, the target type matches.
- `beta F` is `Coinvariants.mk (fibreRep F) ∘ rFib F`. `beta_apply` records this
  by `rfl`.
- `rFib_action` (equivariance, from `compactRestrict_action`) and `rFib_mem_ker`:
  `rFib` maps the coinvariant kernel of the test action into the coinvariant
  kernel of `fibreRep`. Induction on the span: generators `g · m - m` go to
  generators.
- `exists_ker_preimage`: every element of the fibre coinvariant kernel is
  `rFib k` for some `k` in the coinvariant kernel on `X`. Again induction on the
  span. A generator `g · b' - b'` lifts by surjectivity of `rFib`
  (`compactRestrict_surjective`) to the generator `g · m - m`.
- `rFib_multiplier`: if `y ∈ K`, then `rFib (χ_K · a) = rFib a`. Over the fibre,
  `χ_K (q x) = 1`. Compare germs with `germ_globalRestrict` and
  `germ_multiplier`.

### Equal kernels, the isomorphism, naturality

- `ker_alpha_eq_ker_beta`.
  - If `α a = 0`, choose `K ∋ y` with `χ_K · a` in the coinvariant kernel. Then
    `β a = [rFib a] = [rFib (χ_K · a)]` (`rFib_multiplier`), which is zero by
    `rFib_mem_ker`.
  - If `β a = 0`, then `rFib a` lies in the fibre coinvariant kernel. By
    `exists_ker_preimage`, `rFib a = rFib k` for some `k` in the kernel on `X`.
    So `rFib (a - k) = 0`, and through `stalkIso`, `a - k` has zero germ at every
    point of the fibre. By `exists_multiplier_eq_zero`, some `K ∋ y` has
    `χ_K · a = χ_K · k`. That element is in the coinvariant kernel by the
    published `CoinvariantTestModule.multiplier_preserves_ker`. So `α a = 0` by
    `alpha_eq_zero_iff`.
- `alpha_surjective` (from `stalkGerm_surjective` and `Coinvariants.mk_surjective`)
  and `beta_surjective` (from `compactRestrict_surjective` and
  `Coinvariants.mk_surjective`).
- `component F`: the linear equivalence
  `(quotKerEquivOfSurjective α)⁻¹ ≫ quotEquivOfEq ≫ quotKerEquivOfSurjective β`
  from `stalkY F` to the fibre coinvariants. `component_alpha` states that it
  sends `α a` to `β a`.
- `beta_map`: the fibre-side functor sends `β a` to `β (φ a)`, by
  `compactRestrict_naturality`. `alpha_map`: the stalk-side functor sends `α a`
  to `α (φ a)`. This uses Mathlib's `stalkFunctor_map_germ_apply` and the
  published `ProjectorVectorSheaf.sheafMap_originalSection`.
- `natIso`: `NatIso.ofComponents` of the `component F`, each as an isomorphism
  in `ModuleCat ℂ`. For naturality, write an element of `F′_y` as `α a`. Both
  composites send it to `β (φ a)`, by `alpha_map`, `component_alpha` and
  `beta_map`.

### Final theorem

`Langlands.Sheaf.Renard.CoinvariantStatements.fibreCoinvariantStatement`
introduces the data of the statement and returns `⟨natIso hX q hq hY y⟩`. The
hypotheses `IsTopologicalGroup G` and `IsLocallyProfinite G` are not used by the
proof. The topology on `G` is needed only through the published `ActionSheaf`
interfaces.

## Comparison with the source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, III.3.1, Proposition and its proof, printed pp.83–84 /
PDF pp.89–90. Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard proves the Proposition as follows. Restriction `p_Z : F_c(X) → F_c(Z)` is
surjective with kernel `L`, spanned by the `f · φ` with `f(y) = 0`. Hence
`F_c(Z)_G = F_c(X)/(F_c(X)(G) + L)`. He then identifies this with
`F′_c(Y)/L″ = F′_y`, using `F′_c(Y) = F_c(X)_G` and the Remark of II.2.5.

The Lean proof uses the same ingredients. These are: surjectivity of
restriction; compact support covered by a compact open avoiding `y`; and stalks
as quotients by neighbourhood tests. But it compares the two quotients of `A` by
their kernels directly. It does not pass through `F′_c(Y) ≅ F_c(X)_G`, which in
this Library is the unproved `CompactComparisonStatement`. The kernel of `α` is
described with tests `χ_K`, `y ∈ K`, rather than with functions vanishing at
`y`. The two descriptions are equivalent and the Lean proof does not need the
other one.
