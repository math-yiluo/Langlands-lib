# Open-immersion locality of relative differentials: proof

This module proves the published proposition
`Langlands.Scheme.RelativeDifferentialsOpenImmersionIsIsoStatement.{u}` from
`Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionStatement`. The
theorem `Langlands.Scheme.relativeDifferentialsOpenImmersionIsIso` has exactly
that closed statement as its type. It is universe-polymorphic in `u`. For
arbitrary schemes `X'`, `X`, `S'` and `S`, open immersions `g : X' ⟶ X` and
`b : S' ⟶ S`, morphisms `f : X ⟶ S` and `f' : X' ⟶ S'`, and any proof
`w : g ≫ f = f' ≫ b`, it concludes
`IsIso (relativeDifferentialsSquareMap g b w)`. That map is the existing
canonical one. The statement, the relative differential sheaf, its universal
derivation and the square map are imported unchanged. The square need not be
Cartesian, and no affineness, smoothness, finiteness or nonemptiness is
assumed.

## Proof outline

The proof uses the Yoneda criterion `isIso_of_coyoneda_map_bijective`. For
every sheaf of modules `M` on `X'`, it shows that precomposition with the
square map,
`(relativeDifferentials f' ⟶ M) → ((pullback g).obj (relativeDifferentials f) ⟶ M)`,
is bijective. Three bijections rewrite this function:

1. `relativeDifferentialsHomEquiv f' M` identifies maps out of
   `relativeDifferentials f'` with relative derivations `RelativeDerivation f' M`.
2. The module adjunction `pullbackPushforwardAdjunction g`, followed by
   `relativeDifferentialsHomEquiv f ((pushforward g).obj M)`, identifies maps
   out of the pullback with relative derivations
   `RelativeDerivation f ((pushforward g).obj M)`.
3. Under these identifications, precomposition with the square map becomes
   `d ↦ precompOver g w (forgetBase b d)`. The step `hcomm` checks this using
   the published `relativeDifferentialsSquareMap_adjoint` and
   `relativeDifferentialsSquarePushforwardMap_fac`, together with naturality of
   the adjunction and compatibility of `postcomp` with `forgetBase` and
   `precompOver`.

The whole proof therefore reduces to the lemma
`RelativeDerivation.bijective_precompOver_forgetBase`. It says that for an open
immersion `g`, sending a derivation on `X'` over `S'` to its precomposite
derivation on `X` over `S`, with values in `(pushforward g).obj M`, is
bijective.

## Inverse construction

Section `OpenImmersion` builds the inverse explicitly. Take a derivation
`D : RelativeDerivation f ((pushforward g).obj M)` and an open `V` of `X'`.
Then `openImmersionLiftApp g D V` is the additive map
`Γ(X', V) → Γ(M, V)` defined as follows. It first transports a section to
`Γ(X, g ''ᵁ V)` by the inverse of Mathlib's `Scheme.Hom.appIso`. It then
applies `D` on `g ''ᵁ V`, landing in `Γ(M, g ⁻¹ᵁ (g ''ᵁ V))`. Finally it
restricts along `V ≤ g ⁻¹ᵁ (g ''ᵁ V)`. Its properties:

- `openImmersionLiftApp_app`: on a section `g.app U a` pulled back from `X`, it
  returns `D.app U a`. The proof uses `Scheme.Hom.app_appIso_inv`, the
  restriction compatibility of `D`, and the helper `map_map_eq` (two successive
  restrictions in a module sheaf equal one direct restriction).
- `openImmersionLiftApp_restrict`: it commutes with restriction, by
  `Scheme.Hom.appIso_inv_naturality`.
- `openImmersionLiftApp_mul`: the Leibniz rule. The proof uses
  `Scheme.Modules.map_smul` and `map_app_appIso_inv`, which says that
  restricting `g.app (g ''ᵁ V) ((g.appIso V).inv a)` back to `V` gives `a`.
- `openImmersionLiftApp_base`: it kills sections `f'.app W c` pulled back from
  `S'`. Write `c` as the image of `(b.appIso W).inv c` under `b.appLE`. Then,
  using `w`, `f'.app W c` is the restriction of the pullback along `g` of the
  section `f.app (b ''ᵁ W) ((b.appIso W).inv c)` of `X`. The two previous
  properties and the vanishing of `D` on sections from `S` give zero.

These four facts assemble into `openImmersionLift g b w D`, a derivation in
`RelativeDerivation f' M`. The lemmas
`precompOver_forgetBase_openImmersionLift` and
`openImmersionLift_precompOver_forgetBase` show that it is a two-sided
inverse. The first uses `openImmersionLiftApp_app`. The second uses the
restriction compatibility of the original derivation and `map_app_appIso_inv`.

## Source

The mathematical content is the Stacks Project, Morphisms §29.33,
[Lemma 29.33.3 (tag 01US)](https://stacks.math.columbia.edu/tag/01US), in
`01UM.html` of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, folder content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`. For open
subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, that lemma gives a unique
isomorphism `Ω_{X/S}|_U ≅ Ω_{U/V}` compatible with the universal derivations.
The Lean statement is the case `U = X'`, `V = S'`, transported along the open
immersions `g` and `b`. The canonical square
map is the one of Lemma 29.33.8 (tag 01UV) in the same file. The Stacks proof
cites the corresponding statement for modules, Modules §17.28, Lemma 17.28.5
(tag 08RQ) in `08RL.html`. The Lean proof does not transport along
`Scheme.Modules.restrictFunctorIsoPullback`. Instead it checks the universal
property directly: derivations on an open subscheme over an open of the base
correspond to derivations on the ambient scheme, with values in the
pushforward.
