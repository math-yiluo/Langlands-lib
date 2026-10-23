# Proof of the scheme-fibre to stalk-base-change flatness bridge

The theorem `Langlands.AlgebraicGeometry.fiberStalkFlatness` in module
`Langlands.AlgebraicGeometry.FiberStalkFlatness` has type exactly
`Langlands.AlgebraicGeometry.FiberStalkFlatnessStatement.{u}`, for an
arbitrary universe `u`. That published statement (module
`Langlands.AlgebraicGeometry.FiberStalkFlatnessStatement`) is imported by name
and left unchanged. It says: for `S : Scheme.{u}`, `X Y : Over S`,
`f : X ⟶ Y` and `x : X.left`, put `y = f.left x`, `s = Y.hom y`,
`R = 𝒪_{S,s}`, `A = 𝒪_{Y,y}`, `B = 𝒪_{X,x}` (with the algebra structures
given by the stalk maps), `k = κ(s)` the residue field of `R` and
`F = A ⊗[R] k`. If `((Over.pullback (S.fromSpecResidueField s)).map f).left`
is `Flat`, then `Module.Flat F (F ⊗[A] B)`.

The proof uses no further hypotheses. It needs only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. Composition is in categorical
order. `f.appLE U V e : Γ(Y, U) ⟶ Γ(X, V)` is Mathlib's section map of
`f : X ⟶ Y` for `V ≤ f ⁻¹ᵁ U`, and `Γ(T, ⊤)` is the ring of global sections.

## Route

The proof does not construct the point of the fibre over `x`, and it does not
compute the stalks of the fibres. It works with section rings over affine
opens instead. Over suitable affine opens, Mathlib describes the sections of
each fibre as a ring pushout. The flatness hypothesis gives flatness of the
section map between the two fibres. The rings `F` and `F ⊗[A] B` turn out to
be localizations of these fibre section rings, and flatness passes to
localizations. This is a different route from the one suggested in the task:
there is no stalk comparison and no transport of a stalk map.

All auxiliary lemmas are in the namespace
`Langlands.AlgebraicGeometry.FiberStalkFlatness`. All rings below are objects
of `CommRingCat`.

## Algebraic lemmas

**`isLocalization_of_isPushout` (Lemma A).** Let `a : A₀ ⟶ A`, `b : A₀ ⟶ C`,
`c : A ⟶ F`, `d : C ⟶ F` form a pushout square in `CommRingCat`. If `A` is
the localization of `A₀` at a submonoid `M` (via `a`), then `F` is the
localization of `C` at `M.map b` (via `d`). Proof: `CommRingCat.isPushout_iff_isPushout`
turns the flipped categorical pushout into `Algebra.IsPushout A₀ C A F`, and
Mathlib's `Algebra.isLocalization_iff_isPushout` says that a base change of a
localization is a localization. `A₀` acts on `F` through `a ≫ c`; the scalar
tower through `C` comes from the commutativity `h.w` of the square.

**`flat_of_isLocalization_square` (Lemma B).** Let
`φ : C ⟶ D`, `l : C ⟶ F`, `m : D ⟶ G`, `ψ : F ⟶ G` satisfy `φ ≫ m = l ≫ ψ`.
Suppose that `φ` is flat, `l` is a localization at `M ⊆ C` and `m` is a
localization at `N ⊆ D`. Then `ψ` is flat. Proof: `G` is flat over `D`
(`IsLocalization.flat`), so `G` is flat over `C` by transitivity
(`Module.Flat.trans`, with `C` acting on `G` through `l ≫ ψ = φ ≫ m`). Since
`F` is a localization of `C`, `Module.flat_iff_of_isLocalization` shows that an
`F`-module that is flat over `C` is flat over `F`.

**`flat_of_sections` (the algebraic core).** The data are:

- two pushout squares
  `PY : IsPushout tY gK iY jY` (with `tY : a₀ ⟶ aY`, `gK : a₀ ⟶ K`,
  `iY : aY ⟶ ΓY`, `jY : K ⟶ ΓY`) and
  `PX : IsPushout tX gK iX jX` (with `tX : a₀ ⟶ aX`, `iX : aX ⟶ ΓX`,
  `jX : K ⟶ ΓX`), over the same map `gK`;
- `u : aY ⟶ aX` with `tY ≫ u = tX`;
- a flat map `φ : ΓY ⟶ ΓX` with `iY ≫ φ = u ≫ iX` and `jY ≫ φ = jX`;
- a pushout square `Q1 : IsPushout r gK (algebraMap R k) e` with
  `r : a₀ ⟶ R` and `e : K ⟶ k`;
- maps `α : R ⟶ A`, `β : A ⟶ B` and localizations `γY : aY ⟶ A` (at
  `MY`) and `γX : aX ⟶ B` (at `MX`), with `r ≫ α = tY ≫ γY` and
  `γY ≫ β = u ≫ γX`.

The conclusion is `Module.Flat (A ⊗[R] k) ((A ⊗[R] k) ⊗[A] B)` for the algebra
structures given by `α` and `β`.

The proof uses two tensor product squares from
`CommRingCat.isPushout_tensorProduct`: `Q2` for `A ⊗[R] k` and `Q3` (flipped)
for `(A ⊗[R] k) ⊗[A] B`. Pasting `Q1` with `Q2` (`IsPushout.paste_horiz`) and
rewriting `r ≫ α = tY ≫ γY` gives a pushout square `OY` with top
`tY ≫ γY : a₀ ⟶ A`, left `gK`, right `A ⟶ A ⊗[R] k` and bottom
`K ⟶ k ⟶ A ⊗[R] k`. Pasting `OY` with `Q3` and rewriting with `hu` and `hβ`
gives a pushout square `OX` with top `tX ≫ γX : a₀ ⟶ B`, left `gK`, right
`B ⟶ F ⊗[A] B` and bottom `K ⟶ F ⟶ F ⊗[A] B`.

`IsPushout.of_left'` cancels `PY` from `OY`. The result is a pushout square
`TY` with top `γY : aY ⟶ A`, left `iY`, right `A ⟶ F`, and bottom the map
`ψY : ΓY ⟶ F` that `PY` induces. In the same way `TX`, obtained from `OX` and
`PX`, has top `γX : aX ⟶ B`, left `iX`, right `B ⟶ F ⊗[A] B`, and bottom
`ψX : ΓX ⟶ F ⊗[A] B`. Lemma A applied to `TY` and `TX` shows that `ψY` and
`ψX` are localizations. The square `φ ≫ ψX = ψY ≫ (F ⟶ F ⊗[A] B)` is checked
on the two legs of `PY` (`PY.hom_ext`), using `hφ₁`, `hφ₂`, `hβ`, the `desc`
equations of `PX` and `PY`, and the commutativity of `Q3`. Lemma B then makes
the map `F ⟶ F ⊗[A] B`, `c ↦ c ⊗ 1`, flat. `RingHom.flat_algebraMap_iff`
turns this into `Module.Flat F (F ⊗[A] B)`.

## Scheme lemmas

**`germ_stalkMap_eq_appLE_germ`.** For `f : X ⟶ Y`, opens `U` of `Y` and
`V ≤ f ⁻¹ᵁ U` of `X`, and `x ∈ V`, the germ at `f x` followed by
`f.stalkMap x` equals `f.appLE U V e` followed by the germ at `x`. This
follows from `Scheme.Hom.germ_stalkMap` and `TopCat.Presheaf.germ_res`.

**`appLE_eq_of_eq` and `SpecMap_appLE_top_top`.** These are technical
rewriting lemmas. The first transports `appLE` along an equality of
morphisms. The second says that `(Spec.map r).appLE ⊤ ⊤ e` is
`(Spec.map r).appTop`.

**`fromSpecResidueField_appLE`.** For an open `US ∋ s` of `S`, the section
map `(S.fromSpecResidueField s).appLE US ⊤ e`, followed by the isomorphism
`Scheme.ΓSpecIso : Γ(Spec κ(s), ⊤) ≅ κ(s)`, equals
`S.presheaf.germ US s ≫ S.residue s`. Proof: unfold `fromSpecResidueField` as
`Spec.map (S.residue s) ≫ S.fromSpecStalk s`, then use
`Scheme.Hom.comp_appLE`, `Scheme.fromSpecStalk_app` and the naturality of
`ΓSpecIso`.

**`isPushout_residue` (the square `Q1`).** If `US ∋ s` is affine, then the
square with top `germ : Γ(S, US) ⟶ 𝒪_{S,s}`, left
`(S.fromSpecResidueField s).appLE US ⊤ e`, right `S.residue s` and bottom
`(Scheme.ΓSpecIso κ(s)).hom` is a pushout. It commutes by
`fromSpecResidueField_appLE`. The bottom map is an isomorphism. The germ is an
epimorphism, because over the affine open `US` the stalk is a localization of
`Γ(S, US)` (`IsAffineOpen.isLocalization_stalk`, `IsLocalization.epi`).
`IsPushout.of_horiz_isIso_epi` concludes.

**`flat_fiber_stalk` (the scheme assembly).** This is the bridge for
arbitrary pullback squares. Its data are `p : X ⟶ Y`, `q : Y ⟶ S`,
`πX : X ⟶ S` with `p ≫ q = πX`, a point `x`, the point `s = q (p x)`, two
pullback squares
`HX : IsPullback aX bX πX (S.fromSpecResidueField s)` and
`HY : IsPullback aY bY q (S.fromSpecResidueField s)`, and a flat
`fs : Xs ⟶ Ys` with `fs ≫ aY = aX ≫ p` and `fs ≫ bY = bX`. It concludes
flatness of `F ⊗[A] B` over `F` for `R = 𝒪_{S,s}`, `A = 𝒪_{Y,p x}`,
`B = 𝒪_{X,x}`. The proof:

1. Substitute `πX = p ≫ q`. Choose affine opens (`exists_isAffineOpen_mem_and_subset`):
   `US ∋ s` in `S`, `UY ∋ p x` in `Y` with `UY ≤ q ⁻¹ᵁ US`, and `UX ∋ x` in
   `X` with `UX ≤ p ⁻¹ᵁ UY`. All of `Spec κ(s)` maps into `US`, because its
   only image point is `s` (`Scheme.fromSpecResidueField_apply`).
2. Put `UYs = aY ⁻¹ᵁ UY ⊓ bY ⁻¹ᵁ ⊤` and `UXs = aX ⁻¹ᵁ UX ⊓ bX ⁻¹ᵁ ⊤`. They are
   affine: by `Scheme.Hom.isPullback_resLE`, each is a fibre product of affine
   schemes. From `fs ≫ aY = aX ≫ p` follows `UXs ≤ fs ⁻¹ᵁ UYs`.
3. `isIso_pushoutSection_of_isAffineOpen` and `isIso_pushoutSection_iff`
   (Mathlib, `Morphisms/Flat.lean`) give the pushout squares
   `PY : IsPushout (q.appLE US UY) (g.appLE US ⊤) (aY.appLE UY UYs) (bY.appLE ⊤ UYs)`
   and the analogous `PX` for `(p ≫ q).appLE US UX`, where
   `g = S.fromSpecResidueField s`. In other words,
   `Γ(Ys, UYs) = Γ(Y, UY) ⊗_{Γ(S, US)} Γ(Spec κ(s), ⊤)`, and likewise for `X`.
4. Apply `flat_of_sections` with `u = p.appLE UY UX` (and
   `Scheme.Hom.appLE_comp_appLE` for `tY ≫ u = tX`) and `φ = fs.appLE UYs UXs`.
   This map is flat by `Scheme.Hom.flat_appLE`, since both opens are affine.
   Its two compatibilities are the section maps of `fs ≫ aY = aX ≫ p` and of
   `fs ≫ bY = bX` (`appLE_comp_appLE`, `appLE_eq_of_eq`). Take `Q1` from
   `isPushout_residue`, `α = q.stalkMap (p x)` and `β = p.stalkMap x`. The maps
   `γY` and `γX` are the germs at `p x` and at `x`, which are localizations by
   `IsAffineOpen.isLocalization_stalk`. Their compatibilities with `α` and `β`
   are instances of `germ_stalkMap_eq_appLE_germ`.

## The theorem

`fiberStalkFlatness` introduces `S X Y f x` and the flatness hypothesis. It
applies `flat_fiber_stalk` with `p = f.left`, `q = Y.hom`, `πX = X.hom`, and
`Over.w f : f.left ≫ Y.hom = X.hom`. Then `q (p x) = Y.hom (f.left x)` is
exactly the point `s` of the statement. The squares are the chosen pullbacks
`IsPullback.of_hasPullback X.hom g` and `IsPullback.of_hasPullback Y.hom g`,
with `g = S.fromSpecResidueField s`. These are the objects
`((Over.pullback g).obj X).left` and `((Over.pullback g).obj Y).left`. The map
is `fs = ((Over.pullback g).map f).left`. By `Over.pullback_map_left` it is
`pullback.lift (pullback.fst _ _ ≫ f.left) (pullback.snd _ _) _`, so its two
compatibilities are `pullback.lift_fst` and `pullback.lift_snd`. Its flatness
is the hypothesis of the statement.

The `letI` algebra structures of the statement are definitionally those used
by `flat_fiber_stalk`: `R → A` is `(Y.hom.stalkMap y).hom` and `A → B` is
`(f.left.stalkMap x).hom`. The statement's `R`-algebra structure on `B` does
not occur in the conclusion.

## Relation to the source

Stacks Theorem 37.16.2 (tag 039C) identifies the local rings of the fibres
`Y_s`, `X_s` with `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` and `𝒪_{X,x}/𝔪_s 𝒪_{X,x}`. The Lean
proof does not state this identification. It shows directly that `F` and
`F ⊗[A] B` are localizations of the section rings `Γ(Ys, UYs)` and
`Γ(Xs, UXs)`, compatibly with the section map of the fibre morphism. That is
enough to transfer flatness. The proof uses `Flat` of the whole fibre
morphism only through its section maps between affine opens.
