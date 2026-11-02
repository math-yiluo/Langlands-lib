# Finite type models of an open of an affine scheme

Module `Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AffinePinching`, namespace
`Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation`. It imports the ring lemmas of
`Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AwayBijective`.

This module formalizes Stacks, Limits, Lemma 32.5.3 (Tag 07RN) for an affine scheme `S`, in the
single-level, cofinal form used by the absolute Noetherian approximation of algebraic spaces
(FL proof task 8d02331e, pieces RA and PO). Sources: the registered folder
`stacks-noetherian-approximation-2026-11-01` (page `07RN.html`) and the registered folder
`stacks-noetherian-approximation-rings-2026-11-02` (pages `01Z7.html`, `01Z8.html`, `01Z9.html`).

## Relation to Tag 07RN

Tag 07RN: let `S` be quasi-compact and quasi-separated, `V ⊆ S` a quasi-compact open, and
`V = lim V_i` a directed limit of schemes of finite type over `ℤ` with affine transition maps.
Then `S = lim S_j` for a directed system of schemes `S_j` of finite type over `ℤ` with affine
transition maps, with opens `V'_j ⊆ S_j`, isomorphisms `V'_j ≅ V_{α(j)}` and compatibilities.

Its proof first reduces to the case `S = U ∪ V` with `U` affine. When `S` itself is affine,
`U = S` and `W = U ∩ V = V`. The proof then constructs, for every `i` beyond some index, the pinched
ring `B_i = B ×_R R_i` (with `B = Γ(S)`, `R = Γ(V)`, `R_i = Γ(V_i)`), shows that
`V_i → Spec R_i → Spec B_i` is an open immersion (via Tag 01Z9), and takes the finite type
subalgebras `A_{i,p} ⊆ B_i` of Tag 01Z7 for which `V_i → Spec A_{i,p}` is still an open immersion.
For affine `S` the glued scheme `S_{i,p}` is `Spec A_{i,p}` itself, and `V'_j` is the image of
`V_i`.

This module formalizes exactly this per-index construction: for every given index there is a
smaller (cofiltered category) or larger (directed preorder) index `i` and one finite type ring
`A` with the properties of `S_j = Spec A_{i,p}` and `V'_j`. It does **not** state that `S` is the
limit of a system of such models, nor the transition maps between models; that is, it is the
cofinal datum extracted from the proof, not the full statement of Tag 07RN. The extra condition
that finitely many prescribed global functions on `S` come from `A` is internal: it corresponds to
the "finitely many additional elements" of the proof of Tag 01Z7 and was requested by the PO piece
of the FL task to obtain cofinality.

## Definitions

- `FiniteTypeOpenModel π ι T`, for morphisms `π : V ⟶ Y` and `ι : V ⟶ S` with `ι` an open
  immersion and a set `T ⊆ Γ(S, ⊤)`: a structure with fields
  - `A : CommRingCat` with `finiteType : Algebra.FiniteType ℤ A` (an instance);
  - `φ : S ⟶ Spec A` and `e : Y ⟶ Spec A` with `isOpenImmersion : IsOpenImmersion e` (an
    instance);
  - `isPullback : IsPullback π ι e φ`: the square `V → Y → Spec A`, `V → S → Spec A` commutes and
    is a pullback square of schemes;
  - `preimage_opensRange : φ ⁻¹ᵁ e.opensRange = ι.opensRange`: `φ` pulls the image of `Y` back to
    the image of `V`;
  - `exists_appTop_eq : ∀ x ∈ T, ∃ a, φ.appTop a = x`: each element of `T` is the image of a
    global function of `Spec A`.

  For affine `S` and `π = c.π i` this is the datum `S_j = Spec A`, `V'_j = e(Y)`, `V'_j ≅ V_i`,
  `V = φ⁻¹(V'_j)` of Tag 07RN at one index `j`.

## Results

- `exists_finiteTypeOpenModel_of_isLimit` (Tag 07RN for affine `S`, cofinal form). Let `I` be a
  cofiltered category and `D : I ⥤ Scheme` a diagram with affine transition maps
  (`IsAffineHom (D.map f)`), each `D i` quasi-compact (`CompactSpace`) and locally of finite type
  over `Spec ℤ` (`LocallyOfFiniteType (terminal.from (D.obj i))`); together these say that each
  `D i` is of finite type over `ℤ`. Let `c` be a limit cone of `D`, `S` an affine scheme,
  `ι : c.pt ⟶ S` an open immersion, `T ⊆ Γ(S, ⊤)` a finite set and `i₀ : I`. Then there are
  `i : I` with a morphism `i ⟶ i₀` and a `FiniteTypeOpenModel (c.π.app i) ι T`.
- `exists_le_finiteTypeOpenModel_of_isLimit`: the same for an inverse system `D : Iᵒᵖ ⥤ Scheme`
  indexed by a nonempty directed preorder `I`: for every `i₀` there is `i ≥ i₀` with a
  `FiniteTypeOpenModel (c.π.app (op i)) ι T`. This is the shape of Tag 07RN's directed set.

Auxiliary lemmas (all proved here):

- `bijective_awayMap_of_isLocalization`: `Localization.awayMap s g : B_g → R_{s g}` is bijective if
  it is identified, through any localizations `M` of `B` at `g` and `N` of `R` at `s g`, with a
  bijective ring map `M → N` compatible with `s`.
- `bijective_awayMap_comp`: bijectivity of localization maps `A_a → B_{f a} → C_{g (f a)}` is
  stable under composition.
- `finiteType_of_locallyOfFiniteType`: a scheme locally of finite type over `ℤ` has finite type
  `ℤ`-algebras of sections over affine opens. `finiteType_int_of_ringEquiv`: finite type over `ℤ`
  transfers along ring isomorphisms. `isLocallyNoetherian_of_locallyOfFiniteType`: a scheme
  locally of finite type over `ℤ` is locally Noetherian.
- `exists_forall_of_isCofiltered`: finitely many properties of objects of a cofiltered category,
  each stable under morphisms and each true somewhere, hold simultaneously at some object over any
  given object.
- `appTop_π_map_appTop`: compatibility of global sections along the cone legs.
- `exists_appTop_π_eq_isAffineOpen_basicOpen`: a global function on the limit whose basic open is
  affine comes from a level where its basic open is affine (from Mathlib's
  `exists_isAffineOpen_preimage_eq`, `exists_appTop_π_eq_of_isLimit` and
  `exists_map_preimage_eq_map_preimage`, the Mathlib forms of the limit lemmas the proof of
  Tag 07RN cites).
- `exists_level_basicOpen_cover`: a finite cover of the limit by affine basic opens of global
  functions, together with finitely many further global functions, comes from a level below any
  given one.
- `bijective_awayMap_appTop_of_isOpenImmersion`: for an open immersion `ι : X ⟶ S` of
  quasi-compact quasi-separated schemes with `D(g) ⊆ ι(X)`, the localization
  `Γ(S)_g → Γ(X)_{ι^* g}` is bijective (the equality `B_{g_l} = R_{s(g_l)}` of the proof of
  Tag 07RN).
- `isOpenImmersion_toSpecΓ_comp_SpecMap`: for a quasi-affine `X` and `ψ : A ⟶ Γ(X, ⊤)` such that
  `A_{a_l} → Γ(X)_{ψ a_l}` is bijective for each `l` and the basic opens of the `ψ a_l` cover `X`,
  the composite `X ⟶ Spec Γ(X) ⟶ Spec A` is an open immersion with image in `⋃ D(a_l)` (the
  scheme conclusion of Tags 01Z7 and 01Z9).

## Proof of the main theorem

The implemented proof follows the affine case of the proof of Tag 07RN.

1. Each `D i` is locally Noetherian, hence quasi-separated; the limit `c.pt` is quasi-compact
   (Mathlib's `Scheme.compactSpace_of_isLimit`) and quasi-separated (it has an open immersion into
   the affine `S`).
2. The image of `ι` is quasi-compact, so it is a finite union of basic opens `D(g_l)` of `S`
   (`isBasis_basicOpen`, `exists_finite_of_isCompact`). Their preimages `D(s g_l)` in the limit,
   with `s = ι.appTop`, are affine and cover `c.pt`.
3. By `exists_level_basicOpen_cover` there are a level `i` below `i₀` and global functions
   `r'_l` and `x'_b` on `D i` mapping to `s g_l` and to `s b` for `b ∈ T`, with every `D(r'_l)`
   affine and the `D(r'_l)` covering `D i`. Hence `D i` is quasi-affine
   (`Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`).
4. Let `t = (c.π.app i).appTop` and let `P = pinchedRing s t = Γ(S) ×_{Γ(c.pt)} Γ(D i)`. The pairs
   `h_l = (g_l, r'_l)` and `(b, x'_b)` lie in `P`. By `bijective_awayMap_appTop_of_isOpenImmersion`
   each `Γ(S)_{g_l} → Γ(c.pt)_{s g_l}` is bijective, so by `bijective_awayMap_pinchedRing_snd`
   (Tag 01Z8/01Z9) each `P_{h_l} → Γ(D i)_{r'_l}` is bijective. The latter ring is
   `Γ(D(r'_l))` (`isLocalization_basicOpen_of_qcqs`), a finite type `ℤ`-algebra since `D(r'_l)` is
   affine; so each `P_{h_l}` is of finite type over `ℤ`.
5. By `exists_finiteType_subalgebra_bijective_awayMap` (Tag 01Z7, ring part) there is a finite type
   `ℤ`-subalgebra `A ⊆ P` containing the `h_l` and the pairs `(b, x'_b)` with every
   `A_{h_l} → P_{h_l}` bijective. Composing (`bijective_awayMap_comp`), every
   `A_{h_l} → Γ(D i)_{r'_l}` is bijective for `ψ = snd ∘ (A ⊆ P) : A → Γ(D i)`.
6. `e = (D i).toSpecΓ ≫ Spec ψ` is an open immersion with image in `⋃ D(h_l)` by
   `isOpenImmersion_toSpecΓ_comp_SpecMap`. That lemma restricts `Spec ψ` over `⋃ D(h_l)`, which is
   an isomorphism by `isIso_SpecMap_restrict_iSup_basicOpen`, and lifts `toSpecΓ` through the open
   immersion `(Spec ψ)⁻¹(⋃ D(h_l)) ⟶ Spec Γ(D i)` with `IsOpenImmersion.lift`.
7. `φ = S.toSpecΓ ≫ Spec φ₀` with `φ₀ = fst ∘ (A ⊆ P)`. The square commutes,
   `c.π i ≫ e = ι ≫ φ`, by naturality of `toSpecΓ` and the defining equation `s ∘ fst = t ∘ snd`
   of `P`. The equality `φ⁻¹(e(D i)) = ι(c.pt)` holds because `e(D i) ⊆ ⋃ D(h_l)`,
   `φ⁻¹ D(h_l) = D(g_l) ⊆ ι(c.pt)` (`toSpecΓ_preimage_basicOpen`), and conversely by the
   commutative square. Mathlib's `IsOpenImmersion.isPullback` then shows the square is a pullback.
8. For `b ∈ T`, the element `(b, x'_b) ∈ A` gives the global function of `Spec A` (through
   `ΓSpecIso`) whose image under `φ.appTop` is `b`.

The directed-preorder corollary applies the main theorem to `Iᵒᵖ`, which is cofiltered.

The main theorem is elaborated with `set_option maxHeartbeats 1000000`, a finite limit above the
default: the proof is long and its cumulative elaboration exceeds the default limit.
