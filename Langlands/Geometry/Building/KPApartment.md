# The apartment of an equipollence class of valuations

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects. It builds on the
published module `RootDatumValuation`. Given valid data, an `N(k)`-stable
equipollence class `A` of valuations of the root datum of `(G, S)`, it
defines:

- the apartment `A`, as an affine space;
- the action of the actual normalizer points on `A`;
- the filtration groups `U_{a,x,r}`;
- the affine root groups `U_ψ` and `U_{ψ+}`;
- the sets `Ψ ⊆ Ψ′` of affine functionals of Kaletha–Prasad Definition 6.3.4.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- §6.1, from Lemma 6.1.6 to §6.1.8, printed pp. 200–201, PDF pp. 231–232.
  This covers the `V(S)`-action on valuations, its kernel `V(A_G)`,
  equipollence classes, compatibility with `ω` as a property of a class, the
  `N(k)`-action and `n(φ + v) = nφ + n·v`.
- §6.1(c), Definition 6.1.27 and Lemma 6.1.28, printed p. 210, PDF p. 241.
  Here the action of `V(S)` on `A(S)` factors through
  `V(S) → V(S/A_G) = V(S′)`, and `N_ad(k)` preserves the canonical class.
- §6.3, opening paragraph, Definition 6.3.1, Remark 6.3.2, Fact 6.3.3,
  Definition 6.3.4 and Remark 6.3.5, printed pp. 217–218, PDF pp. 248–249.
- Chapter 7, opening paragraphs, printed pp. 235–236, PDF pp. 266–267. There
  each `A(S)` is an affine space under `V(S′)` and is an equipollence class
  of valuations compatible with `ω`, and `N(k)` acts on it as in §6.1.8. In
  general existence of such a class is known only after Chapter 9.

The registered corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`) are used as follows.

- Chapter 6, PDF p. 32:
  - The proof of Lemma 6.1.12 is corrected to `n(φ + v) = nφ + w v`. This is
    `smul_vadd` below.
  - In Definition 6.1.27, `S′` and `G_der` are replaced by `S_ad` and `G_ad`.
  - Above Remark 6.3.5 it is clarified that `a = ψ̇`. This is the root
    attached to `ψ` in `affineRoots` below.
- Chapter 7, PDF p. 33: the added sentences say that `A(S)` carries the two
  affine root systems `Ψ ⊂ Ψ′ ⊂ A(S)*`, and that the action of `N(k)` gives a
  map `N(k) → W(Ψ)_ext`.

## Setting

As in `RootDatumValuation`: `k` is a field, `S` a commutative group scheme
over `Spec k`, and `i : S.toGrp ⟶ G` a homomorphism into a group scheme `G`.
The instances `[Mono i.hom.hom.left]` (for the normalizer action) and
`[IsAffineHom G.X.hom]` (for `relativeRoots i`) are assumed. The intended
case is KP's: `G` connected reductive and `i` the inclusion of a maximal
`k`-split torus. `ω : kˣ → ℝ` is meant to be the valuation of `k`. For a
nonarchimedean local field it is the normalized order. No reductivity,
splitness, maximality or Henselian hypothesis is imposed, because none is
needed to state the definitions.

`V S` is the Library's real vector space `V(S)`, `eval S a` is evaluation of
a character, and `normalizerPoints i` is the actual group `N(k)` of rational
points normalizing `S`. Its published linear action on `V(S)` is
`normalizerAction i`. The root groups `rootGroupPoints i a = U_a(k)` are the
rational points of the actual relative root subgroup functors, as in
`RootDatumValuation`.

## The space of translations

- `rootAnnihilator i` is the common kernel in `V(S)` of the relative roots
  (`mem_rootAnnihilator`). By `vadd_eq_self_iff` below it is the stabilizer in
  `V(S)` of every valuation. KP state that this stabilizer is `V(A_G)`, with
  `A_G` the maximal split central torus. The Library has no `A_G`, so we use
  the common kernel of the roots instead.
- `TranslationSpace i` is the quotient `V(S) ⧸ rootAnnihilator i`. KP (§6.1(c))
  identify `V(S)/V(A_G)` with `V(S/A_G) = V(S′)`, which they write as the
  translation space of `A(S)` in §6.3 and Chapter 7. By the corrected
  Definition 6.1.27 it is also `V(S_ad)`. Those identifications need `A_G`,
  `G_der` or `G_ad`, which are not in the Library, and they are not made
  here. `TranslationSpace i` is our substitute, defined from `S` and `G`
  directly.
- `rootForm i α : TranslationSpace i →ₗ[ℝ] ℝ` is the linear form induced by
  the root `α ∈ relativeRoots i` (`rootForm_mk`). It is KP's root `a` viewed
  as a function on the space of translations.
- `smul_mem_rootAnnihilator` and `map_normalizerAction_rootAnnihilator`:
  `N(k)` preserves the common kernel. The proof uses the published
  `eval_normalizer_smul`, `a(n·v) = (n⁻¹·a)(v)`, and `n⁻¹·Φ ⊆ Φ`.
- `translationAction i : normalizerPoints i →* (TranslationSpace i ≃ₗ[ℝ]
  TranslationSpace i)` is the induced linear action
  (`translationAction_mk`). This is the linear part of the action of `N(k)`
  on `A` (KP 6.1.8).
- `doubleRootGroupPoints i a` is `U_{2a}(k)`, the published root group at
  `2 • a` when `2a ∈ Φ` and `{1}` otherwise. This is KP's convention
  `U_{2a} = {1}` if `2a ∉ Φ`, stated before Definition 6.3.4.

## Laws for a single valuation

These are proved for every `φ` with `IsRootDatumValuation i φ`.

- `IsRootDatumValuation.exists_ne_top`: for a root `a`, some `u ∈ U_a(k)` has
  `φ_a(u) ≠ ∞`. This follows from V 0, since `φ_a(U_a(k))` has at least three
  elements.
- `vadd_eq_self_iff`: `v +ᵥ φ = φ ↔ v ∈ rootAnnihilator i`. This is KP's
  statement after Lemma 6.1.6 that the stabilizer of any point is the kernel
  of the action, with `V(A_G)` replaced by the common kernel of the roots.
  For "only if", compare `φ_a(u) + a(v) = φ_a(u)` at a finite value. For "if",
  note that `a(v) = 0` on roots and `φ_a = ∞` off roots.
- `vadd_eq_vadd_iff`: `v +ᵥ φ = w +ᵥ φ ↔ v − w ∈ rootAnnihilator i`.
- `filtrationSubgroup`: the published set `rootFiltration i φ a r` as a
  subgroup of `G(k)`. For a root this is V 1. For a non-root `a` the set is
  `U_a(k)`, because `φ_a = ∞` there. `coe_filtrationSubgroup` and
  `filtrationSubgroup_antitone` give its carrier and its antitonicity in `r`.

## Valid apartment data (`KPApartmentData`)

`KPApartmentData i ω` is a structure with three fields:

- `carrier : Set (RootFunctionFamily S G)`, the class `A`;
- `exists_eq_orbit`: `A` is the `V(S)`-orbit of some `φ` such that
  `IsRootDatumValuation i φ` and `IsSplitTorusCompatible i ω φ` hold;
- `smul_mem`: `A` is stable under `n • ·` for every `n ∈ N(k)`.

This is the hypothesis of KP Chapter 7, opening paragraphs. There each
`A(S)` is an equipollence class of valuations that are compatible with `ω`,
and `N(k)` acts on it as in §6.1.8. It is also the input "let `A` be an
equipollence class" of §6.3, as used there: Fact 6.3.3 uses an action of
`N(k)` on `A`. Compatibility with `ω` is a property of a class (KP after
Definition 6.1.7, here `IsSplitTorusCompatible.vadd`), so requiring it of one
representative is the same as requiring it of all.

Compatibility with `ω` is included because without it the class is not
determined. Every axiom V 0–V 5 is preserved by `φ ↦ cφ` for real `c > 0`.
When `Φ` is nonempty, `cφ` with `c ≠ 1` is not equipollent to `φ`, since
`φ_a` takes two different finite values on `U_a(k) ∖ {1}` by V 0 and V 1.
So V 0–V 5 alone allow many classes. KP's uniqueness results
(Propositions 6.2.5 and 6.2.6, cited in the Chapter 7 introduction) are for
classes compatible with `ω`.

Only the `S(k)`-part of V 6 is available (see `RootDatumValuation`), so this
type is weaker than KP's hypothesis whenever `Z(k) ≠ S(k)`. KP's canonical
class of Definition 6.1.27 for quasi-split `G` satisfies `smul_mem` by
Lemma 6.1.28. The type is ordinary data. It is not a typeclass, and no
statement here says that a term exists for a given `G`.

Consequences proved for every element of the carrier:

- `isRootDatumValuation_of_mem` and `isSplitTorusCompatible_of_mem` (by the
  published `.vadd` laws);
- `vadd_mem`;
- `equipollent_of_mem`;
- `mem_iff_equipollent`: `A` is a full equipollence class.

## The apartment

- `D.Apartment` is the type of points of `A`: a structure with the valuation
  `val` and the proof `mem` that it lies in `D.carrier`, with `@[ext]`. As in
  KP (§6.3 and Chapter 7: "every point `x` of `A` is by definition a
  valuation"), a point *is* a valuation. There is no chosen origin.
  `Apartment.isValuation` and `Apartment.isSplitTorusCompatible` record the
  axioms at each point. The type is nonempty.
- `AddTorsor (TranslationSpace i) D.Apartment`. The class of `w` acts by
  `w +ᵥ x` (`val_mk_vadd`), which is well defined by `vadd_eq_vadd_iff`.
  `x -ᵥ y` is the class of some `v` with `x = v +ᵥ y` (`vsub_def`,
  `vsub_eq_mk`). It is unique modulo `rootAnnihilator i`, again by
  `vadd_eq_vadd_iff`. So `A` is an affine space under `V(S)/V(A_G)` (KP: under
  `V(S′)`, see above). This is the *reduced* apartment. The enlarged apartment
  (KP Definition 4.3.2) is a different object and is not defined here.

## The action of `N(k)`

- `MulAction (normalizerPoints i) D.Apartment` is the published action
  `(n • φ) a g = φ (n⁻¹·a) (n⁻¹ g n)` of KP 6.1.8 restricted to `A`
  (`val_smul`), using `smul_mem`.
- `smul_vadd`: `n • (v +ᵥ x) = translationAction i n v +ᵥ n • x`. This is KP's
  `n(φ + v) = nφ + n·v` (6.1.8 and the corrected proof of Lemma 6.1.12),
  passed to the quotient.
- `D.normalizerAffineEquiv : normalizerPoints i →* (D.Apartment ≃ᵃ[ℝ]
  D.Apartment)` packages the action as affine automorphisms whose linear parts
  are `translationAction i` (`normalizerAffineEquiv_apply`). This is the
  actual normalizer action. It is distinct from the affine Weyl group `W(Ψ)`
  generated by reflections in affine roots. For the published module
  `AffineRootSystem`, that group is `AffineRootSystem.affineWeylGroup
  D.affineRoots`. KP (corrections, Chapter 7) compare the two through
  `N(k) → W(Ψ)_ext`. That comparison is not stated here.

## Filtration groups and affine root groups

- `D.filtration x a r` is `U_{a,x,r}` for `x ∈ A` (KP Definition 6.1.2, V 1;
  Chapter 7 introduction), the subgroup `filtrationSubgroup` at the valuation
  `x`. `mem_filtration` gives `g ∈ U_a(k)` and `r ≤ x_a(g)`.
  `filtration_le_rootGroupPoints` and `filtration_antitone` hold.
- `filtration_vadd`: `U_{a,x+v,r} = U_{a,x,r−a(v)}` (KP Lemma 6.1.6, also
  `U_{a,y,r} = U_{a,x,r+⟨a,x−y⟩}` in §6.3).
- `D.affineRootGroup a ψ` is `⋂_{x ∈ A} U_{a,x,ψ(x)}` for a character `a` and
  an affine functional `ψ : A →ᵃ[ℝ] ℝ`. KP Definition 6.3.1 defines `U_ψ` as
  `U_{a,x,ψ(x)}` for any `x`, when `ψ` has derivative `a ∈ Φ`. The
  intersection is our way of expressing independence of `x` without choosing a
  point. `affineRootGroup_eq_filtration` proves that it equals
  `U_{a,x,ψ(x)}` for each `x` whenever `ψ.linear = rootForm i α`; the proof is
  `filtration_vadd`. For other `ψ` the intersection has no source meaning and
  is not used by the definitions below. The root `a` is an explicit argument,
  because the Library does not prove that `α ↦ rootForm i α` is injective. For
  a split torus `S` it is injective, since the character lattice embeds in
  `V(S)*`.
- `mem_affineRootGroup_iff`: `U_ψ = {u ∈ U_a(k) | x_a(u) ≥ ψ(x)}` for any
  `x ∈ A` (KP Remark 6.3.2). `affineRootGroup_le_rootGroupPoints` and
  `affineRootGroup_add_const_antitone` also hold.
- `D.affineRootGroupPlus a ψ` is `U_{ψ+}`, the subgroup supremum of the
  `U_{ψ+c}` for real `c > 0`, where `ψ + c` is `ψ + AffineMap.const`. KP define
  `U_{ψ+} = ⋃_{ψ′ > ψ} U_{ψ′}`. An affine functional with `ψ′ > ψ` everywhere
  is `ψ + c` with `c > 0`, because a nonconstant affine function on a real
  affine space takes negative values. So the two index sets agree. This
  argument is not formalized: the Lean definition uses the constants directly.
  The family is directed (`affineRootGroup_add_const_antitone`), so the
  supremum is the union (`mem_affineRootGroupPlus`). Also
  `affineRootGroupPlus_le` holds, and `mem_affineRootGroupPlus_iff`:
  `U_{ψ+} = {u ∈ U_a(k) | x_a(u) > ψ(x)}` when `ψ` has derivative `a`.

## Affine roots (KP Definition 6.3.4)

- `D.extendedAffineRoots` is `Ψ′`: the affine functionals `ψ` with
  `ψ.linear = rootForm i α` for a root `α` and `U_{ψ+} ≠ U_ψ`.
- `D.affineRoots` is `Ψ`, the affine root system of `G` with respect to `S`:
  the `ψ` with `ψ.linear = rootForm i α` for a root `α` and
  `U_ψ ⊈ U_{ψ+} · U_{2α}(k)`, where `·` is the pointwise product of subsets
  and `U_{2α}(k)` is `doubleRootGroupPoints i α`. The root `α` is the
  derivative `a = ψ̇` of the corrections.
- `affineRoots_subset_extendedAffineRoots`: `Ψ ⊆ Ψ′` (KP after Remark 6.3.5).
- `D.affineFunctional α x r` is the unique affine functional with derivative
  `α` and value `r` at `x` (KP after Definition 6.3.1), with
  `affineFunctional_apply` and `affineFunctional_linear`.
  `filtration_eq_affineRootGroup` proves `U_{α,x,r} = U_ψ` for this `ψ`: the
  two indexings of KP agree.

Both sets have type `Set (D.Apartment →ᵃ[ℝ] ℝ)`, with
`[AddTorsor (TranslationSpace i) D.Apartment]`. So they are direct inputs to
the published `AffineRootSystem` module (`hyperplane`, `IsSpecialPoint`,
facets, chambers and vertices), which is stated for any real affine space.

## Not formalized

- That `Ψ` and `Ψ′` are affine root systems with derivative system `Φ`
  (KP Proposition 6.3.13), and that their hyperplanes agree (KP 6.3.8).
- Fact 6.3.3, `U_{nψ} = n U_ψ n⁻¹`. It needs `n U_a(k) n⁻¹ = U_{n·a}(k)`,
  which is not in the Library.
- The identification of `TranslationSpace i` with `V(S′)` or `V(S_ad)`, and of
  `rootAnnihilator i` with `V(A_G)`. These need `G_der`, `G_ad` and `A_G`.
- Full V 6 on `Z(k)` and V 7 are not conditions of `KPApartmentData`. Later
  modules state them as predicates on `D`: V 6 is `D.IsOmegaCompatible C`
  for the actual centralizer `C : CentralizerDatum i` (module
  `KPCentralizerCompatibility`), and V 7 is `D.IsTopologyCompatible`
  (Worker 1045's module `KPApartmentAxioms`).
- The existence of valid data for any `G`. For quasi-split `G` existence is
  KP Definition 6.1.27 with Lemma 6.1.28; in general it is the descent of
  Chapter 9. This remains an obligation of the parent program.
- The apartments `A(S′)` of the other maximal split tori and the maps
  `A(S) → A(gSg⁻¹)` of Axiom 4.1.4. This module fixes one `i`.

The public name `Building.rootAnnihilator` is an abbreviation for the existing
`RealTorusSpace.relativeCentralDirections`, so the translation quotient uses
the same common kernel as the rational central-directions development.
