# Supercuspidal representations are projective and injective with fixed central character

Author: Worker 6. Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement
`RepresentedSupercuspidalCentralProjectivityStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.3.6, the Proposition after the Lemma and its
proof, printed p.148 / PDF p.154. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The passage
was read directly. In translation: fix a (smooth) central character
`χ : Z(G) → ℂˣ` and let `M(G)_χ` be the full subcategory of `M(G)` whose objects
are the smooth representations admitting the central character `χ`. Then every
irreducible supercuspidal representation `(τ, W)` of `G` with central character
`χ` is projective and injective in `M(G)_χ`.

The Lemma of VI.3.6 is the separate statement
`RepresentedSupercuspidalSubquotientRealizationStatement` (same directory).

## Statement

The statement quantifies over a field `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`,
so every nonarchimedean local field of any characteristic, and over a group scheme
`G` over `Spec k` with `hG : IsConnectedReductive G`. It installs
`hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology`
on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the
represented VI.5 statements. It then quantifies over

- a group homomorphism `χ : Subgroup.center (rationalPoints G) →* ℂˣ`;
- a smooth complex representation `τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)`
  with carrier in an arbitrary universe `v`, and `hχ : τ.HasCentralCharacter χ`.

It assumes that `τ` is irreducible (`τ.IsIrreducible`) and supercuspidal: for
every actual rational parabolic triple `(p, l, r)` of `G` (a parabolic
`p : P ⟶ G`, a rational Levi `l : M ⟶ P`, a matching geometric unipotent radical
`r : U ⟶ P`, and the multiplication isomorphism `hmul`) with `¬ IsIso p`, the
normalized Jacquet module `(jacquetFunctor p l r hp hr hl hmul).obj τ` is a
subsingleton, that is, zero.

Let `C` be the object property `fun A => A.HasCentralCharacter χ` on
`SmoothRep.{0, u, v} ℂ (rationalPoints G)`. The conclusion is

`Projective (C := C.FullSubcategory) ⟨τ, hχ⟩ ∧ Injective (C := C.FullSubcategory) ⟨τ, hχ⟩`.

## Relation to the source

- **Central character.** `SmoothRep.HasCentralCharacter A χ` says that every
  element `z` of the center of `G(F)` acts on `A` as the scalar `χ z`. This is
  Renard's "admet le caractère central `χ`". The source's `Z(G)` is the center of
  the group `G = G(F)` ("le centre de `G`"), and the statement uses the same
  abstract center `Subgroup.center (rationalPoints G)` as the published
  central-character predicates.
- **Smoothness of `χ`.** The source fixes a smooth `χ`. The statement does not
  assume it, because it is automatic here: `τ` is irreducible, hence nonzero, and
  the published lemma `SmoothRep.HasCentralCharacter.isLocallyConstant`
  (module `Langlands.Representation.Category.CentralCharacterRegularity`) shows
  that a character by which the center acts on a nonzero smooth representation
  is locally constant.
- **The category `M(G)_χ`.** `C.FullSubcategory` is Mathlib's full subcategory of
  smooth representations (carriers in universe `v`) on which the center acts by
  `χ`. An object is a pair of a representation and a proof of the property, and
  `⟨τ, hχ⟩` is `τ` regarded as an object of it. This is the source's `M(G)_χ`.
- **Projective and injective.** `Projective` and `Injective` are Mathlib's
  categorical notions in `C.FullSubcategory`: lifting along every epimorphism,
  and extending along every monomorphism, of that category. The source's proof
  formulates projectivity as: every nonzero, hence surjective, intertwiner
  `p : (π, V) → (τ, W)` with `π` in `M(G)_χ` has an equivariant section; and
  injectivity dually. The two formulations agree. The subcategory is closed
  under subrepresentations, quotients and finite direct sums of smooth
  representations, so kernels, cokernels and pullbacks of its morphisms, computed
  among smooth representations, stay in it. Hence its epimorphisms are the
  surjective intertwiners and its monomorphisms the injective ones, it is abelian,
  and in an abelian category an object is projective (injective) exactly when
  every epimorphism onto it splits (every monomorphism out of it splits). This
  argument explains the agreement; it is not part of the statement.
- **Supercuspidality.** Renard's supercuspidality is vanishing of the normalized
  Jacquet modules `r_P^G` for every proper parabolic `P`. The statement uses the
  same predicate as the published represented VI.3.6 Lemma and VI.5.2–VI.5.4
  statements: every proper actual rational parabolic, with a rational Levi and its
  matching geometric unipotent radical. The normalization twists by a character
  and does not affect vanishing.
- **Universes.** The source does not consider universes. The field universe `u`
  and the carrier universe `v` are independent. Projectivity and injectivity are
  asserted in the category of representations with carriers in universe `v`, for
  every `v` large enough to contain `τ`.

No admissibility, finite-length, unitarity, standard-parabolic or
category-decomposition premise is added; the source assumes none.

## Proof obligation

The proof is a separate obligation. The source argues as follows: reduce to
`π` in the block `M(G)[τ]` (decomposition VI.3.5), as in the proof of the Lemma;
the restrictions of `π` and `τ` to `⁰G` are compact, hence semisimple (VI.3.2,
IV.1.6), so `p` has a `⁰G`-equivariant section `s₀`; since
`Z(G)` acts by `χ` on both, `s₀` is `⁰G Z(G)`-equivariant; averaging
`ḡ · s₀ = π(g) ∘ s₀ ∘ τ(g⁻¹)` over the finite abelian group `G / ⁰G Z(G)` gives a
`G`-equivariant section. Injectivity is similar.
