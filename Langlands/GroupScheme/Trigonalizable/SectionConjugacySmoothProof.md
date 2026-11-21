# Conjugacy of sections of trigonalizable groups with smooth unipotent part

Worker 386. The theorem `Langlands.GroupScheme.trigonalizableSectionConjugacySmooth.{u}`
proves the corrected Milne 16.27, exactly
[`TrigonalizableSectionConjugacySmoothStatement.{u}`](SectionConjugacySmoothStatement.md).
It uses `diagonalizableSmoothUnipotentCocycle.exists_coboundary` in both parts and the
Library's `TrigonalizableExtensionSplit.exists_section_of_isAlgClosed` (Milne 16.26(a))
in the forward direction of part (b). Neither result is taken as a hypothesis.

## Notation

`k` is a field in universe `u`, `T₀` is the base `Over.mk (𝟙 (Spec k))`, and `𝔻 Λ` is
`(Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`. For a rational point `g` of
`G`, `inn(g)` is `(G.innerIso g).hom`, the inner automorphism that sends a point `x` to
`g x g⁻¹` (`comp_innerIso_hom`). A group `S` is *diagonalizable* when
`S ≅ 𝔻 Λ'` for some finitely generated abelian group `Λ'` in universe `u`, as in the
target statement.

## Section `Conjugation`

Fixed data: group schemes `G, U, Q` over `Spec k`, homomorphisms `i : U ⟶ G` and
`q : G ⟶ Q`, and `hn : range i = range (kernelι q)` (the range of `i` is the kernel of
`q`).

- `comp_eq_one`: `i ≫ q` is the trivial morphism on underlying schemes. The identity
  point of `U` lies in the range of `i`, hence in the range of `kernelι q`, and
  `mem_range_kernelι_iff` gives the claim.
- `innerIso_hom_comp`: for a rational point `u` of `U`, `inn(i u) ≫ q = q`. It is checked
  on points: `q(g x g⁻¹) = q(g) q(x) q(g)⁻¹` and `q(g) = 1` by `comp_eq_one`.
- `exists_conj_of_comp_eq`: let `k` be algebraically closed, `i` a monomorphism, `U`
  smooth and affine over the base and unipotent, `Λ` finitely generated, and
  `i₀ i₁ : 𝔻 Λ ⟶ G` with `i₀ ≫ q = i₁ ≫ q`. Then there is a rational point `u` of `U`
  with `i₀ ≫ inn(i u) = i₁`. Proof: `QuotientHomCocycle.cocycle` is the difference
  cocycle of `i₀` and `i₁` for the conjugation action `QuotientHomCocycle.action` of
  `𝔻 Λ` on `U` through `i₀`; it is a coboundary of some `v` by
  `diagonalizableSmoothUnipotentCocycle.exists_coboundary`,
  and `QuotientHomCocycle.cocycle_eq_coboundary_iff` turns the coboundary into the
  conjugation.
- `exists_eq_comp_inner`: same hypotheses on `k, i, U`; let `j : S ⟶ G` with `S`
  diagonalizable and `s : Q ⟶ G` with `s ≫ q = 𝟙 Q`. Then there is a rational point `u`
  of `U` with `j = j ≫ q ≫ s ≫ inn(i u)`. Proof: for an isomorphism `e : S ≅ 𝔻 Λ'`,
  apply `exists_conj_of_comp_eq` to `i₀ = e.inv ≫ j ≫ q ≫ s` and `i₁ = e.inv ≫ j`, which
  have the same composite with `q` because `s ≫ q = 𝟙`, then precompose with `e.hom`.
- `range_le_range_section`: same hypotheses; let `j' : S' ⟶ G` with `S'` diagonalizable,
  `s` a section of `q`, and `range s ≤ range j'`. Then `range j' ≤ range s`. Proof: with
  `g = i u` from `exists_eq_comp_inner` for `j'` and `s`, every point `x` in the range of
  `j'` satisfies `x = g · s(q x) · g⁻¹`. The point `s(q x)` is in the range of `s`, hence
  of `j'`, so `s(q x) = g · s(q(s(q x))) · g⁻¹ = g · s(q x) · g⁻¹`, using `s ≫ q = 𝟙`.
  Comparing the two equations gives `x = s(q x)`, which is in the range of `s`.

## Main theorem

`trigonalizableSectionConjugacySmooth : TrigonalizableSectionConjugacySmoothStatement.{u}`.

Given the data of the statement (`k` algebraically closed, `G` affine of finite type,
`i : U ⟶ G` a closed normal unipotent subgroup with `U` smooth, `q : G ⟶ 𝔻 Λ` an fppf
quotient by the range of `i`):

- `i` is a monomorphism (`IsClosedSubgroup.mono_overHom`) and `U` is affine over the base,
  since a closed immersion followed by the affine structure morphism of `G` is affine.
- `hn` is the last component of `RelativeRoot.IsFppfQuotient`.
- Every section `s` of `q` is a closed subgroup: `G` is affine, `s ≫ q = 𝟙` is a closed
  immersion on underlying schemes, so `s` is one by `IsClosedImmersion.of_comp`.

(a) For two sections `s₁, s₂`, `exists_conj_of_comp_eq` with `i₀ = s₁`, `i₁ = s₂` gives
`u` with `s₂ = s₁ ≫ inn(i u)`.

(b), forward direction. Let `j : S ⟶ G` be a closed diagonalizable subgroup that is
maximal. `TrigonalizableExtensionSplit.exists_section_of_isAlgClosed` gives a section
`s₀` of `q`.
`exists_eq_comp_inner` for `j` and `s₀` gives `u` with
`j = j ≫ q ≫ s₀ ≫ inn(i u)`. The homomorphism `s = s₀ ≫ inn(i u)` is a section of `q` by
`innerIso_hom_comp`, hence a closed diagonalizable subgroup (with `S' = 𝔻 Λ` and the
identity isomorphism), and the range of `j` is contained in the range of `s`: a point
`y ≫ j` equals `(y ≫ j ≫ q) ≫ s`. Maximality gives `range j = range s`.

(b), converse. Assume `range j = range s` for a section `s`. If `j' : S' ⟶ G` is a
closed diagonalizable subgroup with `range j ≤ range j'`, then `range s ≤ range j'`, and
`range_le_range_section` gives the reverse inclusion, so `range j = range j'`.

## Scope

The field may have any characteristic, and neither the diagonalizable quotient nor
`U` is required to be connected. The theorem assumes `U` smooth; it does not prove
section conjugacy for nonsmooth `U` with smooth diagonalizable quotient. It uses only
the algebraically closed case of extension splitting, not the perfect-field case.

## Provenance

This is an implemented proof route, not a transcription of a source. Part (a) follows the
cohomological formulation of SGA 3 XVII 5.1.1 ii) b): two sections differ by a
one-cocycle of `D(Λ)` in `U`, and such cocycles are coboundaries
(`DiagonalizableSmoothUnipotentCocycle`). Part (b) follows Milne's argument for 16.27(b)
(Milne 2017, p. 333, as corrected in the Markdown of
`TrigonalizableSectionConjugacySmoothStatement`): the forward direction uses the existence
of a section (Milne 16.26(a), already proved in `Trigonalizable.ExtensionSplitAlgClosed`).
Instead of Milne's appeal to 14.17 (`S ∩ U = e`), both directions use `exists_eq_comp_inner`,
which applies the
cocycle theorem to a diagonalizable subgroup `S` and the section through `q`.
