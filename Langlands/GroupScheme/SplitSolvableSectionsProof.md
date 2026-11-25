# Sections of the canonical extension of a split solvable group (proof)

`Langlands.GroupScheme.splitSolvableExtensionSections` proves exactly the
published `Langlands.GroupScheme.SplitSolvableExtensionSectionsStatement.{u}`
(Milne 2017, Proposition 16.54; module
[`SplitSolvableSectionsStatement`](SplitSolvableSectionsStatement.md)), for
every universe `u`, every field `k : Type u` and every `G` with
`IsSplitSolvableGroupScheme G`, with no additional hypothesis. The
normality hypothesis on `range i` is not used.

Milne's proof (Milne 2017, Proposition 16.54, printed p. 344) works over
`k` itself. By Proposition 16.52 (printed p. 343), `G` is trigonalizable
over `k`: `G` acts on the variety of maximal flags of a faithful
representation over `k`, and by the fixed point theorem 16.51 it fixes a
flag defined over `k`. Hence the canonical extension exists, `G_u` is split
and `D` is smooth, and Milne concludes with case (d) of Summary 16.29
(printed p. 334), the case of a split unipotent kernel.

The Lean proof does not formalize this trigonalization over `k`. (The
Library's correction of a scheme section for triangular groups,
`IsSplitTorus.exists_section_of_triangular`, assumes an algebraically closed
field.) Instead, it shows that a split solvable group has a pointed
split-torus domination. The Library's `splitTorusDominatedSolvableQuotient`
turns this domination into a unipotent kernel and a torus quotient; it goes
through the algebraic closure internally and then descends. Comparing that
quotient with the given `q` shows that the kernel of `q` has a split
unipotent representative and that `D` is a split torus. The proof then uses
the Library's split-unipotent extension section theorem
`IsTorus.exists_splitUnipotentExtensionSection`, which plays the role of
16.29(d) for existence, and the Library's conjugacy theorem
`solvableMaximalSplitTorusConjugacy` for the conjugacy and maximality
clauses. It uses three helper modules written for this proof:

- [`Rational.SplitSolvablePicardSection`](Rational/SplitSolvablePicardSection.md):
  every quotient map of a split-solvable series has a scheme section
  (torsors under split-solvable groups over Picard-trivial affine bases are
  trivial; `k[t]` and `k[t, t⁻¹]` have trivial Picard group).
- [`Rational.SplitSolvableTorusDomination`](Rational/SplitSolvableTorusDomination.md):
  a split solvable group has a pointed dominant morphism of schemes from a
  split torus (`IsSplitSolvableGroupScheme.hasPointedSplitTorusDomination`).
- [`Rational.SplitSolvableExtensionStructure`](Rational/SplitSolvableExtensionStructure.md):
  `IsSplitSolvableGroupScheme.canonicalExtension_structure`, which says that
  the kernel of `q` has the same range as a smooth connected split unipotent
  closed subgroup `i' : U' ⟶ G`, and that `D` is a split torus.

## Lemmas in this module

In namespace `SplitSolvableSections`, over a field `k`:

- `range_inf_eq_bot`: if `G` is affine and locally of finite type over `k`,
  `j : S ⟶ G` is a closed subgroup with `S` a split torus, and `i : U ⟶ G`
  is a closed subgroup with `U` unipotent, then
  `range j ⊓ range i = ⊥` on every test scheme. This is part 2 of the
  Library's `unipotentMultiplicativeTriviality`, since a split torus is of
  multiplicative type (`IsSplitTorus.isTorus`,
  `IsTorus.isMultiplicativeType`); the two factors are swapped pointwise.
- `isMaximalSplitTorus_of_comp_eq_id`: let `T` be a commutative group
  scheme with `T.toGrp` a split torus, `q : G ⟶ T.toGrp` with
  `range (kernelι q) = range i` for a closed unipotent subgroup `i`, and
  `s : T.toGrp ⟶ G` with `s ≫ q = 𝟙`. Then `IsMaximalSplitTorus s` (module
  [`Rational.SplitTorus`](Rational/SplitTorus.md)). The section is a closed
  subgroup (`IsClosedSubgroup.of_comp_eq_id`). If `f ≫ i'' = s` for a split
  subtorus `i'' : T'.toGrp ⟶ G`, then `range i'' ⊓ range i = ⊥`, so
  `i'' ≫ q` is a monomorphism (`mono_comp_of_inf_eq_bot`); it is split
  epi with right inverse `f` (because `f ≫ i'' ≫ q = s ≫ q = 𝟙`), hence an
  isomorphism, and `f` is its inverse, so `f` is an isomorphism.
- `exists_kernel_point_conj`: let `q : G ⟶ D` have split torus target with
  `range (kernelι q) = range i`, `s` a section of `q`, and `g` a rational
  point of `G`. Then there is a rational point `v` of `U` with
  `s ≫ (G.innerIso g).hom = s ≫ (G.innerIso (v ≫ i.hom.hom)).hom`. Put
  `d = q(g)` and `h = s(d)`. Then `q(g h⁻¹) = d d⁻¹ = 1`, so `g h⁻¹ = i(v)`
  for a rational point `v` of `U`, and `g = i(v) h`. By `innerIso_mul_hom`,
  conjugation by `g` is conjugation by `h` followed by conjugation by
  `i(v)`. Conjugation by `h = s(d)` restricted along `s` is `s` after the
  inner automorphism of `D` by `d` (`innerIso_hom_comp`), which is trivial
  since `D` is commutative (`IsSplitTorus.innerIso_hom`).

## Proof of the theorem

Fix the data of the statement. By `canonicalExtension_structure`, obtain
`i' : U' ⟶ G` with `range i' = range i` (closed, smooth, connected,
unipotent, split unipotent) and `IsSplitTorus D`. Since `D` is a split
torus, it is `T.toGrp` for the commutative group scheme
`T = hD.toCommGroupScheme`; the proof replaces `D` by `T.toGrp` throughout
so that `IsMaximalSplitTorus`, which takes commutative sources, applies.

1. **Existence of a section.** `q` is an fppf quotient by `range i'`, so the
   Library's `IsTorus.exists_splitUnipotentExtensionSection` (module
   [`Rational.SplitUnipotentExtensionSection`](Rational/SplitUnipotentExtensionSection.md)),
   applied with the published `RelativeRoot.splitUnipotentStableVectorSubgroup`
   and `RelativeRoot.torusVectorActionLinearization`, gives `s` with
   `s ≫ q = 𝟙 D`. By `isMaximalSplitTorus_of_comp_eq_id`, every section is
   a maximal split torus of `G`.
2. **Conjugacy of sections.** For sections `s₁`, `s₂`, the published
   `solvableMaximalSplitTorusConjugacy` (for the smooth connected affine
   solvable `G`) gives a rational point `g` of `G` and an isomorphism
   `e : D ≅ D` with `s₁ ≫ (G.innerIso g).hom = e.hom ≫ s₂`. Composing with
   `q` and using that `q` is invariant under inner automorphisms
   (`innerIso_hom_comp_of_isSplitTorus`) gives `𝟙 = e.hom`, so
   `s₂ = s₁ ≫ (G.innerIso g).hom`. Then `exists_kernel_point_conj` replaces
   `g` by `v ≫ i.hom.hom` for a rational point `v` of `U`.
3. **Maximal split tori.** Let `j : S ⟶ G` be a closed subgroup with `S` a
   split torus; replace `S` by `TS.toGrp` for a commutative `TS` as above.
   - Suppose `j` is maximal for inclusion of ranges among closed split tori.
     Then `j` is a maximal split torus: if `f ≫ j'' = j` for a split
     subtorus `j''`, then `range j ≤ range j''`, hence equality by
     hypothesis; both `j` and `j''` then represent `range j''`, so the
     comparison isomorphism `isoOfIsRepresentedBy` satisfies
     `(iso).hom ≫ j'' = j = f ≫ j''`, and cancelling the monomorphism `j''`
     shows `f` is that isomorphism. Take a section `s₀` (part 1).
     `solvableMaximalSplitTorusConjugacy` gives `g` and `e : S ≅ D` with
     `j ≫ (G.innerIso g).hom = e.hom ≫ s₀`. Put
     `s = s₀ ≫ (G.innerIso g).inv`. Then `s ≫ q = s₀ ≫ q = 𝟙`, because
     `(G.innerIso g).inv ≫ q = q`, and `j = e.hom ≫ s`, so
     `range j = range s` (`SubgroupFunctor.range_iso_comp`).
   - Conversely, let `s` be a section with `range j = range s`, and let
     `j' : S' ⟶ G` be a closed split torus with `range j ≤ range j'`. For a
     point `x` of `range j'` over a test scheme, `y = s(q(x))` lies in
     `range s = range j ≤ range j'`, and `q(x y⁻¹) = 1`, so `x y⁻¹` lies in
     `range j' ⊓ range i = ⊥` (`range_inf_eq_bot`). Hence `x = y` lies in
     `range s = range j`, so `range j' ≤ range j` and the ranges are equal.

The declaration depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
