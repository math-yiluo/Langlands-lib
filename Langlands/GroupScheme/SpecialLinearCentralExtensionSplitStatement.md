# Statement: central extensions of `SL₂` split uniquely

Worker 75.

`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, which provides `Flat` (used for fppf
  covers);
- [`SpecialLinear`](SpecialLinear.md), which provides
  `SpecialLinear.groupScheme n R`, the affine group scheme of determinant-one
  `n × n` matrices over `Spec R`;
- [`Rational.Characters`](Rational/Characters.md), which provides `IsCentral` and the
  centre subgroup functor `center`.

Through these imports it also uses `Gm.toSpecZ` from [`Multiplicative`](Multiplicative.md),
`SubgroupFunctor.range` from [`SubgroupFunctor`](SubgroupFunctor.md), and `GroupScheme`,
`GroupScheme.baseChange` and `CommGroupScheme` from
[`Langlands.AbelianScheme.GroupScheme`](../AbelianScheme/GroupScheme.md). `GroupScheme S`
is `Grp (Over S)`, a homomorphism of group schemes `f : G ⟶ H` has underlying morphism
`f.hom.hom : G.X ⟶ H.X` in `Over S`, and `Z.toGrp` is the underlying group scheme of a
commutative group scheme `Z`.

It states Gabber's theorem in Conrad's notes (Proposition 4.3.1): over any scheme `S`,
every fppf central extension of `SL₂` by a commutative separated `S`-group splits, and
the splitting is unique. The Lean statement treats the case where the middle term of the
extension is a group scheme.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`. It then sets
  `SL₂ := (GroupScheme.baseChange (Gm.toSpecZ S)).obj
  (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ)))`, the base change
  of `SL₂` over `Spec ℤ` along the unique morphism `Gm.toSpecZ S : S ⟶ Spec ℤ`. This is
  `SL_{2,S}`. Its points over an `S`-scheme `T` are the determinant-one `2 × 2` matrices
  with entries in `Γ(T, 𝒪_T)`;
- a commutative group scheme `Z` over `S` whose structure morphism is separated
  (`IsSeparated Z.toGrp.X.hom`);
- a group scheme `E` over `S` and homomorphisms `z : Z.toGrp ⟶ E` and `q : E ⟶ SL₂`.
  `E` is Conrad's `G′`.

It assumes:

1. `Mono z.hom.hom`: the underlying morphism of `z` is a monomorphism in `Over S`. This
   holds exactly when `z` is injective on `T`-points for every `S`-scheme `T`.
2. `IsCentral z`: for every `S`-scheme `T` and every `x ∈ Z(T)`, the point `x ≫ z` lies in
   `(center E).carrier T`. That is, for every `a : T' ⟶ T` its restriction to `T'`
   commutes with every point of `E(T')`.
3. Exactness at `E`: for every `S`-scheme `T : Over S` and every point `x : T ⟶ E.X`,
   `x ≫ q.hom.hom = 1` holds exactly when `x ∈ (SubgroupFunctor.range z).carrier T`.
   Here `1 : T ⟶ SL₂.X` is the identity point, the unit of the group structure on
   `T ⟶ SL₂.X` from `open scoped CategoryTheory.MonObj`. `(SubgroupFunctor.range z).carrier T`
   is the set of points `y ≫ z.hom.hom` with `y : T ⟶ Z.toGrp.X`.
4. Surjectivity as fppf sheaves: for every `S`-scheme `T` and every point `y : T ⟶ SL₂.X`
   there is an fppf cover `𝒰` of `T.left` such that each restriction of `y` to a member
   of `𝒰` lifts along `q`. In Lean, `𝒰` is a
   `Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left`:
   a family of flat, locally finitely presented morphisms `𝒰.f i : 𝒰.X i ⟶ T.left` whose
   images cover `T.left`, indexed by a type in universe `u`. Each `𝒰.X i` is an
   `S`-scheme through `𝒰.f i ≫ T.hom`. For every `i` there is
   `x : Over.mk (𝒰.f i ≫ T.hom) ⟶ E.X` with
   `x ≫ q.hom.hom = Over.homMk (𝒰.f i) rfl ≫ y`.

## Conclusion

The conclusion is `∃! s : SL₂ ⟶ E, s ≫ q = 𝟙 SL₂`: there is exactly one homomorphism of
group schemes `s : SL₂ ⟶ E` that is a section of `q`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 4.3.1 (Gabber), p.126: "Let S be a scheme, and Z a commutative separated
  S-group. Any fppf central extension of group sheaves 1 → Z → G′ → SL₂ → 1 is uniquely
  split as a central extension. (In particular, G′ is an S-scheme.)"
- The paragraph after it, p.126: "We only need the case that G′ is an S-affine S-group of
  finite presentation (possibly not smooth!) with Z of multiplicative type."
- The proof, pp.126–131. It begins with uniqueness, p.126: "We first address the
  uniqueness of the splitting, which is to say (due to the centrality of Z in G′) the
  vanishing of any S-homomorphism G = SL₂ → Z."
- p.126, end of §4.2: "This completes the proof of Theorem 4.2.6 conditional on the
  (unique) splitting of central extensions of SL₂, provided by Proposition 4.3.1 below."

## Derivation from the source

- **`G′` is a group scheme.** Conrad allows `G′` to be any fppf group sheaf and deduces
  that it is representable. The Lean statement assumes that `G′ = E` is a group scheme
  over `S`, so it is the special case of Proposition 4.3.1 where `G′` is already a scheme.
  It does not state the parenthetical representability claim. The case Conrad says he
  needs, `G′` affine of finite presentation over `S` with `Z` of multiplicative type, is
  covered: no affineness, finiteness or smoothness hypothesis on `E` is imposed.
- **Exactness as fppf sheaves.** `Z`, `E` and `SL₂` are schemes, so their functors of
  points are sheaves for the fppf topology. For morphisms of sheaves, injectivity and the
  kernel are computed on points over each `T`, and surjectivity means that every point
  lifts locally on a cover. So exactness of `1 → Z → G′ → SL₂ → 1` as fppf sheaves is
  hypotheses 1, 3 and 4 together.
- **`q` need not be flat.** Hypothesis 4 is surjectivity of fppf sheaves, not flatness of
  `q`. When `Z` is not flat over `S`, `q` need not be flat, so the Library's
  `RelativeRoot.IsFppfQuotient`, which requires `q` to be flat, surjective and locally of
  finite presentation, would be a stronger hypothesis than Conrad's.
- **Splitting.** A splitting of the central extension is a homomorphism `s : SL₂ → G′`
  with `q ∘ s = id`. Since `Z` is central, `(z, s) : Z × SL₂ → G′` is then an isomorphism
  of central extensions. Conrad's "uniquely split" is the uniqueness of `s`, as his
  proof begins: by centrality, two sections differ by a homomorphism `SL₂ → Z`, and the
  proof shows that such a homomorphism is trivial. The conclusion `∃!` states existence
  and uniqueness of `s`.

## Scope

All schemes are in universe `u`. The proposition does not state:

- Proposition 4.3.1 for a central extension whose middle term is only an fppf group
  sheaf, or its representability consequence;
- Lemma 4.3.2 (equivariant splittings over the root groups), or any other step of the
  proof;
- Proposition 4.3.4, the `SL₂` variant of Proposition 4.2.7.

## Relation to the Library

- `CentralTorusExtensionStatement` in
  [`Torus.CentralExtensionStatement`](Torus/CentralExtensionStatement.md) concerns a
  central extension of a torus by a torus over a field. It encodes the extension with
  `RelativeRoot.IsFppfQuotient`, which requires the quotient map to be flat.
- `SplitRankOneRootCellStatement` in
  [`Reductive.SplitRankOneRootCellStatement`](Reductive/SplitRankOneRootCellStatement.md)
  states parts of Conrad's Theorem 4.2.6 for connected reductive groups of semisimple
  rank at most one over a field. Conrad's proof of that theorem uses Proposition 4.3.1.

This module proves none of these relations.
