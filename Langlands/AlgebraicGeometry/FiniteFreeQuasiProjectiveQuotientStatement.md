# Quotients of quasi-projective schemes over a field by free finite group actions

The module
`Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement`
defines one proposition in namespace `Langlands.AlgebraicGeometry`:

- `FiniteFreeQuasiProjectiveQuotientStatement`.

It states that a free action of a finite group on a quasi-projective scheme
over a field has a quotient which is again quasi-projective over the field, and
that the quotient map is a finite étale Galois covering with the given group.
The module supplies no proof.

## The statement

The proposition quantifies over

- a field `K : Type` and a scheme `X : Scheme.{0}` with a morphism
  `s : X ⟶ Spec K`;
- a natural number `N` and a morphism `j : X ⟶ ProjectiveSpace K N` with
  `IsImmersion j` and `j ≫ projectiveSpaceToSpec K N = s`;
- a finite group `G : Type` and an action `A : FiniteFreeSchemeAction G X`
  such that `(A.act g).hom ≫ s = s` for every `g : G`.

`ProjectiveSpace K N` is the Library's `Proj` of the polynomial ring in
`N + 1` variables with its total-degree grading, and `projectiveSpaceToSpec`
is its structure morphism (module `Langlands.AlgebraicGeometry.ProjectiveSpace`).
The hypotheses on `j` say that `X` is quasi-projective over `K`: it is
isomorphic, over `K`, to a locally closed subscheme of a projective space.

`FiniteFreeSchemeAction G X` is the Library structure of module
`Langlands.AlgebraicGeometry.FiniteFreeSchemeActionRelation`. It consists of
isomorphisms `act g : X ≅ X` with `act 1 = 𝟙` and
`act g ≫ act h = act (g * h)` (a right action, written in the order of
composition of morphisms), and it requires freeness on points valued in every
nonempty scheme: for a nonempty scheme `T` and `a : T ⟶ X`, the map
`g ↦ a ≫ (act g).hom` is injective. For an action by automorphisms this is
equivalent to the triviality of the stabilizer of every geometric point
`Spec Ω ⟶ X`, `Ω` algebraically closed, since every nonempty scheme has such a
point. Hence it is the condition that the inertia groups of all points are
trivial.

The conclusion is the existence of

- `Q : A.EffectiveQuotient`, the Library structure of module
  `Langlands.AlgebraicGeometry.FiniteFreeQuasiAffineQuotient`: a scheme
  `Q.scheme` and a morphism `Q.map : X ⟶ Q.scheme` with
  `A.target ≫ Q.map = A.source ≫ Q.map`, which is finite, étale and
  surjective, such that the square formed by `A.target`, `A.source` and two
  copies of `Q.map` is a pullback square (the disjoint union
  `∐_{g : G} X` of the graphs of the action is the kernel pair of `Q.map`),
  and such that `Q.map` is the coequalizer of `A.source` and `A.target`;
- a morphism `t : Q.scheme ⟶ Spec K` with `Q.map ≫ t = s`;
- a natural number `M` and a morphism `j' : Q.scheme ⟶ ProjectiveSpace K M`
  with `IsImmersion j'` and `j' ≫ projectiveSpaceToSpec K M = t`.

`A.source` and `A.target` are the morphisms `∐_{g : G} X ⟶ X` whose
restrictions to the summand `g` are `𝟙 X` and `(A.act g).hom`. So the
pullback condition says that `X ×_{X/G} X` is the disjoint union of the graphs
of the action maps: `X ⟶ X/G` is a principal covering with group `G`.

The statement is in universe `0`, the universe of the schemes over number
fields to which the Library applies it.

## Sources

- David Mumford, *Abelian Varieties*, Tata Institute Studies in Mathematics 5,
  Oxford University Press (1970), source `mumford-abelian-varieties-full-scan`,
  SHA-256 `9541a2e454c78920d4a41b4a78cac36544cd83e99bd1a221e55f25e3f247dcc3`,
  Chapter II, §7. The Theorem on printed p.66 (scan page 38) constructs the
  quotient `X/G` of a variety by a finite group of automorphisms whose orbits
  lie in affine open subsets, with `π : X ⟶ X/G` finite and surjective, and
  proves that `π` is étale when `G` acts freely. The Remark on printed p.69
  (scan page 39) shows that every finite set of points of a quasi-projective
  `X` lies in an affine open subset.
- A. Grothendieck et al., *Revêtements étales et groupe fondamental (SGA 1)*,
  recomposed edition arXiv math/0206203v2, source `sga1-arxiv-math-0206203v2`,
  SHA-256 `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`,
  Exposé V. Proposition 1.8 (printed p.90, PDF p.106) gives the existence of
  `X/G` for actions whose orbits lie in affine opens; Corollaire 2.3 (printed
  p.93, PDF p.109) gives étaleness of `X ⟶ X/G` when all inertia groups are
  trivial; Proposition 2.6 (printed p.95, PDF p.111) shows that `X` is then a
  principal covering of `X/G` with group `G`, that is,
  `X ×_{X/G} X ≅ X × G` through the graphs of the action. SGA 1 uses right
  actions, `T_{gg'} = T_{g'} T_g`, the convention of
  `FiniteFreeSchemeAction`.
- Quasi-projectivity of the quotient is the theorem
  `AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj`
  of the Anthropic Lean formalization of Fermat's Last Theorem, source
  `anthropic-flt-complete-lean-source-6e837e75`, directory SHA-256
  `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, file
  `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj.lean`.
  For a finite group acting on a scheme over `Spec B` with an immersion into
  `Proj` of a polynomial ring over `B`, and for a quotient map that is
  integral, affine and surjective, whose fibres are the orbits, whose rings of
  sections are the invariants and along which invariant affine opens descend,
  it gives an immersion of the quotient into `Proj` of a polynomial ring over
  `B`, when the quotient is separated, quasi-compact and locally of finite
  presentation over `B`.

The statement combines these: under the hypotheses, the quotient exists, the
quotient map is finite étale and makes `X` a principal covering of the
quotient with group `G`, and the quotient is quasi-projective over `K`. It is
used by `Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientReduction`.
