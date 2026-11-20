# Sections of trigonalizable groups with smooth unipotent part

`Langlands.GroupScheme.TrigonalizableSectionConjugacySmoothStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## What this statement replaces

This statement replaces
`Langlands.GroupScheme.TrigonalizableSectionConjugacyStatement` (module
[`Trigonalizable.SectionConjugacyStatement`](SectionConjugacyStatement.md)).
That statement formalizes Milne's Theorem 16.27 as printed, and it is false
over every algebraically closed field of characteristic `p > 0`. Milne's
Theorem 16.27 and the maximal-subgroup sentence of his Summary 16.29 are
false as printed for the same reason: they lack a smoothness hypothesis.

The only change from the old statement is one hypothesis,
`Smooth U.X.hom`. It is an explicit binder of the definition, placed after
`IsClosedSubgroup i`. The rest of the body of the definition is the same
as in the old statement. The old
proposition stays in the Library unproved, with its Lean text unchanged. It
must not be used as a proof target or as a premise. This follows the
operator's answer to request `5639a3e0824c51b4b974ae79c240f1bf` (correspondence
file `768b729328a35053acbdf5882ff2f104.md`) and standing ruling 8.

The counterexamples are written out in the public note
[Milne 16.27 and 16.29: sections of trigonalizable groups need smoothness](../../../notes/errata/milne-2017-trigonalizable-section-conjugacy.md),
§§2–4. In summary, let `k` be algebraically closed of characteristic
`p > 0` and let a closed subgroup `H` of `G_m` act on `G_a` by
multiplication, `t · x = tx`. This action preserves `α_p`, and the
semidirect product `α_p ⋊ H` has the group law
`(x₁, t₁)(x₂, t₂) = (x₁ + t₁x₂, t₁t₂)`. Take `U = α_p` and let `q` be the
projection to `H`. All hypotheses of the old statement hold.

- **Part (a) fails for `α_p ⋊ μ_p`,** with `D = μ_p = D(ℤ/p)`. This is
  Raynaud's example, SGA 3 XVII 5.9 d). For each `c ∈ k`,
  `s_c(t) = (c(1 − t), t)` is a homomorphic section of `q`. It is
  multiplicative because `c(1 − t₁) + t₁c(1 − t₂) = c(1 − t₁t₂)`. It lands in
  `α_p` because `(c(1 − t))^p = c^p(1 − t^p) = 0` on `μ_p`. Since
  `U(k) = α_p(k) = {0}`, part (a) would force `s_c = s_0`, which fails for
  `c ≠ 0`. The two sections are not conjugate even after a base change. If
  `u ∈ α_p(R)` conjugates `s_0` to `s_c`, then `(u − c)(1 − t) = 0` in
  `R[t]/(t^p − 1)`, so `u = c`, and `c^p = 0` forces `R = 0`.
- **Part (b) fails for `α_p ⋊ G_m`,** with `D = G_m = D(ℤ)`, which is
  smooth. Fix `c ≠ 0`. Then `S = {(c(1 − t), t) : t ∈ μ_p} ≅ μ_p` is a
  closed diagonalizable subgroup. Every crossed homomorphism from `μ_n`
  (`n ≥ 2`) or from `G_m` to `G_a` has the form `a(1 − t)`. It lands in `α_p`
  only if `a = 0` or `n ∣ p` (Lemma A of the note). A diagonalizable
  subgroup meets `α_p` trivially (Lemma B). So a closed diagonalizable
  subgroup containing `S` is the graph of a crossed homomorphism extending
  `c(1 − t)`, and it equals `S`: `S` is maximal. But the only section of `q`
  is `t ↦ (0, t)`, whose image is not `S`.

In both examples `U = α_p` is not smooth. With `U` smooth, both parts hold,
as explained under "Sources of record".

## Statement

Let `k : Type u` be an algebraically closed field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `U` be a
group scheme over `Spec k` with a homomorphism `i : U ⟶ G`, let
`Λ : Type u` satisfy `[AddCommGroup Λ]` and `[AddGroup.FG Λ]`, write
`D(Λ)` for `(Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`, and let
`q : G ⟶ D(Λ)` be a homomorphism. Assume `IsClosedSubgroup i`,
`Smooth U.X.hom`, `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal` and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

Write `IsDiag S` for: there are `Λ' : Type u` with `[AddCommGroup Λ']` and
`AddGroup.FG Λ'` and an isomorphism of group schemes
`S ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp`. The
conclusion is the conjunction of two parts.

1. **(a) Sections are conjugate.** For all homomorphisms
   `s₁ s₂ : D(Λ) ⟶ G` with `s₁ ≫ q = 𝟙` and `s₂ ≫ q = 𝟙`, there is a point
   `u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X` (a `k`-rational point
   of `U`) such that `s₂ = s₁ ≫ (G.innerIso (u ≫ i.hom.hom)).hom`.
2. **(b) Maximal diagonalizable subgroups.** For every group scheme `S` over
   `Spec k` and every homomorphism `j : S ⟶ G` with `IsClosedSubgroup j` and
   `IsDiag S`, the following are equivalent:
   - for every `j' : S' ⟶ G` with `IsClosedSubgroup j'` and `IsDiag S'`,
     `SubgroupFunctor.range j ≤ SubgroupFunctor.range j'` implies
     `SubgroupFunctor.range j = SubgroupFunctor.range j'`;
   - there is a homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙` and
     `SubgroupFunctor.range j = SubgroupFunctor.range s`.

The ingredients are existing declarations, used without change.

- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `Smooth U.X.hom` (Mathlib, `AlgebraicGeometry.Smooth`) says that the
  structure morphism `U → Spec k` is smooth. For an algebraic group over a
  field this is Milne's "smooth algebraic group", that is, a group variety
  (Milne p.13).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over `Spec k`. `IsNormal` says that, on every test scheme,
  these points form a normal subgroup of the points of `G`. The order `≤` is
  inclusion of these subgroups on every test scheme.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `Diagonalizable.groupScheme (CommRingCat.of k) Λ` (from
  [`Torus.Diagonalizable`](../Torus/Diagonalizable.md)) is the
  diagonalizable group `D(Λ) = Spec k[Λ]` over `Spec k`.
- `G.innerIso g` (from [`InnerAutomorphism`](../InnerAutomorphism.md)) is the
  group-scheme automorphism of `G` given on points over every test scheme by
  conjugation `x ↦ g x g⁻¹` with the pulled-back point `g`, for a point `g`
  of `G` over the base.
- `IsAlgClosed k` and `AddGroup.FG Λ` (`Λ` is finitely generated) are from
  Mathlib.

## Sources of record

**Part (a)** is SGA 3, Exp. XVII (Raynaud), Théorème 5.1.1 ii) b). This
theorem, not Milne 16.27, is the source of record for (a). For an extension
`1 → U → E → H → 1` of a group `H` of multiplicative type by a unipotent
algebraic group `U`, it says that two liftings of `H` in `E` are conjugate
by an element of `U(k)` when `k` is algebraically closed and `U` is smooth.
A lifting (relèvement) of `H` is a subgroup that the quotient map sends
isomorphically onto `H`. Liftings and sections determine each other: a
section is determined by its image, on which `q` is its inverse.
Conjugating a lifting by `u` conjugates the corresponding section by `u`.
So, for `E = G` and `H = D(Λ)`, 5.1.1 ii) b) is part (a).

**Part (b)** follows from (a) and from the existence of a section by
Milne's argument in the proof of 16.27(b), printed p.333. A diagonalizable
subgroup `S` meets `G_u` trivially (Milne 14.17), so `q` maps `S`
isomorphically onto `q(S)`. Let `s` be a section of `q`, which exists by
Milne 16.26(a) (SGA 3 XVII 5.1.1 i) a)). Put `G' = q⁻¹(q(S))`. It is an
extension of `q(S)` by the same smooth `U`. Both the restriction of `s` and
the inverse of `q` on `S` are sections of `G' → q(S)`. Part (a) for `G'`
gives `u ∈ U(k)` with `S = inn(u)(s(q(S))) ⊆ inn(u)(s(D))`, and
`inn(u) ∘ s` is again a section. So every diagonalizable subgroup lies in
the image of a section. Conversely, if `S'` is diagonalizable and contains
`s(D)`, then for a point `x` of `S'` the point `x · s(q(x))⁻¹` lies in
`S' ∩ G_u`, which is trivial. Hence images of sections are exactly the
maximal diagonalizable subgroups. At the conjugacy step Milne cites
"Theorem 16.26", but the step uses part (a) for `G'`. This is why (b) needs
the same hypothesis as (a): `G'` has the same unipotent part `U`.

## What this statement leaves out

- **Smoothness of `U` is sufficient, not necessary, for (a).** By SGA 3
  XVII 5.1.1 ii) a), part (a) also holds when `k` is algebraically closed
  and the diagonalizable quotient `D(Λ)` is smooth, with `U` arbitrary.
  That case, with smoothness of `D(Λ)` in place of `Smooth U.X.hom`, is
  neither stated nor proved here. Nobody should read this statement as
  saying that smoothness of `U` is needed for (a).
- **Part (b) with `D(Λ)` smooth and `U` not smooth is false.** This is the
  second counterexample above. So, unlike (a), part (b) cannot trade the
  smoothness of `U` for the smoothness of `D(Λ)`.
- **The conjugacy clause of 16.27(b)** (any two maximal diagonalizable
  subgroups are conjugate by an element of `G_u(k)`) is not stated
  separately. It follows from (a) and (b), since
  `range (s₁ ≫ inn(u))` is the image of `range s₁` under `inn(u)`.
- **Other fields.** Nothing is stated over fields that are not
  algebraically closed.
- **Characteristic `0`.** There every algebraic group is smooth (Milne
  p.13), so the hypothesis holds automatically and the statement is Milne's
  16.27. The proposition still quantifies over all algebraically closed
  fields, with the explicit hypothesis.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.27, p.333: "Let G be a trigonalizable algebraic group over an
  algebraically closed field k, and let q: G → D be the quotient of G by
  G_u. (a) Let s1, s2: D → G be sections of q (as a homomorphism of algebraic
  groups). Then there exists a u ∈ G_u(k) such that s2 = inn(u) ∘ s1.
  (b) The maximal diagonalizable subgroups of G are those of the form s(D)
  with s a section of q; any two are conjugate by an element of G_u(k)."
  The proof of (b), p.333: "Let s be a section of q: G → D and let S be a
  diagonalizable subgroup of G. Then S ∩ G_u = e (see 14.17), and so q
  induces an isomorphism of S onto q(S). [...] As S gives a section of q′,
  there exists by Theorem 16.26 a u ∈ G_u(k) such that
  S = inn(u)s′q(S). We deduce that S ⊂ inn(u)s(D)."
- Corollary 14.17, p.284: "The intersection of a unipotent algebraic
  subgroup of an algebraic group with an algebraic subgroup of
  multiplicative type is trivial."
- Theorem 16.26, p.332: the extension `e → G_u → G → D → e` splits when, in
  case (a), "the field k is algebraically closed".
- Summary 16.29, p.334, assumes "D a smooth group of multiplicative type".
  In its case (b), "k is algebraically closed", it asserts that "the
  maximal subgroups of multiplicative type in G are those of the form s(D)
  with s a section of q". The second counterexample contradicts this.
- Proposition 16.2, pp.324–325: "The following conditions on an algebraic
  group G are equivalent: (a) G is trigonalizable; ... (d) there exists a
  normal unipotent algebraic subgroup U of G such that G/U is
  diagonalizable."
- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." Notation 16.7, p.326:
  "When G is an algebraic group, we use G_u exclusively to denote a normal
  algebraic subgroup such that G_u is unipotent and G/G_u is of
  multiplicative type."
- Theorem 12.8, p.233: "An algebraic group G is diagonalizable if and only if
  it is isomorphic to D(M) for some commutative group M."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 1.61, p.24: "A sequence of algebraic groups e → N → G → Q (3)
  is exact if i is an isomorphism of N onto the kernel of q. A sequence
  e → N → G → Q → e (4) is exact if in addition q is faithfully flat."
- p.13: "Therefore “group variety” = “smooth algebraic group”. In
  characteristic zero, all algebraic groups are smooth (3.23, 8.39 below)."
- Theorem 16.33, pp.335–336, for "a smooth connected solvable algebraic
  group over a perfect field k": "(c) The subgroup G_u in (a) is smooth and
  connected, and G/G_u is a torus". This is cited only in the Provenance
  section.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`,
SHA256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`;
the one-based PDF page is the printed page plus 11) states Theorem 16.27 on
printed p.333 with the same words. Its proof continues on p.334.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(SHA256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`)
and `milne-2022-algebraic-groups-errata-2026-11-04` (SHA256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) were
checked. Neither records the defect: neither has an entry for printed
pp.332, 333 or 334. The 2017 errata have no entry for pp.13, 24, 135, 233,
284, 325, 326, 335 or 336. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern Proposition 16.2 or the affineness sentence. The 2022
errata have no entry for pp.24, 135, 233, 324, 325 or 326; their p.18 entry
concerns the proof of Proposition 1.37.

M. Raynaud, SGA 3 Exposé XVII, recomposed edition by P. Gille and P. Polo
(provisional version of November 2008), source ID
`sga3-expose-xvii-gille-polo-2008`, SHA256
`687f333c4f86221e7898f44c1706845d8e0b79af50ab31f3ed9a3b0f696ae25b`. Page
numbers are the printed pages of that edition. The one-based PDF page is
the printed page minus 324.

- Théorème 5.1.1, p.345: "Soient k un corps, U un k-groupe algébrique
  unipotent, H un k-groupe de type multiplicatif, E un k-groupe algébrique
  extension de H par U [...] Alors : i) L'extension E est triviale dans
  chacun des cas suivants : a) k est algébriquement clos. [...] ii) Si H′
  et H″ sont deux relèvements de H dans E, alors H′ et H″ sont conjugués
  par un élément de U(k) dans chacun des cas suivants : a) k est
  algébriquement clos et H est lisse. b) k est algébriquement clos et U est
  lisse."
- 5.9 d), p.358: "Voici un autre exemple, avec k algébriquement clos de
  caractéristique p > 0. Soit G le groupe radiciel produit semi-direct de
  µ_p par α_p, où µ_p opère sur α_p par « homothéties ». [...] on voit que
  H¹(µ_p, α_p) est non nul, donc deux relèvements de µ_p dans G ne sont pas
  nécessairement conjugués."

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Trigonalizable `G` and the quotient by `G_u`.** The hypotheses on `i`
  and `q` are condition (d) of Proposition 16.2, with the quotient `G/U`
  presented as `D(Λ)`: `U` is a normal unipotent algebraic subgroup (a
  closed subgroup), and `q` is a quotient map with kernel `U` onto a
  diagonalizable group, which by Theorem 12.8 may be taken to be `D(Λ)` with
  `Λ` finitely generated (as `G/U` is of finite type). By Proposition 16.2
  such a `G` is trigonalizable, and every trigonalizable `G` admits such `i`
  and `q`. Since a diagonalizable group is of multiplicative type, `U` is
  `G_u` (Notation 16.7, unique by Theorem 16.6) and `q` is the quotient of
  `G` by `G_u`. `IsFppfQuotient` expresses the quotient map: flat and
  surjective (faithfully flat, Definition 1.61), locally of finite
  presentation (automatic between schemes of finite type over a field), with
  kernel `U`. The statement does not mention trigonalizability itself. In
  SGA 3 terms, `G` is the extension `E` of `H = D(Λ)` by `U`; a diagonalizable
  group is of multiplicative type.
- **Smoothness of `U`.** This hypothesis is not in Milne's statement. It
  is the hypothesis of SGA 3 XVII 5.1.1 ii) b), and the section "What this
  statement replaces" shows that both parts fail without it.
- **(a).** A section of `q` as a homomorphism of algebraic groups is a
  group-scheme homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`. An element of
  `G_u(k)` is a `k`-rational point `u` of `U`, that is, a morphism over
  `Spec k` from `Spec k` itself to `U`. `inn(u)` is conjugation by the
  corresponding point `u ≫ i.hom.hom` of `G`, which is
  `(G.innerIso (u ≫ i.hom.hom)).hom`; `inn(u) ∘ s₁` is written
  `s₁ ≫ inn(u)` in diagrammatic order.
- **(b).** A diagonalizable subgroup is a closed subgroup `j : S ⟶ G`
  (Proposition 1.41, p.18: algebraic subgroups are closed) with `S`
  diagonalizable, that is (Theorem 12.8) `IsDiag S`. Maximality among
  diagonalizable subgroups is the displayed condition on ranges. "Of the
  form `s(D)`" means that the subgroup has the same points as the image of a
  section `s`, which is `range j = range s`.
- **Universes.** One universe `u` is used for the field, the character
  groups and the schemes. This is a formalization convention.

## Provenance

The Lean text of the old statement is reused with one added binder. The
correction, the counterexample to (b) and the scope list above are derived
for this Library. The counterexample to (a) is Raynaud's. Worker 386 found
the failure while executing Task 7806, the proof task for the old
statement. Worker 75, the author of the old statement, checked the
counterexample and staged the same corrected Lean statement, with the same
declaration name and module path, as candidate
`1884491c-56ab-4759-be7a-cdb829a06247`. The operator decided that Worker 386
publishes the corrected statement, so Worker 75 withdrew that candidate.
The Lean text here is the same as theirs.

Before the statement was fixed, the executors of Task 3483 (Worker 75 and
Worker 3483) were asked whether a planned use of 16.27 has a non-smooth
unipotent part. Such a use would need the case of SGA 3 XVII 5.1.1 ii) a)
described under "What this statement leaves out". Worker 75 reported that
no planned use needs it. No Library module imports the old statement. In
Library commit `86dbe494f42945f32e487976003611ce4579e721`, the modules that
cite Milne 16.27 or 16.29 in prose use them in one of two ways. Some use
them for smooth connected solvable groups over perfect fields, whose
unipotent part is smooth (Milne 16.33(c), pp.335–336: "The subgroup G_u in
(a) is smooth and connected"). The others use only the existence of a
splitting (16.26, and the splitting clause of 16.29(b)), which is not
affected.
