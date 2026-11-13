# Statement: the Isomorphism Theorem for split reductive groups over an affine base

Worker 75.

`Langlands.GroupScheme.AffineSplitIsomorphismTheoremStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) (for `IsFibrewiseRootDatumOf`
and, through it, `splitTorus`, `splitTorus.pointsEquiv` and
`splitTorus.exponentWeightSpace`), [`Reductive.Basic`](Basic.md) (for `IsReductive` and
`IsClosedSubgroup`) and [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)
(for `IsFibrewiseMaximalTorus`).

It states, over an affine base `Spec R`, the existence half of the "in particular" clause
of Conrad's Isomorphism Theorem: every isomorphism of root data between two split
reductive groups comes from an isomorphism of the groups that is compatible with the
splittings.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`, with base scheme `Spec R`. The ring may be zero,
  non-Noetherian, non-local, and `Spec R` may be disconnected;
- group schemes `G H : GroupScheme (Spec R)` with `hG : IsReductive G` and
  `hH : IsReductive H` ([`Reductive.Basic`](Basic.md)): each is smooth and affine over
  `Spec R`, and its geometric fibres are connected reductive groups. The statement takes
  the instances `IsAffineHom G.X.hom` and `IsAffineHom H.X.hom` from `hG.isAffineHom`
  and `hH.isAffineHom` by `haveI`, so it adds no instance argument;
- finite types `I I' : Type u` and homomorphisms `i : splitTorus (Spec R) I ⟶ G` and
  `i' : splitTorus (Spec R) I' ⟶ H` from the coordinate split tori `𝔾_m^I` and
  `𝔾_m^{I'}` over `Spec R`;
- types `J J' : Type u` and Mathlib root data `P : RootDatum J (I → ℤ) (I → ℤ)` and
  `Q : RootDatum J' (I' → ℤ) (I' → ℤ)` on the coordinate character and cocharacter
  lattices.

It has four hypotheses on `(G, i, P)` and the same four on `(H, i', Q)`. Together they say
that `(G, i, P)` and `(H, i', Q)` are split. They are the hypotheses of the Library's
encoding of Conrad's Definition 5.1.1, used in
[`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) and in
[`RelativeLevi.SplitBorelConjugacyStatement`](../RelativeLevi/SplitBorelConjugacyStatement.md):

1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
2. `IsFibrewiseMaximalTorus i`: for every point `s` of `Spec R`, the residue fibre of `i`
   over `κ(s)` satisfies the field predicate `IsMaximalTorus`.
3. `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and for every field
   `k` with a ring homomorphism `R → k`, the realization of `P` over `k` is the root datum
   (`IsRootDatumOf`) of the base change of `i` to `k`. The realization
   (`CoordinateRootDatum.fieldRealization`) transports `P` along
   `splitTorus.characterLatticeEquiv` and `splitTorus.cocharacterLatticeEquiv`, under
   which `m : I → ℤ` is the character `t ↦ ∏ⱼ tⱼ ^ mⱼ` and `n : I → ℤ` is the
   cocharacter `s ↦ (s ^ nⱼ)ⱼ`. So the roots and coroots of every field-valued fibre are
   the constant elements of `P`.
4. For every `α : J`, the weight space `splitTorus.exponentWeightSpace I G i (P.root α)`
   is isomorphic to `R` as an `R`-module, that is, free of rank one. This weight space is
   the `R`-submodule of the Lie algebra `lieKernel G R` of vectors `X` such that, over
   every `R`-algebra `A` and for every point `t ∈ (Aˣ)^I` of the torus, the adjoint
   action of `i(t)` multiplies the image of `X` by `∏ⱼ tⱼ ^ (P.root α)ⱼ`.

The last quantifier is an equivalence of root pairings `f : RootPairing.Equiv Q P`
(Mathlib, `LinearAlgebra/RootSystem/Hom`). Its weight map
`f.weightMap : (I' → ℤ) → (I → ℤ)` is a linear bijection from the character lattice of
`𝔾_m^{I'}` to that of `𝔾_m^I`; its coweight map `f.coweightMap : (I → ℤ) → (I' → ℤ)` is
a linear bijection with the transpose property `weight_coweight_transpose`; and its index
bijection `f.indexEquiv : J' ≃ J` satisfies
`f.weightMap (Q.root j') = P.root (f.indexEquiv j')` (`root_weightMap`) and
`f.coweightMap (P.coroot j) = Q.coroot (f.indexEquiv.symm j)` (`coroot_coweightMap`).
This is the direction convention of the field-level
[`Reductive.SplitIsomorphismTheoremStatement`](SplitIsomorphismTheoremStatement.md):
the weight map goes from the characters of the target torus to those of the source
torus.

## Conclusion

There are an isomorphism `φ : G ≅ H` of group schemes over `Spec R` and an isomorphism
`τ : splitTorus (Spec R) I ≅ splitTorus (Spec R) I'` of group schemes such that

- `i ≫ φ.hom = τ.hom ≫ i'`: `φ` maps the torus of `G` onto the torus of `H`, and its
  restriction to the tori is `τ`;
- for every test scheme `U` over `Spec R`, every point `x : U ⟶ 𝔾_m^I` and every
  `m : I' → ℤ`,
  `∏ j', (pointsEquiv I' U (x ≫ τ.hom.hom.hom))_{j'} ^ m j' = ∏ j, (pointsEquiv I U x)_j ^ (f.weightMap m) j`.
  Here `τ.hom.hom.hom` is the underlying morphism of `τ.hom` in `Over (Spec R)`, so
  `x ≫ τ.hom.hom.hom` is the point `τ(x)` of `𝔾_m^{I'}`, and
  `splitTorus.pointsEquiv I U` identifies the `U`-points of `𝔾_m^I` with families
  in `(Γ(U, 𝒪_U)ˣ)^I`. The left side is the character `χ_m : t ↦ ∏ t_{j'} ^ m_{j'}` of
  `𝔾_m^{I'}` evaluated at `τ(x)`; the right side is the character `χ_{f m}` of `𝔾_m^I`
  evaluated at `x`. Since the identity holds for every `U` and `x`, it says that
  `χ_m ∘ τ = χ_{f.weightMap m}` as morphisms of schemes `𝔾_m^I → 𝔾_m` (Yoneda). So the
  map on character lattices induced by `τ` is the constant map `f.weightMap`.

The conclusion constrains only the weight map of `f`. The other two components are
determined by it: the index bijection because `P.root` is injective, and the coweight map
by the transpose property, because the pairing of `Q` is perfect.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Theorem 6.1.17 (Isomorphism Theorem), p.197: "Let S be a scheme that is non-empty. The
  functor (6.1.2) (G, T, M, {X_a}_{a∈∆}) ↝ (R(G, T, M), ∆) from pinned split reductive
  S-groups to based root data is an equivalence of categories when using isomorphisms as
  morphisms. In particular, every split reductive S-group (G, T, M) is uniquely
  determined up to isomorphism by its root datum, and every isomorphism of root data
  R(G′, T′, M′) ≃ R(G, T, M) arises from an isomorphism f : (G′, T′, M′) ≃ (G, T, M)
  compatible with the splittings, with f uniquely determined up to the faithful action of
  (T/Z_G)(S) on G."
- Theorem 6.1.16(1) (Isogeny Theorem), p.196, and Corollary 6.1.15, p.195, from which the
  source derives Theorem 6.1.17 ("An immediate consequence of Theorem 6.1.16 and the
  arguments with the ℤ-basis ∆ of X(T/Z_G) in the proof of Corollary 6.1.15", p.197).
- Definition 5.1.1, p.136: "Let G be a reductive group over a non-empty scheme S. It is
  split if there exists a maximal torus T equipped with an isomorphism T ≃ D_S(M) for a
  finite free Z-module M such that: 1. the nontrivial weights a : T → G_m that occur on 𝔤
  arise from elements of M …, 2. each root space 𝔤_a is free of rank 1 over O_S, 3. each
  coroot a∨ : G_m → T arises from an element of the dual lattice M∨ …"
- Definition 6.1.6, p.190: a quasi-finite surjection f : (G′, T′) → (G, T) of split
  reductive groups "is compatible with the splittings if there is a homomorphism
  h : M → M′, bijection d : Φ′ → Φ, and function q : Φ′ → Z_{≥1} valued in prime powers
  such that: 1. the induced map X(f) : M_S = X(T) → X(T′) = M′_S arises from h, 2. for all
  a′ ∈ Φ′, h(d(a′)) = q(a′)a′ and h∨(a′∨) = q(a′)d(a′)∨, 3. …". The text after it notes
  that f determines h, d and q.
- Definition 6.1.8, p.191: a p-morphism R′ → R of reduced root data is a triple (h, d, q)
  with h : X → X′, a bijection d : Φ′ → Φ and q : Φ′ → {pⁿ}, such that h_ℚ is an
  isomorphism, h(d(a′)) = q(a′)a′ and h∨(a′∨) = q(a′)d(a′)∨; "a p-morphism that is an
  isomorphism must be a 1-morphism", and the map h goes in the "other" direction.
- Definition 3.2.1, p.91, and Remark A.1.2, p.267, resting on Grothendieck's
  Theorem A.1.1: a torus that is maximal on residue fibres is a maximal torus in Conrad's
  (geometric) sense, as in
  [`Reductive.LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md).

## Derivation from the source

The proposition is the existence part of the "in particular" clause of Theorem 6.1.17
over a non-empty affine base, with `(G′, T′, M′) = (G, i, ℤ^I)` and
`(G, T, M) = (H, i', ℤ^{I'})` in Conrad's notation. Its terms translate as follows.

- **Split reductive groups.** Conrad's `T ≃ D_S(M)` with `M = ℤ^I` is the split torus
  `splitTorus (Spec R) I` with its coordinates; any finite free `M` has this form after
  choosing a basis. Hypotheses 1–4 transcribe Definition 5.1.1 as in
  [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) (Lemma 5.1.3):
  a closed subgroup that is a maximal torus on residue fibres (hence a maximal torus by
  Remark A.1.2), with roots and coroots given on every fibre by the constant root datum
  `P` (conditions 1 and 3), and with root spaces free of rank one over `R`
  (condition 2). The root datum `R(G, T, M) = (M, Φ, M∨, Φ∨)` of the split group is then
  `P` up to reindexing roots by `J`, since `P.root` is injective; `P` is reduced, as
  Definition 6.1.8 requires.
- **Isomorphism of root data.** An isomorphism `R(G′, T′, M′) ≃ R(G, T, M)` is a
  1-morphism `(h, d, 1)` with `h : M → M′` bijective, `d : Φ′ → Φ` a bijection,
  `h(d(a′)) = a′` and `h∨(a′∨) = d(a′)∨`. An equivalence `f : RootPairing.Equiv Q P`
  gives exactly this, with `h = f.weightMap : ℤ^{I'} → ℤ^I`, `d` read through
  `P.root` and `Q.root` from `f.indexEquiv.symm : J ≃ J'`, `h(d(a′)) = a′` from
  `root_weightMap`, and `h∨ = f.coweightMap` (transpose property) with
  `h∨(a′∨) = d(a′)∨` from `coroot_coweightMap`. Conversely, such a triple `(h, d, 1)`
  yields an equivalence: its coweight map is the transpose of `h`, which is bijective
  because the pairings are perfect.
- **"Arises from an isomorphism f compatible with the splittings".** An isomorphism of
  pairs `(G′, T′) ≃ (G, T)` is an isomorphism `φ : G ≅ H` carrying `T′` onto `T`, which
  is `i ≫ φ.hom = τ.hom ≫ i'` with an isomorphism of tori `τ`. Compatibility with the
  splittings (Definition 6.1.6(1)) says that `X(φ|T′)`, which sends a character `χ` of
  `𝔾_m^{I'}` to `χ ∘ τ`, is the constant map `h`; this is the identity of points in the
  conclusion. Since `h` determines `d` and `q = 1`, the triple `R(φ)` is then the given
  isomorphism `(h, d, 1)`, which is what "arises from" means.
- **Affine base.** The free root-space hypothesis uses `splitTorus.exponentWeightSpace`,
  which the Library defines only over an affine base `Spec R`. Conrad's theorem allows any
  non-empty scheme `S`. The statement over a general `S` is not a formal consequence of
  this one: isomorphisms chosen over the members of an affine open cover need not glue,
  and gluing would use the uniqueness clause. So this proposition is a specialization of
  the source's statement to affine bases, not a reformulation of it.
- **Empty base.** Non-emptiness of `S` is not assumed. For `R = 0` the proposition holds
  trivially: every scheme over the empty scheme `Spec 0` is empty, so all objects of
  `GroupScheme (Spec 0)` are uniquely isomorphic, the equation `i ≫ φ.hom = τ.hom ≫ i'`
  holds, and the identity of points is an identity in the trivial group of units of
  the zero ring.
- **Free root spaces.** Over a base with non-trivial Picard group, root spaces need not
  be free: for a line bundle `L`, the diagonal torus of `GL(𝒪 ⊕ L)` has root spaces `L`
  and `L⁻¹` (up to the sign convention). This is why condition 2 of Definition 5.1.1 is
  imposed as hypothesis 4.

## Scope

All objects are in universe `u`. The proposition does not state:

- the uniqueness of `φ` up to the action of `(T/Z_G)(S)`;
- the first sentence of Theorem 6.1.17, the equivalence between pinned split reductive
  groups and based root data; pinnings do not occur;
- the first part of the "in particular" clause in its own right (it is the special case
  in which `φ` is only required to exist), the converse direction (an isomorphism of
  split groups induces an isomorphism of root data), or the Isogeny Theorem 6.1.16(1).

## Relation to the Library

- [`Reductive.SplitIsomorphismTheoremStatement`](SplitIsomorphismTheoremStatement.md)
  records the same existence assertion over a field (Milne, Remark 23.26), with arbitrary
  split maximal tori and their actual character lattices. Over a field the present
  hypotheses 1–4 describe split maximal tori with their root data, but the two
  propositions are stated on different lattices; this module does not prove either from
  the other.
- [`Reductive.LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md)
  records an isomorphism theorem over local rings for coordinate split tori, without the
  free root-space hypothesis (root spaces are free over a local ring) and with the
  conclusion `Nonempty (G ≅ H)` only.
- [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) states Lemma 5.1.3,
  that reductive groups become split in this encoding étale-locally on the base.

This module proves none of these relations.
