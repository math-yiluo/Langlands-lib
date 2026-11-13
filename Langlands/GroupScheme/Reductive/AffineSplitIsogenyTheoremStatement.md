# Statement: the Isogeny Theorem for split reductive groups over an affine base

Worker 75.

`Langlands.GroupScheme.AffineSplitIsogenyTheoremStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) (for `IsFibrewiseRootDatumOf`
and, through it, `splitTorus`, `splitTorus.pointsEquiv` and
`splitTorus.exponentWeightSpace`), [`Reductive.Basic`](Basic.md) (for `IsReductive` and
`IsClosedSubgroup`), [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)
(for `IsFibrewiseMaximalTorus`), [`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md)
(for `IsIsogeny`) and
[`LinearAlgebra.RootDatumIsogeny`](../../LinearAlgebra/RootDatumIsogeny.md) (for
`RootDatumIsogeny`).

It states, over an affine base `Spec R`, the existence part of Conrad's Isogeny Theorem:
every `p(S)`-morphism between the root data of two split reductive groups is induced by an
isogeny of the groups that is compatible with the splittings.

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
- types `J J' : Type u` with instances `[Finite J] [Finite J']`, and Mathlib root data
  `P : RootDatum J (I → ℤ) (I → ℤ)` and `Q : RootDatum J' (I' → ℤ) (I' → ℤ)` on the
  coordinate character and cocharacter lattices, with instances `[P.IsReduced]` and
  `[Q.IsReduced]`. The type `RootDatumIsogeny` below needs these four instances. They
  restrict nothing: hypothesis 3 below, `IsFibrewiseRootDatumOf`, contains finiteness of
  the index type and reducedness of the root datum as its first two conjuncts.

It has four hypotheses on `(G, i, P)` and the same four on `(H, i', Q)`. Together they say
that `(G, i, P)` and `(H, i', Q)` are split. They are the hypotheses of the Library's
encoding of Conrad's Definition 5.1.1, used in
[`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) and in
[`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md):

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

The remaining quantifiers are a natural number `p` and an isogeny of root data
`f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P`
([`LinearAlgebra.RootDatumIsogeny`](../../LinearAlgebra/RootDatumIsogeny.md)), subject to
one hypothesis. The structure `f` consists of:

- `f.characteristicExponent : p = 1 ∨ Nat.Prime p`;
- a linear map `f.weightMap : (I' → ℤ) → (I → ℤ)` from the character lattice of
  `𝔾_m^{I'}` to that of `𝔾_m^I`, and a linear map `f.coweightMap : (I → ℤ) → (I' → ℤ)`
  between the cocharacter lattices in the opposite direction, both injective and
  transpose to each other for the pairings of `P` and `Q`
  (`weight_coweight_transpose`);
- a bijection `f.indexEquiv : J' ≃ J` and a function `f.rootFactor : J' → ℕ` whose values
  are powers of `p` (`rootFactor_pow`), such that for every `j' : J'`
  `f.weightMap (Q.root j') = f.rootFactor j' • P.root (f.indexEquiv j')`
  (`root_weightMap`) and
  `f.coweightMap (P.coroot (f.indexEquiv j')) = f.rootFactor j' • Q.coroot j'`
  (`coroot_coweightMap`).

The hypothesis on `f` is `∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0`: if some root factor
is not `1`, then `p` is zero in `R`.

## Conclusion

There are a homomorphism `φ : G ⟶ H` of group schemes over `Spec R` and a homomorphism
`τ : splitTorus (Spec R) I ⟶ splitTorus (Spec R) I'` of group schemes such that

- `IsIsogeny φ` ([`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md)): the
  underlying morphism of schemes of `φ` is finite, flat and surjective;
- `i ≫ φ = τ ≫ i'`: `φ` maps the torus of `G` into the torus of `H`, and its restriction
  to the tori is `τ`;
- for every test scheme `U` over `Spec R`, every point `x : U ⟶ 𝔾_m^I` and every
  `m : I' → ℤ`,
  `∏ j', (pointsEquiv I' U (x ≫ τ.hom.hom))_{j'} ^ m j' = ∏ j, (pointsEquiv I U x)_j ^ (f.weightMap m) j`.
  Here `τ.hom.hom` is the underlying morphism of `τ` in `Over (Spec R)`, so
  `x ≫ τ.hom.hom` is the point `τ(x)` of `𝔾_m^{I'}`, and
  `splitTorus.pointsEquiv I U` identifies the `U`-points of `𝔾_m^I` with families
  in `(Γ(U, 𝒪_U)ˣ)^I`. The left side is the character `χ_m : t ↦ ∏ t_{j'} ^ m_{j'}` of
  `𝔾_m^{I'}` evaluated at `τ(x)`; the right side is the character `χ_{f m}` of `𝔾_m^I`
  evaluated at `x`. Since the identity holds for every `U` and `x`, it says that
  `χ_m ∘ τ = χ_{f.weightMap m}` as morphisms of schemes `𝔾_m^I → 𝔾_m` (Yoneda). So the
  map on character lattices induced by `τ` is the constant map `f.weightMap`.

The conclusion constrains only the weight map of `f`. The other components are determined
by it: the coweight map by the transpose property, because the pairing of `Q` is perfect,
and the index bijection and root factors by `root_weightMap`, because `P` is reduced
(Conrad's remark after Definition 6.1.8, quoted below).

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Theorem 6.1.16(1) (Isogeny Theorem), p.196: "Let S be a non-empty scheme. 1. (Isogeny
  Theorem) For split reductive (G′, T′, M′) and (G, T, M) over S, any p(S)-morphism
  R(G′, T′, M′) → R(G, T, M) is induced by an isogeny f : (G′, T′, M′) → (G, T, M)
  compatible with the splittings, and f is unique up to the faithful action of
  (T/Z_G)(S) on G."
- Definition 6.1.6, p.190: "Let (G, T, M) and (G′, T′, M′) be split reductive groups
  over a scheme S ≠ ∅. A quasi-finite surjection f : (G′, T′) → (G, T) is compatible with
  the splittings if there is a homomorphism h : M → M′, bijection d : Φ′ → Φ, and
  function q : Φ′ → Z_{≥1} valued in prime powers such that: 1. the induced map
  X(f) : M_S = X(T) → X(T′) = M′_S arises from h, 2. for all a′ ∈ Φ′, h(d(a′)) = q(a′)a′
  and h∨(a′∨) = q(a′)d(a′)∨, 3. if q(a′) > 1 is a power of a prime p(a′) then S is a
  Z/p(a′)Z-scheme." The text after it: "h_ℚ is an isomorphism (since each f_s is an
  isogeny) and f uniquely determines h, d, and q."
- Definition 6.1.8, p.191: "Let R′ = (X′, Φ′, X′∨, Φ′∨) and R = (X, Φ, X∨, Φ∨) be reduced
  root data, and p a prime or 1. A p-morphism R′ → R is a triple (h, d, q) consisting of
  a homomorphism h : X → X′, a bijection d : Φ′ → Φ, and a function q : Φ′ → {pⁿ}_{n≥0}
  such that 1. the induced map h_ℚ is an isomorphism (i.e., h is a finite-index
  injection), 2. for all a′ ∈ Φ′, h(d(a′)) = q(a′)a′ and h∨(a′∨) = q(a′)d(a′)∨. … If S is
  a non-empty scheme, a p-morphism (h, d, q) is called a p(S)-morphism if S is a
  Z/p(a′)Z-scheme whenever q(a′) > 1 is a power of a prime p(a′). Since the root data are
  reduced and q takes values in Z_{≥1}, the condition h(d(a′)) = q(a′)a′ implies that h
  determines d and q."
- Definition 3.3.9, p.103: "A homomorphism f : G′ → G between smooth S-affine S-groups is
  an isogeny if it is a finite flat surjection, and is a central isogeny if also ker f is
  central in G′."
- Definition 5.1.1, p.136: "Let G be a reductive group over a non-empty scheme S. It is
  split if there exists a maximal torus T equipped with an isomorphism T ≃ D_S(M) for a
  finite free Z-module M such that: 1. the nontrivial weights a : T → G_m that occur on 𝔤
  arise from elements of M …, 2. each root space 𝔤_a is free of rank 1 over O_S, 3. each
  coroot a∨ : G_m → T arises from an element of the dual lattice M∨ …"
- Definition 3.2.1, p.91, and Remark A.1.2, p.267, resting on Grothendieck's
  Theorem A.1.1: a torus that is maximal on residue fibres is a maximal torus in Conrad's
  (geometric) sense, as in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md).

## Derivation from the source

The proposition is the existence part of Theorem 6.1.16(1) over a non-empty affine base,
with `(G′, T′, M′) = (G, i, ℤ^I)` and `(G, T, M) = (H, i', ℤ^{I'})` in Conrad's notation.
Its terms translate as follows.

- **Split reductive groups.** As in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md):
  Conrad's `T ≃ D_S(M)` with `M = ℤ^I` is the split torus `splitTorus (Spec R) I` with its
  coordinates; any finite free `M` has this form after choosing a basis. Hypotheses 1–4
  transcribe Definition 5.1.1 as in
  [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) (Lemma 5.1.3).
  The root datum `R(G, T, M) = (M, Φ, M∨, Φ∨)` of the split group is then `P` up to
  reindexing roots by `J`, since `P.root` is injective; `P` is reduced, as Definition 6.1.8
  requires.
- **p-morphism of root data.** A `p`-morphism `(h, d, q) : R(G′, T′, M′) → R(G, T, M)` has
  `h : M → M′`, here `ℤ^{I'} → ℤ^I`, which is `f.weightMap`. The bijection `d : Φ′ → Φ`
  from the roots of `G` to those of `H` sends `P.root (f.indexEquiv j')` to `Q.root j'`,
  and `q` takes the value `f.rootFactor j'` at `P.root (f.indexEquiv j')`; the values are
  powers of `p`, and `p` is `1` or a prime. With `a′ = P.root (f.indexEquiv j')`, the
  identity `h(d(a′)) = q(a′)a′` is `root_weightMap`. The dual map `h∨ : M′∨ → M∨` is the
  transpose of `h`, which is `f.coweightMap` by `weight_coweight_transpose`, and
  `h∨(a′∨) = q(a′)d(a′)∨` is `coroot_coweightMap`. Condition 1 of Definition 6.1.8, that
  `h_ℚ` is an isomorphism, is equivalent to injectivity of both `h` and its transpose
  `h∨` between these finite free lattices: injectivity of `h` gives
  `rank M ≤ rank M′`, injectivity of `h∨` gives the reverse inequality, and an injection
  of free lattices of equal finite rank has finite index. Conversely, a triple `(h, d, q)`
  satisfying Definition 6.1.8 gives such an `f`, with `f.coweightMap = h∨`.
- **p(S)-morphism.** If `f.rootFactor j' ≠ 1`, then it is `pⁿ` with `n ≥ 1` and `p ≠ 1`,
  so `p` is prime and `p(a′) = p`. The scheme `Spec R` is a `ℤ/pℤ`-scheme exactly when
  `p = 0` in `R`. So the hypothesis `∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0` is
  Conrad's `p(S)` condition.
- **"Induced by an isogeny f compatible with the splittings".** An isogeny
  `f : (G′, T′) → (G, T)` is a finite flat surjective homomorphism `φ : G ⟶ H`
  (Definition 3.3.9; `IsIsogeny φ`) that carries `T′` into `T`. Since `i'` is a closed
  immersion, the restriction of `φ` to the torus of `G` factors through `i'` by a unique
  homomorphism of tori `τ`; this is `i ≫ φ = τ ≫ i'`. A finite surjection is a
  quasi-finite surjection. Condition 1 of Definition 6.1.6 says that `X(φ|T′)`, which
  sends a character `χ` of `𝔾_m^{I'}` to `χ ∘ τ`, is the constant map `h`; this is the
  identity of points in the conclusion. Conditions 2 and 3 of Definition 6.1.6 for the
  given `(h, d, q)` are the hypotheses on `f`. So `φ` is compatible with the splittings
  through `(h, d, q)`. Since `φ` determines its triple (the text after Definition 6.1.6),
  `R(φ)` is the given triple, which is what "induced by" means. Conversely, an isogeny as
  in Conrad's conclusion gives `φ` and `τ = φ|T′` satisfying the three clauses.
- **Affine base.** The free root-space hypothesis uses `splitTorus.exponentWeightSpace`,
  which the Library defines only over an affine base `Spec R`. Conrad's theorem allows any
  non-empty scheme `S`. The statement over a general `S` is not a formal consequence of
  this one: isogenies chosen over the members of an affine open cover need not glue, and
  gluing would use the uniqueness clause. So this proposition is a specialization of the
  source's statement to affine bases, not a reformulation of it.
- **Empty base.** Non-emptiness of `S` is not assumed. For `R = 0` the proposition holds
  trivially: every scheme over the empty scheme `Spec 0` is empty, so there are unique
  morphisms `φ` and `τ`, the equation `i ≫ φ = τ ≫ i'` holds, the morphism of empty
  schemes underlying `φ` is finite, flat and surjective, and the identity of points is an
  identity in the trivial group of units of the zero ring.
- **Free root spaces.** Over a base with non-trivial Picard group, root spaces need not
  be free: for a line bundle `L`, the diagonal torus of `GL(𝒪 ⊕ L)` has root spaces `L`
  and `L⁻¹` (up to the sign convention). This is why condition 2 of Definition 5.1.1 is
  imposed as hypothesis 4.

## Scope

All objects are in universe `u`. The proposition does not state:

- the uniqueness of `φ` up to the action of `(T/Z_G)(S)`;
- the Existence Theorem 6.1.16(2), that every root datum is the root datum of a split
  reductive group;
- the converse direction (Example 6.1.9: an isogeny compatible with the splittings
  induces a `p(S)`-morphism of root data), or Proposition 6.1.7 (quasi-finite surjections
  between split groups are compatible with the splittings over a connected base).

## Relation to the Library

- [`Reductive.SplitIsogenyStatement`](SplitIsogenyStatement.md) records, as
  `SplitIsogenyExistenceStatement`, the same existence assertion over a field (Milne,
  Theorem 23.9), with exponent `p = ringExpChar k`, arbitrary split maximal tori and their
  actual character and cocharacter lattices. The two propositions are stated on different
  lattices; this module does not prove either from the other.
- [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  states the corresponding assertion for isomorphisms of root data (Conrad,
  Theorem 6.1.17), with the same split hypotheses and the same identity of points, and
  concludes that `φ` and `τ` are isomorphisms. The present proposition applied to the
  central isogeny `RootDatumIsogeny.ofHom` of an equivalence gives only an isogeny `φ`; the
  isomorphism case is not a formal consequence of it.
- [`Reductive.FibrewiseIsogenyStatement`](FibrewiseIsogenyStatement.md) states Conrad's
  Proposition 6.1.10, that a homomorphism of reductive groups whose fibres are isogenies
  is an isogeny.

This module proves none of these relations.
