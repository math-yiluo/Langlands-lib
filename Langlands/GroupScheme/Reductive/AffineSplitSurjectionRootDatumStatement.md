# Statement: quasi-finite surjections of split reductive groups respect the splittings

Worker 75.

`Langlands.GroupScheme.AffineSplitSurjectionRootDatumStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports Mathlib's
`AlgebraicGeometry.Morphisms.QuasiFinite` (for `LocallyQuasiFinite`),
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) (for `IsFibrewiseRootDatumOf`
and, through it, `splitTorus`, `splitTorus.pointsEquiv` and
`splitTorus.exponentWeightSpace`), [`Reductive.Basic`](Basic.md) (for `IsReductive` and
`IsClosedSubgroup`), [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md)
(for `IsFibrewiseMaximalTorus`) and
[`LinearAlgebra.RootDatumIsogeny`](../../LinearAlgebra/RootDatumIsogeny.md) (for
`RootDatumIsogeny`).

It states Conrad's Proposition 6.1.7 over an affine base `Spec R`: a quasi-finite
surjective homomorphism between split reductive groups that carries the split maximal
torus of the source into that of the target is compatible with the splittings
Zariski-locally on the base, and over the whole base when the base is connected.

## Statement and quantifiers

The proposition quantifies over the same data as
[`Reductive.AffineSplitIsogenyTheoremStatement`](AffineSplitIsogenyTheoremStatement.md):

- every commutative ring `R : Type u`, with base scheme `Spec R`. The ring may be zero,
  non-Noetherian and non-local, and `Spec R` may be disconnected;
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
  `[Q.IsReduced]`. The type `RootDatumIsogeny` in the conclusion needs these four
  instances. They restrict nothing: hypothesis 3 below, `IsFibrewiseRootDatumOf`,
  contains finiteness of the index type and reducedness of the root datum as its first two
  conjuncts.

It has four hypotheses on `(G, i, P)` and the same four on `(H, i', Q)`. Together they say
that `(G, i, P)` and `(H, i', Q)` are split. They are the hypotheses of the Library's
encoding of Conrad's Definition 5.1.1, as in
[`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) and
[`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md):

1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
2. `IsFibrewiseMaximalTorus i`: for every point `s` of `Spec R`, the residue fibre of `i`
   over `κ(s)` satisfies the field predicate `IsMaximalTorus`.
3. `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and for every field
   `k` with a ring homomorphism `R → k`, the realization of `P` over `k` is the root datum
   (`IsRootDatumOf`) of the base change of `i` to `k`. Under the realization, `m : I → ℤ`
   is the character `t ↦ ∏ⱼ tⱼ ^ mⱼ` and `n : I → ℤ` is the cocharacter
   `s ↦ (s ^ nⱼ)ⱼ`. So the roots and coroots of every field-valued fibre are the constant
   elements of `P`.
4. For every `α : J`, the weight space `splitTorus.exponentWeightSpace I G i (P.root α)`
   in the Lie algebra `lieKernel G R` is isomorphic to `R` as an `R`-module, that is, free
   of rank one.

It then quantifies over homomorphisms `φ : G ⟶ H` and
`τ : splitTorus (Spec R) I ⟶ splitTorus (Spec R) I'` of group schemes over `Spec R`, with
three hypotheses:

- `LocallyQuasiFinite φ.hom.hom.left` (Mathlib): the underlying morphism of schemes of `φ`
  is locally quasi-finite;
- `Surjective φ.hom.hom.left` (Mathlib): it is surjective;
- `i ≫ φ = τ ≫ i'`: `φ` maps the torus of `G` into the torus of `H`, and its restriction
  to the tori is `τ`.

## Conclusion

The conclusion is a conjunction of two clauses. Both use an isogeny of root data
`f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P`
([`LinearAlgebra.RootDatumIsogeny`](../../LinearAlgebra/RootDatumIsogeny.md)) for some
`p : ℕ`. Such an `f` consists of: `p = 1 ∨ Nat.Prime p`; injective linear maps
`f.weightMap : (I' → ℤ) → (I → ℤ)` and `f.coweightMap : (I → ℤ) → (I' → ℤ)`, transpose to
each other for the pairings of `Q` and `P`; a bijection `f.indexEquiv : J' ≃ J`; and root
factors `f.rootFactor : J' → ℕ`, each a power of `p`, with
`f.weightMap (Q.root j') = f.rootFactor j' • P.root (f.indexEquiv j')` and
`f.coweightMap (P.coroot (f.indexEquiv j')) = f.rootFactor j' • Q.coroot j'`.

Both clauses also use the identity of points

`∏ j', (pointsEquiv I' U (x ≫ τ.hom.hom))_{j'} ^ m j' = ∏ j, (pointsEquiv I U x)_j ^ (f.weightMap m) j`

for a test scheme `U` over `Spec R`, a point `x : U ⟶ 𝔾_m^I` and `m : I' → ℤ`. Here
`τ.hom.hom` is the underlying morphism of `τ` in `Over (Spec R)`, so `x ≫ τ.hom.hom` is
the point `τ(x)` of `𝔾_m^{I'}`, and `splitTorus.pointsEquiv I U` identifies the `U`-points
of `𝔾_m^I` with families in `(Γ(U, 𝒪_U)ˣ)^I`. The left side is the character
`χ_m : t ↦ ∏ t_{j'} ^ m_{j'}` of `𝔾_m^{I'}` evaluated at `τ(x)`; the right side is the
character `χ_{f m}` of `𝔾_m^I` evaluated at `x`. When the identity holds for all `x` over
all `U` mapping into an open `V`, it says that `χ_m ∘ τ = χ_{f.weightMap m}` as morphisms
`𝔾_m^I → 𝔾_m` over `V` (Yoneda), so the map on character lattices induced by `τ` over `V`
is the constant map `f.weightMap`.

1. **Zariski-local clause.** For every point `s` of `Spec R` there are an open
   `V : (Spec R).Opens` with `s ∈ V`, a natural number `p` and
   `f : RootDatumIsogeny p Q P` such that
   - `∀ j', f.rootFactor j' ≠ 1 → (p : Γ(Spec R, V)) = 0`: if some root factor is not
     `1`, then `p` is zero in the ring of sections of `𝒪` over `V`;
   - the identity of points holds for every test scheme `U` over `Spec R` with
     `U.hom ⁻¹ᵁ V = ⊤`, that is, whose structure morphism lands in `V`, every `x` and
     every `m`.
2. **Connected clause.** If `Spec R` is a connected topological space (in particular
   non-empty), there are `p` and `f : RootDatumIsogeny p Q P` such that
   `∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0` and the identity of points holds for every
   test scheme `U` over `Spec R`, every `x` and every `m`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 6.1.7, p.190: "For split reductive (G, T, M) and (G′, T′, M′) over a
  scheme S ≠ ∅, any quasi-finite surjection f : (G′, T′) → (G, T) is compatible with the
  splittings Zariski-locally on S. If S is connected then f is compatible with the
  splittings over S." The text before it calls it an "immediate consequence of the
  preceding considerations" (pp.187-190: Lemmas 6.1.3 and 6.1.4).
- Definition 6.1.6, p.190: "Let (G, T, M) and (G′, T′, M′) be split reductive groups
  over a scheme S ≠ ∅. A quasi-finite surjection f : (G′, T′) → (G, T) is compatible with
  the splittings if there is a homomorphism h : M → M′, bijection d : Φ′ → Φ, and
  function q : Φ′ → Z_{≥1} valued in prime powers such that: 1. the induced map
  X(f) : M_S = X(T) → X(T′) = M′_S arises from h, 2. for all a′ ∈ Φ′, h(d(a′)) = q(a′)a′
  and h∨(a′∨) = q(a′)d(a′)∨, 3. if q(a′) > 1 is a power of a prime p(a′) then S is a
  Z/p(a′)Z-scheme." The text after it: "h_ℚ is an isomorphism (since each f_s is an
  isogeny) and f uniquely determines h, d, and q."
- p.187, before Lemma 6.1.3: for a quasi-finite surjective S-homomorphism f : G′ → G with
  f(T′) ⊂ T, "f : T′ → T is an isogeny, since the map X(f) … induces a finite-index
  inclusion of lattices on geometric fibers over S", and "There is an open cover {U_i} of
  S such that the map induced by X(f) on U_i-sections carries M into M′."
- Definition 6.1.8, p.191: a p-morphism R′ → R of reduced root data, for p a prime or 1,
  is a triple (h, d, q) with h : X → X′, a bijection d : Φ′ → Φ and q valued in powers of
  p, such that h_ℚ is an isomorphism, h(d(a′)) = q(a′)a′ and h∨(a′∨) = q(a′)d(a′)∨;
  "If S is a non-empty scheme, a p-morphism (h, d, q) is called a p(S)-morphism if S is a
  Z/p(a′)Z-scheme whenever q(a′) > 1 is a power of a prime p(a′)."
- Example 6.1.9, p.191: "For a non-empty scheme S and quasi-finite surjection
  f : (G′, T′, M′) → (G, T, M) compatible with the splittings, the associated triple
  R(f) := (h, d, q) is a p(S)-morphism between the root data where either p = 1 or
  char(k(s)) = p > 1 for all s ∈ S".
- Definition 5.1.1, p.136 (split reductive groups), Definition 3.2.1, p.91, and
  Remark A.1.2, p.267 (maximal tori), as in
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md).

## Derivation from the source

The proposition is Proposition 6.1.7 over an affine base, with `(G′, T′, M′) = (G, i, ℤ^I)`
and `(G, T, M) = (H, i', ℤ^{I'})` in Conrad's notation. Its terms translate as follows.

- **Split reductive groups** are encoded by hypotheses 1–4 exactly as in
  [`Reductive.AffineSplitIsogenyTheoremStatement`](AffineSplitIsogenyTheoremStatement.md),
  and their root data are `P` and `Q`.
- **Quasi-finite surjection f : (G′, T′) → (G, T).** This is a homomorphism `φ` that is
  quasi-finite and surjective and carries `T′` into `T`. Since `i'` is a closed immersion,
  the last condition is `i ≫ φ = τ ≫ i'` for a unique homomorphism of tori `τ`. Conrad's
  quasi-finite (EGA) means of finite type with finite fibres. Here `φ` is a morphism
  between schemes that are affine and of finite type over `Spec R` (smooth and affine),
  and `H` is separated over `Spec R`, so `φ` is affine and of finite type. For a morphism
  of finite type, Mathlib's `LocallyQuasiFinite` is equivalent to having finite fibres
  (`locallyQuasiFinite_iff_finite_preimage_singleton`). So the hypothesis
  `LocallyQuasiFinite φ.hom.hom.left` is Conrad's quasi-finiteness.
- **Compatible with the splittings.** Over a non-empty open `V`, compatibility asks for
  `(h, d, q)` with conditions 1–3 of Definition 6.1.6 over `V`. The dictionary with `f` is
  the one in
  [`Reductive.AffineSplitIsogenyTheoremStatement`](AffineSplitIsogenyTheoremStatement.md):
  `h = f.weightMap`, `d` sends `P.root (f.indexEquiv j')` to `Q.root j'`, `q` takes the
  value `f.rootFactor j'` at `P.root (f.indexEquiv j')`, condition 2 is `root_weightMap`
  and `coroot_coweightMap` (with `h∨ = f.coweightMap`, the transpose of `h`), and
  condition 1 over `V` is the identity of points for test schemes mapping into `V`.
  `V` is a `ℤ/pℤ`-scheme exactly when `p = 0` in `Γ(Spec R, V)`, so condition 3 is the
  root-factor clause. The conclusion asks for slightly more than Definition 6.1.6 in two
  respects, both of which follow from it.
  - **A single exponent `p`.** `RootDatumIsogeny p` uses one `p` for all root factors.
    Over a non-empty `V`, two root factors that are powers `> 1` of different primes `p`
    and `ℓ` would make both `p` and `ℓ` zero on `V`, hence `1 = 0` on `V`; so all root
    factors different from `1` are powers of one prime `p`, and `p = 1` serves when all
    root factors are `1`. This is the `p(S)`-morphism of Example 6.1.9.
  - **Injectivity of both lattice maps.** `RootDatumIsogeny` requires `f.weightMap` and
    its transpose `f.coweightMap` to be injective. Between free lattices of finite rank
    this is equivalent to `h_ℚ` being an isomorphism, which Conrad notes after
    Definition 6.1.6 for every `f` compatible with the splittings ("since each f_s is an
    isogeny").
- **Zariski-locally on S** is the first clause: every point has an open neighbourhood `V`
  over which `φ` is compatible with the splittings. Test schemes `U` with
  `U.hom ⁻¹ᵁ V = ⊤` are the schemes over `V`.
- **Over a connected S** is the second clause, with `V` the whole base; `S ≠ ∅` is part of
  `ConnectedSpace`. The two clauses are independent as stated: the first does not give the
  second because a single `f` must work on all of `Spec R`, and the second says nothing
  about disconnected bases.
- **Affine base.** The free root-space hypothesis uses `splitTorus.exponentWeightSpace`,
  which the Library defines only over an affine base `Spec R`. Conrad's proposition allows
  any non-empty scheme `S`. For the Zariski-local clause the general case reduces to affine
  open subschemes, but transferring the split hypotheses to an open subscheme is not part
  of this module; so the proposition is a specialization to affine bases.
- **Empty base.** For `R = 0`, `Spec R` has no points and is not connected, so both
  clauses hold trivially.

## Scope

All objects are in universe `u`. The proposition does not state:

- that `f` (equivalently `(h, d, q)`) is determined by `φ` on `V`;
- that `φ` is finite and flat, hence an isogeny (Proposition 6.1.10, recorded as
  [`Reductive.FibrewiseIsogenyStatement`](FibrewiseIsogenyStatement.md) in a fibrewise
  form);
- the centrality criterion after Example 6.1.9 (`φ` is a central isogeny if and only if
  all root factors are `1`), or the compatibility of `R(φ)` with composition and base
  change;
- Lemma 6.1.4 on the maps between root groups.

## Relation to the Library

- [`Reductive.IsogenyRootDatumStatement`](IsogenyRootDatumStatement.md) records the field
  case (Milne, Proposition 23.5) for isogenies between split reductive groups over a field,
  on actual character lattices and with `p = ringExpChar k`, together with the centrality
  and isomorphism criteria. This module does not prove either proposition from the other.
- [`Reductive.AffineSplitIsogenyTheoremStatement`](AffineSplitIsogenyTheoremStatement.md)
  states the converse direction (Conrad, Theorem 6.1.16(1)): every `p(S)`-morphism of root
  data is induced by an isogeny compatible with the splittings.

This module proves none of these relations.
