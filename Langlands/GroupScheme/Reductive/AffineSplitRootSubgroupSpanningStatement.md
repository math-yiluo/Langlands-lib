# Statement: open cell, Borel subgroup, directly spanned root subgroups and commutator relations over an affine base

Worker 75.

`Langlands.GroupScheme.AffineSplitRootSubgroupSpanningStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. Its only import is
[`Reductive.LocalSplitCell`](LocalSplitCell.md). That module provides `Ga`,
`IsRootParametrization`, `rootPoint`, `orderedProduct`, `cellObj` and `cellMap`. Through its
imports it also provides:

- `IsReductive`, `IsClosedSubgroup`, `IsUnipotent`, `geometricFiber` and `scalarMap` from
  [`Reductive.Basic`](Basic.md);
- `IsFibrewiseRootDatumOf` and `splitTorus` from
  [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md);
- `IsMaximalTorus` from [`Torus.Maximal`](../Torus/Maximal.md);
- `VectorGroup.groupScheme` and `VectorGroup.coordinates` from
  [`VectorGroupQuotient`](../VectorGroupQuotient.md).

It states four results of Conrad's §5.1 for a split reductive group over an affine base
`Spec R`, where `R` is any commutative ring:

- the open cell of Theorem 5.1.13;
- the closed "Borel" subgroup `T ⋉ U_{Φ⁺}` of Theorem 5.1.13;
- Proposition 5.1.16(1), the smooth closed subgroups `U_Ψ` directly spanned by root
  groups, which includes the part of Theorem 5.1.13 about `U_{Φ⁺}`;
- Proposition 5.1.14, the commutator relations between root groups.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`, with no further hypothesis. It may be zero,
  non-Noetherian, non-local and non-reduced. When `R = 0`, `Spec R` is empty and every
  clause holds trivially, so Conrad's "non-empty scheme `S`" needs no separate
  hypothesis;
- a group scheme `G : GroupScheme (Spec R)` with the instance `IsAffineHom G.X.hom` and
  `IsReductive G` ([`Reductive.Basic`](Basic.md)). `IsReductive G` means `G` is smooth and
  affine over `Spec R` and every geometric fibre is a smooth connected affine group with
  trivial unipotent radical. The affineness instance repeats part of `IsReductive G`;
  the binders are those of `LocalSplitBigCellStatement` in
  [`Reductive.LocalSplitCell`](LocalSplitCell.md);
- a finite type `I : Type u` and a homomorphism `i : splitTorus (Spec R) I ⟶ G` from the
  coordinate split torus `T = 𝔾_m^I`;
- a type `J : Type u` and a Mathlib root datum `P : RootDatum J (I → ℤ) (I → ℤ)`;
- a family `u : J → (Ga R ⟶ G)` of homomorphisms from the additive group
  `Ga R = 𝔾ₐ = VectorGroup.groupScheme R 1`.

The hypotheses are exactly those of `LocalSplitBigCellStatement` in
[`Reductive.LocalSplitCell`](LocalSplitCell.md), without `[IsLocalRing R]` and
`[IsReduced R]`:

1. `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
2. For every point `s` of `Spec R`, the base change of `i` along
   `Spec κ(s) → Spec R` is a maximal torus (`IsMaximalTorus`) of the fibre `G_{κ(s)}`.
3. `IsFibrewiseRootDatumOf I G i P` ([`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md)):
   `J` is finite, `P` is reduced, and for every field `k` with an `R`-algebra structure the
   realization of `P` over `k` is the root datum of the base change of `i` to `k`. A
   character `m : I → ℤ` is `t ↦ ∏ⱼ tⱼ ^ mⱼ`.
4. For every `α : J`, `IsRootParametrization i (P.root α) (u α)`
   ([`Reductive.LocalSplitCell`](LocalSplitCell.md)). The map `u α` represents the
   relative root subgroup of `G` for the character `P.root α`. It is a closed immersion,
   and it is torus-equivariant: `i(t) u_α(c) i(t)⁻¹ = u_α(α(t) c)` for every test scheme
   `Z`, every `t ∈ T(Z)` and every `c ∈ Γ(Z, 𝒪_Z)`.

The roots are `Φ = P.root`. Mathlib's `RootPairing.root` is an embedding, so `Φ` is
indexed by `J` without repetition, and `-P.root α` is again a root. For a base
`b : P.Base`, `b.IsPos α` says that `P.root α` is positive for `b`; the positive roots for
`b` form a positive system `Φ⁺`, and every positive system arises this way.

Points are written as follows. For a test scheme `Z` over `Spec R` and
`c ∈ Γ(Z, 𝒪_Z)`, `rootPoint (u α) Z c : Z ⟶ G.X` is the point `u_α(c)`. For
`e : Fin r → J` and `c : Fin r → Γ(Z, 𝒪_Z)`, `orderedProduct u e Z c` is the ordered
product `u_{e 0}(c 0) ⋯ u_{e (r-1)}(c (r-1))` in the group `G(Z)`.

## Conclusion

The conclusion is the conjunction of four clauses.

1. **Open cell.** For every base `b`, all `m, n : ℕ` and enumerations
   `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}` of the negative
   and the positive roots, the morphism of schemes underlying
   `cellMap i u neg pos : 𝔾ₐᵐ × T × 𝔾ₐⁿ ⟶ G`,
   `(v, t, w) ↦ (∏ₖ u_{neg k}(vₖ)) · i(t) · (∏ₖ u_{pos k}(wₖ))`, is an open immersion.
2. **The subgroup `T ⋉ U_{Φ⁺}`.** For every base `b`, every `n : ℕ` and every enumeration
   `pos` of the positive roots, there are a group scheme `B` over `Spec R`, a homomorphism
   `jB : B ⟶ G` with `IsClosedSubgroup jB`, and an isomorphism
   `φ : cellObj R I 0 n ≅ B.X` over `Spec R` such that `φ ≫ jB = cellMap i u Fin.elim0 pos`.
   Here `cellObj R I 0 n = (𝔾ₐ⁰ × T) × 𝔾ₐⁿ`, and `𝔾ₐ⁰` is the trivial group, so the empty
   product of negative root groups is `1`. The equation says that the map
   `T × 𝔾ₐⁿ ⟶ G`, `(t, w) ↦ i(t) · ∏ₖ u_{pos k}(wₖ)`, is an isomorphism onto the closed
   subgroup `B`.
3. **Directly spanned subgroups `U_Ψ`.** Let `Ψ : Set J` be closed and satisfy
   `Ψ ∩ -Ψ = ∅`, encoded as follows:
   - closed: `∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : J, P.root d = P.root a + P.root c → d ∈ Ψ`;
   - `Ψ ∩ -Ψ = ∅`: `∀ a ∈ Ψ, ∀ c ∈ Ψ, P.root a + P.root c ≠ 0`.

   Then there are a group scheme `H` over `Spec R` and a homomorphism `j : H ⟶ G` such
   that:
   - `IsClosedSubgroup j` and `Smooth H.X.hom`;
   - `H` is normalized by the torus: for every test scheme `Z`, every `t ∈ T(Z)` and every
     `h ∈ H(Z)` there is `h' ∈ H(Z)` with `i(t) · j(h) · i(t)⁻¹ = j(h')`;
   - for every point `s` of `Spec R`, the geometric fibre `geometricFiber H s` (base change
     to an algebraic closure of `κ(s)`) has connected underlying space and is unipotent
     (`IsUnipotent`: every nonzero finite-dimensional representation has a nonzero fixed
     vector);
   - for every `n : ℕ` and every enumeration `e : Fin n ≃ Ψ`, there is an isomorphism
     `φ : 𝔾ₐⁿ ≅ H.X` over `Spec R` with `φ ≫ j` equal to the multiplication map
     `𝔾ₐⁿ ⟶ G`, `w ↦ ∏ₖ u_{e k}(wₖ)`. In Lean this map is `orderedProduct` at the
     universal point: the test scheme is `𝔾ₐⁿ` itself and the arguments are the
     coordinate functions `VectorGroup.coordinates R n _ (𝟙 _)`.

   `H` is chosen before the enumeration, so the same subgroup works for every
   enumeration.
4. **Commutator relations.** Let `a, c : J` with `P.root c ≠ P.root a` and
   `P.root c ≠ -P.root a`. For every `n : ℕ` and every enumeration `e` of the type
   `{d : J // ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root d = p • P.root a + q • P.root c}`, there are
   `p, q : Fin n → ℕ` and `C : Fin n → R` such that:
   - for every `k`, `0 < p k`, `0 < q k` and `P.root (e k) = p k • P.root a + q k • P.root c`;
   - for every test scheme `Z` and all `x, y ∈ Γ(Z, 𝒪_Z)`,
     `u_a(x) · u_c(y) · u_a(-x) · u_c(-y) = ∏ₖ u_{e k}(C_k · x ^ p k · y ^ q k)`,
     where `C_k` stands for its image `scalarMap Z (C k)` in `Γ(Z, 𝒪_Z)` and the product
     is `orderedProduct` taken in the order of `e`.

   When no root has the form `pa + qc` with `p, q > 0`, the product is empty and the
   clause says that `U_a` and `U_c` commute.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Theorem 5.1.13, p.143: "Let (G, T, M) be a split reductive group over a non-empty
  scheme S. Fix a positive system of roots Φ⁺ ⊂ Φ. For any enumeration {a_i} of Φ⁺, the
  multiplication map ∏_i U_{a_i} → G is an isomorphism onto a smooth closed subgroup U_{Φ⁺}
  that is normalized by T, independent of the choice of enumeration, and has connected
  unipotent fibers. The multiplication map U_{−Φ⁺} × T × U_{Φ⁺} → G is an isomorphism onto
  an open subscheme Ω_{Φ⁺} and the semi-direct product T ⋉ U_{Φ⁺} → G is a closed
  S-subgroup." The proof is on pp.144–145.
- Proposition 5.1.14, p.145: "Let (G, T, M) be a split reductive group over a non-empty
  scheme S. Pick roots a, b ∈ Φ such that b ≠ ±a. Choose trivializations of the root
  spaces 𝔤_c for all roots c = ia + jb with integers i, j > 0. Consider the associated
  parameterizations p_c : G_a ≃ U_c, and fix an enumeration of this set of roots c. The
  root groups U_a and U_b commute if there are no roots of the form ia + jb with integers
  i, j > 0, and in general the commutation relation is given by (5.1.5)
  (p_a(x), p_b(y)) := p_a(x)p_b(y)p_a(−x)p_b(−y) = ∏_{i,j>0} p_{ia+jb}(C_{i,j,a,b} x^i y^j)
  where the product is taken over all roots ia + jb with i, j > 0 and the coefficients
  C_{i,j,a,b} are global functions on S." The proof is on pp.145–146.
- The digression on p.146: "a subset Ψ ⊂ Φ is called closed if a + b ∈ Ψ for any
  a, b ∈ Ψ such that a + b ∈ Φ." Lemma 5.1.15, pp.146–147, shows that for closed `Ψ`,
  "Ψ ∩ −Ψ is empty" is equivalent to `Ψ` lying in a positive system of roots.
- Proposition 5.1.16(1), p.147: "Let (G, T, M) be a split reductive group over a
  non-empty scheme S, and let Ψ be a closed set in Φ such that Ψ ∩ −Ψ = ∅. 1. For any
  enumeration {a_i} of Ψ, the multiplication map ∏ U_{a_i} → G is an isomorphism onto a
  smooth closed subgroup U_Ψ. This subgroup is normalized by T, independent of the choice
  of enumeration, and has connected unipotent fibers." The proof is on pp.147–148.
- Definition 5.1.1, p.136 (split reductive groups): "Let G be a reductive group over a
  non-empty scheme S. It is split if there exists a maximal torus T equipped with an
  isomorphism T ≃ D_S(M) for a finite free Z-module M such that: 1. the nontrivial
  weights a : T → G_m that occur on 𝔤 arise from elements of M …, 2. each root space
  𝔤_a is free of rank 1 over O_S, 3. each coroot a∨ : G_m → T arises from an element of
  the dual lattice M∨ …"

## Derivation from the source

- **The split group.** With `M = ℤ^I`, Conrad's `T ≃ D_S(M)` is the coordinate split
  torus `𝔾_m^I`, and the root datum of the split group is `P`. Hypotheses 1–3 say that `i`
  is a closed subgroup that is a maximal torus on every fibre, with constant root datum
  `P`. For each root `α`, hypothesis 4 gives a torus-equivariant isomorphism `u α` from
  `𝔾ₐ` onto the root group `U_α`. Such an isomorphism has `Lie(U_α) = 𝔤_α` free of rank
  one, which is condition 2 of Definition 5.1.1. Conversely, Conrad's parametrization
  `p_α` attached to a trivialization of `𝔤_α` is such a map. The family `u` plays the role
  of Conrad's chosen parametrizations `p_c`. The statement quantifies over every family
  `u` satisfying hypothesis 4, so it holds for every choice of trivializations.
- **Clause 1** is the second sentence of Theorem 5.1.13, with `U_{±Φ⁺}` written as the
  ordered products of their root groups.
- **Clause 2** is the last assertion of Theorem 5.1.13. `T ⋉ U_{Φ⁺} → G` is the
  multiplication map `T × U_{Φ⁺} → G`. With `U_{Φ⁺} = ∏ₖ U_{pos k}` it is the map
  `(t, w) ↦ i(t) ∏ₖ u_{pos k}(wₖ)`. "Is a closed S-subgroup" is encoded as an
  isomorphism onto the underlying scheme of a closed subgroup `B` of `G`. The group law of
  `B` transported to `T × 𝔾ₐⁿ` is the semidirect product law. The statement does not
  spell this out; it is determined by `jB` being a homomorphism.
- **Clause 3** is Proposition 5.1.16(1). "Closed subgroup U_Ψ" is the closed subgroup
  `j : H ⟶ G`. "Smooth" is `Smooth H.X.hom`. "Normalized by T" is stated on points, with
  the existential quantifier expressing that `i(t) j(h) i(t)⁻¹` lies in the image of `j`.
  "Independent of the choice of enumeration" is the order of quantifiers, `∃ H, ∀ e`.
  "Connected unipotent fibers" is stated on geometric fibres. For a group scheme over a
  field, connectedness (the group has a rational point) and unipotence do not change
  under extension of the field, so this agrees with the condition on residue-field
  fibres. The closedness condition takes
  `a = c` as well, and Conrad's definition also allows `a = b`. `Ψ ∩ -Ψ = ∅` is stated
  through roots: `Ψ` contains no `c` with `P.root c = -P.root a` for some `a ∈ Ψ`, and
  the case `a = c` holds automatically since roots are nonzero.
- **The part of Theorem 5.1.13 about `U_{Φ⁺}`** is the case of clause 3 with `Ψ` the
  positive roots of a base. In a reduced root system a root that is a sum of two positive
  roots is positive, so this `Ψ` is closed, and `Φ⁺ ∩ -Φ⁺ = ∅`.
- **Clause 4** is Proposition 5.1.14 with Conrad's `b` renamed `c`. The commutator
  `(p_a(x), p_c(y))` is computed in the group `G(Z)`; the points of `𝔾ₐ²` are pairs of
  global functions, so asking the identity for all `Z`, `x` and `y` is the identity of
  morphisms `𝔾ₐ × 𝔾ₐ → G` (Yoneda). `u_a(-x) = u_a(x)⁻¹` because `u a` is a
  homomorphism, so the left side is the commutator. Since `P` is reduced and
  `c ≠ ±a`, the roots `P.root a` and `P.root c` are linearly independent, and the
  exponents `(p k, q k)` with `P.root (e k) = p k • P.root a + q k • P.root c` are
  determined by `e k`. The statement still asks for them explicitly. Conrad's
  coefficients `C_{i,j,a,b}` are global functions on `S = Spec R`, that is elements of
  `R`; on a test scheme `Z` they act through `scalarMap Z : R → Γ(Z, 𝒪_Z)`. As Conrad
  notes, the coefficients depend on the enumeration and on the parametrizations, so
  they are existentially quantified after `e` and `u`.
- **Affine base.** The Library's root parametrizations (`IsRootParametrization`, and
  `cellMap` built on them) are defined over an affine base `Spec R`. Conrad allows any
  non-empty scheme `S`. So this proposition specializes the source to affine bases.

## Scope

All objects are in universe `u`. The proposition does not state:

- Proposition 5.1.16(2), the filtration `U_{Ψ_{λ>n}}` of `U_Ψ` with quotients that are
  vector groups;
- the uniqueness of `U_Ψ` or of `B` as subgroups, or the description of `Lie(U_Ψ)` as the
  sum of the root spaces;
- the computation of the structure constants `C`; Conrad calls them "mysterious at this
  stage of the theory";
- that `B` has connected solvable fibres, or that its geometric fibres are Borel
  subgroups. These facts appear in the proof of Theorem 5.1.13 but not in its statement;
- the corresponding results over a non-affine base.

## Relation to the Library

- `LocalSplitBigCellStatement` in [`Reductive.LocalSplitCell`](LocalSplitCell.md) is
  clause 1 for a reduced local ring `R`. It is proved in
  [`Reductive.LocalSplitBigCellProof`](LocalSplitBigCellProof.md); that Markdown notes
  that the proof uses neither locality nor reducedness.
- [`Reductive.SplitBigCellField`](SplitBigCellField.md) has the open cell over a field.
- [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  encodes split reductive groups over `Spec R` by a free-root-space hypothesis instead of
  root parametrizations.

This module proves none of these relations.
