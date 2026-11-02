# The equivariant apartment quotient

Module `Langlands.Geometry.Building.ApartmentQuotient`, namespace
`Langlands.Geometry.Building`.

This module builds the group-action quotient behind Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 4.4.4 (printed p. 183),
for an abstract subgroup family. It also builds the quotient-map step in the proof of
Corollary 4.4.5, with the 2024 corrections applied. Everything here is plain group
theory, using Mathlib groups, subgroups, `MulAction`, `MulActionHom` and `Quotient`.
No field, reductive group, root datum, group scheme, parahoric subgroup, building,
metric or topology is involved. The module does not say that any such data exist
for a reductive group. It also does not assume, or package, an existence theorem
for Bruhat–Tits buildings.

## Setting

Throughout, `H` is a group, `N : Subgroup H`, and `A` is a type with
`[MulAction N A]` (the action of the subgroup `N`, viewed as a group). A subgroup
family is a function `P : A → Subgroup H`. The quotient acts as the group `H`, and
`N` acts on it by restriction (Mathlib's `Subgroup.smul_def`: `n • q = (n : H) • q`).

## The relation and its hypothesis

- `apartmentRel N P a b` for `a b : H × A` is
  `∃ n : N, n • a.2 = b.2 ∧ a.1⁻¹ * b.1 * (n : H) ∈ P a.2`.
  `apartmentRel_iff` restates it on pairs:
  `(g, x) ∼ (h, y) ↔ ∃ n : N, n • x = y ∧ g⁻¹ * h * n ∈ P x`.
  The factors appear in the order of KP (4.4.2): `g⁻¹ h n ∈ G(k)_x`.
- `IsConjCovariant N P` is `∀ n x p, p ∈ P x → n * p * n⁻¹ ∈ P (n • x)`,
  that is `n P_x n⁻¹ ≤ P_(n • x)` for every `n ∈ N`. This is the only hypothesis on
  `P` used to build the quotient.
  - `IsConjCovariant.inv_conj_mem`: applied to `n⁻¹`, it gives
    `n⁻¹ P_(n • x) n ≤ P_x`.
  - `IsConjCovariant.conj_mem_iff`: `n p n⁻¹ ∈ P (n • x) ↔ p ∈ P x`. So
    covariance in fact forces `n P_x n⁻¹ = P_(n • x)` as sets.
- `IsConjCovariant.apartmentRel_equivalence`: covariance makes `apartmentRel N P`
  an equivalence relation.
  - Reflexivity uses `n = 1`.
  - Symmetry sends `n` to `n⁻¹`. Given `g⁻¹ h n ∈ P x` and `n • x = y`, covariance
    applied to the inverse gives `n (n⁻¹ h⁻¹ g) n⁻¹ = h⁻¹ g n⁻¹ ∈ P y`.
  - Transitivity sends `n, m` to `m * n`. It multiplies `g⁻¹ h n ∈ P x` by
    `n⁻¹ (h⁻¹ k m) n ∈ P x`, which comes from `inv_conj_mem`.
- `IsStabilizerCompatible N P` is `∀ n x, (n : H) ∈ P x → n • x = x`: elements of
  `N ∩ P_x` fix `x`. It is used only for injectivity of the canonical apartment map.

## The quotient and its action

- `CovariantSubgroupFamily N A` is a structure with fields `toFun : A → Subgroup H`
  and `isConjCovariant : IsConjCovariant N toFun`. It coerces to a function, so
  `P x` denotes `P.toFun x`. Its `setoid` is `apartmentRel N P`, an equivalence by
  `apartmentRel_equivalence`.
- `ApartmentQuotient P := Quotient P.setoid`, with class map
  `ApartmentQuotient.mk P (g, x)`.
- `mk_eq_mk_iff`: `mk P (g, x) = mk P (h, y) ↔ ∃ n : N, n • x = y ∧ g⁻¹ * h * n ∈ P x`.
  So the fibres of `H × A → ApartmentQuotient P` are exactly the classes of (4.4.2).
- `ApartmentQuotient.ind` is the induction principle on classes `mk P (g, x)`.
- The `MulAction H (ApartmentQuotient P)` instance is left multiplication on the
  first factor. `smul_mk : h • mk P (g, x) = mk P (h * g, x)` holds by definition.
  The action is well defined because `(h g)⁻¹ (h g') n = g⁻¹ g' n`. This needs no
  hypothesis beyond the relation itself; covariance is used only to form the quotient.

## The canonical apartment map

- `apartment P x := mk P (1, x)`.
- `mk_eq_smul_apartment : mk P (g, x) = g • apartment P x`, and
  `exists_smul_apartment`: every point of the quotient is `g • apartment P x` for
  some `g : H` and `x : A`.
- `apartment_smul : apartment P (n • x) = (n : H) • apartment P x` for `n : N`.
  The right side is `mk P (n, x)`. The relation `(n, x) ∼ (1, n • x)` holds with
  witness `n`, because `n⁻¹ * 1 * n = 1 ∈ P x`.
  `apartmentHom P : A →[N] ApartmentQuotient P` bundles this map, with `N` acting on
  the quotient through `H`.
- `apartment_eq_apartment_iff`:
  `apartment P x = apartment P y ↔ ∃ n : N, n • x = y ∧ (n : H) ∈ P x`.
- `apartment_injective_iff`: `Function.Injective (apartment P) ↔
  IsStabilizerCompatible N P`. `apartment_injective` is the direction used in
  practice. Without this condition the map need not be injective.

## The exact stabilizer

`MulAction.stabilizer H (apartment P x)` is the stabilizer of `[(1, x)]` for the
`H`-action. It is not `P x` in general.

- `mem_stabilizer_apartment_iff`:
  `h ∈ stabilizer H (apartment P x) ↔ ∃ n : N, n • x = x ∧ ∃ p ∈ P x, h = p * n`.
  So the stabilizer is the set of products `P_x · N_x`, where `N_x` is the
  `N`-stabilizer of `x`. This matches KP's form `G(k)_x = G(k)♮_x · N(k)_x`.
  In the proof, `h • [(1, x)] = [(1, x)]` gives `n` with `n • x = x` and
  `h n ∈ P x`. One then takes `p = h n` and the stabilizer element `n⁻¹`.
- `le_stabilizer_apartment : P x ≤ stabilizer H (apartment P x)`.
- `map_stabilizer_le_stabilizer_apartment`:
  `(MulAction.stabilizer N x).map N.subtype ≤ stabilizer H (apartment P x)`.
- `stabilizer_apartment_eq_sup`:
  `stabilizer H (apartment P x) = P x ⊔ (MulAction.stabilizer N x).map N.subtype`.
- `stabilizer_apartment_eq_iff`: the stabilizer equals `P x` iff every `n : N` with
  `n • x = x` has `(n : H) ∈ P x`. This is the extra condition needed to identify
  the full fixer with `P x`.

## Induced maps between quotients

Fix the same `H` and `N`. Take `N`-sets `A₁, A₂, A₃` with covariant families
`P₁, P₂, P₃`, and an `N`-equivariant map `f : A₁ →[N] A₂`. Assume
`hf : ∀ x, P₁ x ≤ P₂ (f x)`.

The inclusion is required for every `x`. One point does not suffice, because the
relation for `P₁` at an arbitrary `x` must be carried to the relation for `P₂` at
`f x`.

- `apartmentRel_map`: representative independence. `(g, x) ∼₁ (h, y)` implies
  `(g, f x) ∼₂ (h, f y)` with the same `n`, using `f (n • x) = n • f x` and `hf x`.
- `map P₁ P₂ f hf : ApartmentQuotient P₁ →[H] ApartmentQuotient P₂` is
  `[(g, x)] ↦ [(g, f x)]`. It is `H`-equivariant (`map_smul_eq`) and has these formulas:
  - `map_mk : map … (mk P₁ (g, x)) = mk P₂ (g, f x)`;
  - `map_apartment : map … (apartment P₁ x) = apartment P₂ (f x)`.
- `map_id`: the identity of `A` with `le_rfl` gives `MulActionHom.id H`.
- `map_comp`: `map` of `f'.comp f` (with the composed inclusions) is
  `(map P₂ P₃ f' hf').comp (map P₁ P₂ f hf)`.
- `map_surjective`: if `f` is surjective, so is `map P₁ P₂ f hf`.

None of these lemmas says that `map` is injective. The example
`not_injective_map_botFamily_topFamily` below shows that injectivity can fail when
`f` is the identity of a point and `P₁ x ≤ P₂ x` holds everywhere.

### Same apartment, larger family

Take `P, P'` on the same `A` with `hPP' : ∀ x, P x ≤ P' x`, and compare along the identity map.

- `map_id_injective_iff`: `map P P' (MulActionHom.id N) hPP'` is injective iff
  `P' x ≤ stabilizer H (apartment P x)` for every `x`.
- `map_id_bijective_iff`: the same condition is equivalent to bijectivity, since
  surjectivity always holds.
- `map_id_bijective_iff_le_sup`: by the stabilizer formula, the condition says
  `P' x ≤ P x ⊔ (MulAction.stabilizer N x).map N.subtype` for every `x`.

This is the abstract form of KP's remark after (4.4.2): `G(k)_x` may be replaced by
`G(k)♮_x` or any intermediate subgroup. Take `P = G(k)♮_•` and `P'` intermediate.
KP's identity `G(k)_x = G(k)♮_x · N(k)_x` is then the condition
`P' x ≤ P x ⊔ N_x`. The source identity itself is not proved here.

## Examples (`ApartmentQuotient.Example`)

All examples use the one-point apartment `Unit`, on which every action is trivial.

- `botFamily H N` is the constant family `⊥`; `topFamily H N` is the constant
  family `⊤`. Both are trivially covariant.
- `botFamily_isStabilizerCompatible`: `⊥` is stabilizer compatible.
- `stabilizer_botFamily_top`: for `N = ⊤` and `P = ⊥`, the stabilizer of
  `apartment (botFamily H ⊤) ()` is `⊤`, although `P () = ⊥`.
- `botFamily_lt_stabilizer`: for nontrivial `H`,
  `botFamily H ⊤ () < stabilizer H (apartment (botFamily H ⊤) ())`. Here `P_x` is
  properly smaller than the quotient-point stabilizer, while the canonical apartment
  map is injective (its domain is a point).
- `zmodTwo_botFamily_lt_stabilizer`: the same strict inclusion for the concrete group
  `H = Multiplicative (ZMod 2)`.
- `not_injective_map_botFamily_topFamily`: for nontrivial `H` and `N = ⊥`, the map
  `map (botFamily H ⊥) (topFamily H ⊥) (MulActionHom.id ⊥) _` is not injective,
  although it covers the identity of the apartment and `⊥ ≤ ⊤` holds at every
  point. The proof picks `h ≠ 1`: the classes `[(h, ())]` and `[(1, ())]` are
  distinct for `⊥` but have the same image for `⊤`. (Informally, the source is a
  copy of `H` and the target is a single point; Lean proves only the failure of
  injectivity.)

## Dictionary with Kaletha–Prasad and what remains

In KP Proposition 4.4.4:

- `B` is a building satisfying Axioms 4.1.1, 4.1.4 and 4.1.9.
- `H = G(k)`, and `N = N(k)` is the group of `k`-points of the normalizer of a
  maximal `k`-split torus `S`.
- `A` is the apartment of `S` (an affine space).
- `P x` is the stabilizer `G(k)_x` of `x` in `B`, or `G(k)♮_x`, or any intermediate
  subgroup.

The proposition then says that `G(k) × A → B, (g, x) ↦ g x` is surjective and
`G(k)`-equivariant, and that its fibres are the classes of (4.4.2). This module
proves only the algebra of that relation, for abstract data.

For the source data, the hypotheses here have the following status:

- Covariance holds in the source because the stabilizers in `B` satisfy
  `n G(k)_x n⁻¹ = G(k)_(n x)`.
- Stabilizer compatibility holds there because `A ⊂ B` is `N(k)`-equivariant.
- For the full stabilizer family, `N(k)_x ≤ G(k)_x`, so `stabilizer_apartment_eq_iff`
  gives back `G(k)_x`.

None of these facts is formalized here. A building has to be constructed first.

Still missing for KP's actual buildings:

- An actual building `B` with its `G(k)`-action and the apartment `A` of a maximal
  split torus. This includes the canonical affine apartment of Proposition 4.4.3,
  facets, and the reduced and enlarged buildings.
- An identification of `B` with `ApartmentQuotient P` as `G(k)`-sets. In KP this
  uses Definition 1.5.5(3), conjugacy of maximal split tori and Corollary 4.2.25.
- The subgroups `G(k)♮_x` and the parahoric subgroups `G(k)^0_x` (from parahoric
  integral models), and the theorems comparing them with `G(k)_x`. Examples are
  `G(k)_x = G(k)♮_x · N(k)_x` from the proof of Proposition 4.4.4 and
  `G(k)_x = G(k)^0_x · N(k)_x` from the proof of Proposition 4.4.6.
  The parahoric `G(k)^0_x` is a different object from `G(k)_x` and `G(k)♮_x`, and
  this module identifies none of them.
- The existence of buildings satisfying the axioms (KP Theorem 9.2.7).

**Corollary 4.4.5.** Use the corrected statement (KP corrections 2024, p. 29: "If
for every pair …", with "such that" deleted). It assumes `G(k)^0_(x₁) ⊂ G(k)^0_(x₂)`
for every pair of corresponding points `x₁ ∈ A₁`, `x₂ ∈ A₂` under the canonical
isomorphism of Proposition 4.4.3. The proof presents both buildings as quotients and
descends `id × (canonical isomorphism)` to a surjective `G(k)`-equivariant map
`B₁ → B₂`. That descent step is `map` with `f` the apartment isomorphism and `hf`
the universally quantified inclusion. Its surjectivity is `map_surjective`.

KP prove injectivity separately. They use an apartment `A′₁` containing any two given
points and the bijectivity of the map on each apartment. Respecting facets also needs
4.1.12. None of this geometry is formalized here, and the module does not claim the
building isomorphism.

## Provenance

The construction is derived from KP 2023 Proposition 4.4.4 (printed p. 183, relation
(4.4.2) and the remark that follows it) and from the quotient-map step in the proof of
Corollary 4.4.5 (printed pp. 183–184), with the correction to Corollary 4.4.5 in KP's
2024 corrections (p. 29).

The following are formulated here rather than taken from the source; they are the
hypotheses under which the abstract relation behaves as in the source:

- the covariance condition;
- the stabilizer-compatibility condition;
- the stabilizer formula for an arbitrary family;
- the comparison criteria;
- the examples.

All declarations use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
