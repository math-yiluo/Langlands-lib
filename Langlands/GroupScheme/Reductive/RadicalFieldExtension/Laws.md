# Normal law systems: descent of normal groups of points

Module `Langlands.GroupScheme.Reductive.RadicalFieldExtension.Laws`.

This module extends the law systems of `Langlands.GroupScheme.Absolute.BorelFieldExtensionDescent`
(namespace `BorelFieldExtension`). Those law systems record, by finitely many polynomial
identities, that the zero sets of finitely many families of functions form a solvable group
of points. Here two more pieces of data are added:

- a conjugation law: the first family stays in its ideal under conjugation by arbitrary
  points;
- finitely many fixed functions `u l ∈ H`, with coefficients in `k`, that lie in the ideal of
  the first family.

The proof of `AlgebraicallyClosedRadicalFieldExtensionStatement` uses this to move a normal
solvable group of `K`-points to a normal solvable group of `k`-points. The data are
internal to this proof and have no counterpart in the literature; they follow the pattern of
the existing law systems.

## Statements

Throughout, `k ⊆ K` are fields and `H` is a commutative Hopf algebra over `k`. Its `K`-points
are `k`-algebra maps `H → K`; `extPoint x : K ⊗[k] H → K` is the `K`-linear extension of a
point `x`.

- `tensor_eq_zero_of_separating₂`: if the families `χ₁` of `K`-algebra maps `Q₁ → K` and `χ₂`
  of `K`-algebra maps `Q₂ → K` each separate elements, then an element of `Q₁ ⊗[K] Q₂` that
  is killed by every product `χ₁ i ⊗ χ₂ i'` is zero.
- `baseMap_mem_map_includeRight`: suppose the `K`-points separate the elements of
  `K ⊗[k] H`, and let `w : H → H ⊗[k] H` be a law with `(x, y) ∘ w ∈ Γ₂` for every `K`-point
  `x` and every `y ∈ Γ₁`. Then `w` maps the vanishing ideal of `Γ₂` into the extension of the
  vanishing ideal of `Γ₁` along the second inclusion `H → H ⊗[k] H`.
- `eq_zero_of_forall_extPoint`: if `K` is algebraically closed, `H` is of finite type over
  `k`, and `K ⊗[k] H` is reduced, then the `K`-points separate the elements of `K ⊗[k] H`.
- `wConj`, `pairLift_comp_wConj`: the conjugation law `(x, y) ↦ x y x⁻¹` in the convolution
  group of `H → H ⊗[k] H`, and its evaluation at a pair of points.
- `rightFam`: the pullbacks of a family of functions along the second projection.
- `IsNormalLawSystem R n s u g`: `g` is a law system over `R` (`IsLawSystem R n s g`). In
  addition, conjugating each `g 0 i` by the law `wConj` gives an element of the ideal spanned
  by `rightFam (g 0)`, and each `1 ⊗ u l` lies in the ideal spanned by `g 0`.
- `extPoint_pairLift_eq_zero_right`: if `y` kills the family `v`, and the law `w` maps `t`
  into the ideal spanned by `rightFam v`, then `(x, y) ∘ w` kills `t` for every point `x`.
- `map_span_rightFam`: extending the ideal spanned by `v` along the second inclusion gives
  the ideal spanned by `rightFam v`.
- `exists_isNormalLawSystem`: let `H` be of finite type and `S` a solvable normal subgroup of
  the `K`-points. Suppose every member of `S` kills each `u l`, and the `K`-points separate
  `K ⊗[k] H`. Then the vanishing ideals of the derived series of `S` give a normal law
  system over `K`, and every member of `S` kills its first family.
- `IsNormalLawSystem.map`: normal law systems are stable under change of coefficients along
  `R → R'`.
- `IsNormalLawSystem.descend`: let `s` be finite and the index type of `u` finite. A normal
  law system over `K` comes from a normal law system over `k[F]` for some finite set
  `F ⊆ K`.
- `IsNormalLawSystem.normal`, `IsNormalLawSystem.apply_eq_zero`: for a normal law system
  over `k`, the `k`-points that kill the first family form a normal subgroup, and its
  members kill every `u l`.
- `exists_isPrime_lt_of_normal_solvable` (the algebraic core): assume the following.
  - `k` is algebraically closed and `H` is of finite type over `k`.
  - `S` is a solvable normal group of `K`-points whose members kill finitely many
    functions `u l ∈ H`.
  - The `K`-points separate `K ⊗[k] H`.
  - `Q ⊆ K ⊗[k] H` is a prime ideal, and an element lies in `Q` exactly when every member
    of `S` kills it.
  - `P` is a prime of `H`, every element of `Q` maps to zero in `K ⊗[k] (H/P)`, and
    `1 ⊗ p ∉ Q` for some `p ∈ P`.

  Then there are a prime `𝔭 < P` of `H` and a normal solvable subgroup `Γ` of the `k`-points
  of `H` with two properties: its members kill every `u l`, and it contains every `k`-point
  whose kernel contains `𝔭`.

## Proof

- `tensor_eq_zero_of_separating₂` expands `t` in a `K`-basis `b` of `Q₁`,
  `t = Σ b a ⊗ c a`. For each `i'`, the element `Σ χ₂ i' (c a) • b a` of `Q₁` is killed by
  every `χ₁ i`, so it is zero. Linear independence of `b` gives `χ₂ i' (c a) = 0` for all
  `i'`, so `c = 0`. This copies the proof of
  `RationalPointClosure.tensor_eq_zero_of_separating`, which uses one family on both sides.
- `baseMap_mem_map_includeRight`: let `I` be the vanishing ideal of `Γ₁` and `N` its
  extension to `K ⊗[k] (H ⊗[k] H)`. The map `Φ : K ⊗[k] (H ⊗[k] H) → (K ⊗[k] H) ⊗[K] (K ⊗[k] H)/I`
  has a left inverse `L` modulo `N`, that is, `L ∘ Φ` is the quotient map by `N`. The image
  `Φ (w f)` is killed by every `extPoint x ⊗ y` with `y ∈ Γ₁`. On `Φ`, this is evaluation at
  the point `(x, y) ∘ w ∈ Γ₂`, and `f` vanishes on `Γ₂`. The points of `Γ₁` separate
  `(K ⊗[k] H)/I`, so `tensor_eq_zero_of_separating₂` gives `Φ (w f) = 0`, and applying `L`
  gives the claim.
- `eq_zero_of_forall_extPoint`: `K ⊗[k] H` is of finite type over `K`, hence a Jacobson ring,
  so the zero ideal of the reduced ring `K ⊗[k] H` is the intersection of the maximal ideals.
  Each maximal ideal is the kernel of a `K`-point (`pointOfMaximal`, Nullstellensatz). That
  point is `extPoint x` for the restriction `x` of the point to `H`.
- `exists_isNormalLawSystem` follows `BorelFieldExtension.exists_isLawSystem`, with
  `Γ j` the `j`-th derived subgroup of `S`. Noetherianity gives finite generators `g j` of the
  vanishing ideals. The identity, product, inverse, commutator and final laws come from
  `baseMap_mem_pairIdeal`, as there. The conjugation law comes from
  `baseMap_mem_map_includeRight` with `Γ₁ = Γ₂ = S`, using normality of `S` and
  `pairLift_comp_wConj`. The fixed functions lie in the vanishing ideal of `S` by `hu`.
- `IsNormalLawSystem.map` maps each ideal membership along `coeffMap ψ`.
- `IsNormalLawSystem.descend` follows `BorelFieldExtension.IsLawSystem.descend`. Each of the
  finitely many ideal memberships, including the new conjugation and fixed-function
  conditions, is witnessed by finitely many coefficients (`eventually_coeffs`). A finite set
  `F` containing these coefficients and the coefficients of all `g j i` works.
  Membership over `k[F]` follows from injectivity of `coeffMap` along `k[F] ⊆ K`
  (`mem_span_of_injective`).
- `IsNormalLawSystem.normal`: if `z` kills `g 0`, then for every point `x` the conjugation
  law and `extPoint_pairLift_eq_zero_right` show that `x z x⁻¹` kills `g 0`.
  `IsNormalLawSystem.apply_eq_zero`: the kernel of `extPoint z` contains the span of `g 0`,
  hence each `1 ⊗ u l`.
- `exists_isPrime_lt_of_normal_solvable` follows
  `BorelFieldExtension.exists_isPrime_lt_of_solvable`. Choose a normal law system for `S`,
  descend it to a finitely generated subalgebra `k[F] ⊆ K`, and specialize along a
  `k`-algebra map `φ : k[F] → k`, which exists because `k` is algebraically closed. The prime
  `𝔭 < P` comes from `exists_isPrime_lt_specMap`. Then `Γ` is the group of `k`-points killing
  the first specialized family. It is normal and kills each `u l` by the two previous
  results. It is solvable because it lies in the solvable group from
  `exists_solvable_of_isLawSystem`. If a `k`-point kills `𝔭`, it kills the specializations of
  the first family, because those families lie in `Q`.
