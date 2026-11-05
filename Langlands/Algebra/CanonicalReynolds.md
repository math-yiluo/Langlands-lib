# Canonical Reynolds operators of semisimple representations

This module is an internal derivation from Mathlib's semisimple
representations (`Representation.IsSemisimpleRepresentation`, which means
that every subrepresentation has a complement), invariants
(`Representation.invariants`) and graded algebras. It formalizes the classical
Reynolds-operator argument of invariant theory. A semisimple representation
splits as its invariants plus the span of all differences `ρ g v - v`. The
projection onto the invariants along this span is a canonical Reynolds
operator. For a group acting on a commutative algebra this operator yields
Hilbert's finite generation of invariants, lying over for the invariant
subalgebra, and separation of stable comaximal ideals. The module identifies
no theorem from the literature. Hilbert's 1890 finiteness theorem and the
treatment in geometric invariant theory are background only.

Throughout, `k` is a field and `G` a group, both in arbitrary universes. No
topology, finiteness of `G` or finite dimension is assumed. Everything is in
the namespace `Langlands.Algebra.CanonicalReynolds`.

## Linear part

Let `ρ : Representation k G V`.

- `differenceSpan ρ N` is the `k`-span of the vectors `ρ g v - v` for
  `g : G` and `v ∈ N`.
- `IsStable ρ N` means `ρ g v ∈ N` for all `g` and all `v ∈ N`. This is a
  `Prop` on submodules, so it does not use the `Subrepresentation` structure.
- Elementary facts: `sub_mem_differenceSpan`, `differenceSpan_mono`,
  `isStable_top`, `isStable_invariants`, `IsStable.inf`, `differenceSpan_le`
  (the difference span of a stable subspace lies inside it) and
  `isStable_differenceSpan`. The last one uses
  `ρ g (ρ h v - v) = (ρ (g h) v - v) - (ρ g v - v)`.
- `apply_of_mem_invariants` restates membership in `ρ.invariants`.

The remaining linear results assume `[IsSemisimpleRepresentation ρ]`, except
where stated otherwise.

- `exists_isStable_isCompl`: every stable subspace has a stable complement.
  This rephrases the complemented-lattice hypothesis for submodules.
- `differenceSpan_le_of_isCompl` (no semisimplicity needed): let `N` and `Q`
  be stable with `Q` a complement of `N ⊓ ρ.invariants`. Then the difference
  span of `N` lies in `Q ⊓ N`. Writing `v = p + q` with `p` invariant gives
  `ρ g v - v = ρ g q - q`.
- `le_invariants_sup_differenceSpan`: for stable `N`,
  `N ≤ (N ⊓ ρ.invariants) ⊔ differenceSpan ρ N`. The proof takes a stable
  complement `Q` of `N ⊓ ρ.invariants` and a stable complement `Q'` of the
  difference span. Let `c ∈ Q ⊓ N`, decomposed as `a + q'` with `a` in the
  difference span and `q' ∈ Q'`. Then `q'` lies in `Q ⊓ N`, and
  `ρ g q' - q'` lies in both the difference span and `Q'`, so `q'` is
  invariant. Hence `q'` lies in `(N ⊓ ρ.invariants) ⊓ Q = 0`. So
  `Q ⊓ N` lies in the difference span, which gives the inclusion.
- `disjoint_invariants_differenceSpan` and
  `isCompl_invariants_differenceSpan`: the invariants and
  `differenceSpan ρ ⊤` are complementary submodules.
- `reynolds ρ : V →ₗ[k] V` (requires semisimplicity) is Mathlib's
  `Submodule.projection` onto `ρ.invariants` along `differenceSpan ρ ⊤`.

Properties of `reynolds ρ`:

- `reynolds_mem_invariants`, `reynolds_of_mem_invariants`,
  `sub_reynolds_mem` (`v - reynolds ρ v` lies in the difference span) and
  `reynolds_eq_zero_iff` (the kernel is the difference span).
- `reynolds_eq_of`: if `w` is invariant and `v - w` lies in
  `differenceSpan ρ ⊤`, then `reynolds ρ v = w`.
- `reynolds_apply`: `reynolds ρ (ρ g v) = reynolds ρ v`.
- `reynolds_mem`: `reynolds ρ` maps every stable subspace `N` into `N`.
  This follows from `le_invariants_sup_differenceSpan` and `reynolds_eq_of`.
- `apply_reynolds_of_invariant`: let `ψ : V →ₗ[k] M` satisfy
  `ψ (ρ g v) = ψ v` for all `g` and `v`. Then `ψ (reynolds ρ v) = ψ v`.
- `map_differenceSpan_le` (no semisimplicity needed) and `map_reynolds`: let
  `σ : Representation k G W` be semisimple too, and let `φ : V →ₗ[k] W`
  satisfy `φ (ρ g v) = σ g (φ v)`. Then
  `φ (reynolds ρ v) = reynolds σ (φ v)`.
- `isSemisimpleRepresentation_of_surjective`: if `ρ` is semisimple and
  `φ : V →ₗ[k] W` is equivariant and surjective, then `σ` is semisimple. The
  image of a stable complement of the preimage of a subrepresentation is a
  complement of that subrepresentation.

## Algebras

Now `A` is a commutative `k`-algebra and `ρ : Representation k G A`.

- `IsMultiplicative ρ` (a `Prop`-valued structure) means `ρ g 1 = 1` and
  `ρ g (a * b) = ρ g a * ρ g b` for all `g`, `a`, `b`. Thus the group acts by
  `k`-algebra endomorphisms.
- `invariantSubalgebra hρ : Subalgebra k A`, for `hρ : IsMultiplicative ρ`,
  has carrier `ρ.invariants`. `mem_invariantSubalgebra` records this.

With `[IsSemisimpleRepresentation ρ]`:

- `reynolds_mul_left`: for invariant `f`,
  `reynolds ρ (f * a) = f * reynolds ρ a`. This is `map_reynolds` applied to
  left multiplication by `f`, which is equivariant. `reynolds_one` gives
  `reynolds ρ 1 = 1`.
- `comap_map_ideal`: extending an ideal `I` of the invariant subalgebra to
  `A` and contracting it back returns `I`. If an invariant `x` equals
  `∑ fᵢ yᵢ` with `fᵢ ∈ A` and `yᵢ ∈ I`, then applying `reynolds ρ` gives
  `x = ∑ reynolds ρ (fᵢ) yᵢ`.
- `exists_algHom_comp_val_eq` (lying over for rational points): assume
  `k` is algebraically closed and `A` is of finite type over `k`. Then every
  `k`-algebra homomorphism `χ` from the invariant subalgebra to `k` is the
  restriction of a `k`-algebra homomorphism `ψ : A →ₐ[k] k`. The kernel of
  `χ` is maximal. By `comap_map_ideal`, its extension to `A` is proper, so it
  lies in a maximal ideal `M`. The residue field `A ⧸ M` is finite over `k`
  because `k` is a Jacobson ring and `A ⧸ M` is of finite type. Since `k` is
  algebraically closed, `k → A ⧸ M` is bijective. The required `ψ` is the
  quotient map followed by the inverse of this bijection.
- `exists_invariant_mem_sub_one_mem` (separation): let `I` and `J` be ideals
  of `A`, each stable as a `k`-subspace, with `I ⊔ J = ⊤`. Then some
  invariant `f` satisfies `f ∈ I` and `f - 1 ∈ J`. Write `1 = i + j` and
  take `f = reynolds ρ i`. Then `f - 1 = reynolds ρ (-j)` by `reynolds_one`,
  and `reynolds_mem` keeps both values in their ideals.
- `map_invariantSubalgebra_eq`: let `σ` be a multiplicative representation on
  a commutative `k`-algebra `B`. Let `φ : A →ₐ[k] B` be surjective with
  `φ (ρ g a) = σ g (φ a)`. Then `φ` maps the invariant subalgebra of `ρ` onto
  that of `σ`. Only `ρ` is assumed semisimple; `σ` is semisimple by
  `isSemisimpleRepresentation_of_surjective`, and `map_reynolds` lifts each
  invariant of `σ`.

## Graded algebras: Hilbert's finiteness theorem

Let `𝒜 : ℕ → Submodule k A` be a grading (`GradedAlgebra 𝒜`).

- `proj_apply_rep`: if every `𝒜 d` is stable, then the degree-`d` component
  of `ρ g x` is `ρ g` applied to the degree-`d` component of `x`. The proof
  is by induction on `x` through homogeneous elements.
- `invariantSubalgebra_fg`: assume the following.
  1. `ρ` is semisimple and multiplicative.
  2. Every `𝒜 d` is stable.
  3. `A` is a Noetherian ring.
  4. Every element of `𝒜 0` is a scalar `algebraMap k A c`.

  Then the invariant subalgebra is finitely generated as a `k`-algebra
  (`Subalgebra.FG`).

  Proof. Let `S` be the set of invariants that are homogeneous of positive
  degree. The ideal of `A` spanned by `S` is finitely generated, hence spanned
  by a finite subset `T ⊆ S`. By strong induction on `d`, every invariant
  `a ∈ 𝒜 d` lies in `Algebra.adjoin k T`. For `d = 0`, `a` is a scalar. For
  `d > 0`, write `a = ∑ fₜ t` and take degree-`d` components. Applying
  `reynolds ρ` and `reynolds_mul_left` gives
  `a = ∑ reynolds ρ (fₜ of degree d - deg t) * t`, with the terms with
  `deg t > d` equal to zero. Each coefficient is an invariant of degree
  `d - deg t < d`, by `reynolds_mem` for the stable subspace `𝒜 (d - deg t)`,
  so the induction hypothesis applies. Finally every homogeneous component of
  an invariant is invariant, by `proj_apply_rep`.

## Scope

The module does not prove that any particular representation is semisimple.
In applications this must be supplied, for example from complete reducibility
of finite-dimensional representations together with local finiteness. It also
constructs no quotient variety and no closed orbit.
