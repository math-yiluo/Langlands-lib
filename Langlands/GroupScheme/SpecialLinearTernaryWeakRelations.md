# The ternary relations from weak root group relations

Module `Langlands.GroupScheme.SpecialLinearTernaryWeakRelations`, namespace
`Langlands.GroupScheme.SpecialLinear.TernaryPresentation`.

This internal module is group theory only: it has no schemes or functors. It
imports `Langlands.GroupScheme.SpecialLinearTernaryLift`. That module defines
the structure `TernaryRelations φ₁ φ₂`, which packages nine exact relations
between two homomorphisms `φ₁ φ₂ : SL₂(F) →* H`. It also proves
`TernaryRelations.exists_lift`: such a pair is the restriction of one
homomorphism `SL₃(F) →* H` to the two block copies `left` and `right`.

Some of the nine relations are hard to check directly in a group of rational
points: the commutator relation needs the exact constant, and the braid
relation needs the full Weyl element. This module replaces them by weaker
hypotheses:

- each commutator is required only up to an unspecified point of the third
  root group;
- root groups must be separated (no nontrivial point of one root group lies in
  another);
- the product of the two Weyl elements must conjugate one lower root group to
  the other.

From these hypotheses the module derives the exact relations. Everything is
proved in Lean; no literature result is used.

Notation, for homomorphisms `φ ψ : SL₂(F) →* H` into a group `H`, and with `F`
a field:
- `upper t = [1, t; 0, 1]` and `lower t = [1, 0; t, 1]`;
- `BinaryPresentation.diag u = diag(u, u⁻¹)`;
- `BinaryUpper.weylMatrix = w = [0, -1; 1, 0]`;
- `cornerPoint φ ψ t = φ(w) ψ(upper (-t)) φ(w)⁻¹`, from the imported module.
  For the two block embeddings of `SL₂` into `SL₃` this is the elementary
  matrix with entry `t` in position `(0, 2)`.

The option `backward.isDefEq.respectTransparency false` is set for the whole
file.

## Weyl element identities (section `WeylElement`)

- `upper_mul_lower_mul_upper`: for `s ≠ 0`,
  `upper s · lower (-s⁻¹) · upper s = diag s · w⁻¹` in `SL₂(F)`. This is
  checked entrywise.
- `upper_neg` (`upper (-s) = (upper s)⁻¹`) and `diag_neg_one_inv`
  (`diag(-1)⁻¹ = diag(-1)`).
- For a homomorphism `φ`, the following are images of matrix identities:
  `map_weyl_mul_weyl` (`φ(w)² = φ(diag(-1))`), `map_diag_neg_one_inv`,
  `map_lower_eq` (`φ(lower r) = φ(w)⁻¹ φ(upper (-r)) φ(w)`), `map_upper_eq`
  (`φ(upper s) = φ(w) φ(lower (-s)) φ(w)⁻¹`) and `map_diag_mul_weyl`
  (`φ(diag u) φ(w) = φ(w) φ(diag u⁻¹)`).
- `weyl_inv_conj`: conjugation by `φ(w)⁻¹` equals conjugation by
  `φ(diag(-1))` followed by conjugation by `φ(w)`.

## Exact commutator from weak data (section `Corner`)

Here `φ ψ : SL₂(F) →* H`. Some lemmas assume the torus hypothesis
`ht : φ(diag u) ψ(upper t) φ(diag u)⁻¹ = ψ(upper (u⁻¹ t))`. Under that
hypothesis:

- `cornerPoint_neg` and `weyl_inv_conj_cornerPoint`
  (`φ(w)⁻¹ cornerPoint φ ψ t φ(w) = ψ(upper (-t))`) need no hypothesis.
- `weyl_conj_cornerPoint`: `φ(w) cornerPoint φ ψ t φ(w)⁻¹ = ψ(upper t)`.
- `weyl_inv_conj_upper`: `φ(w)⁻¹ ψ(upper c) φ(w) = cornerPoint φ ψ c`.
- `torus_conj_cornerPoint_of`:
  `φ(diag u) cornerPoint φ ψ t φ(diag u)⁻¹ = cornerPoint φ ψ (u t)`.
- `commute_upper_cornerPoint_of` does not use `ht`. If every `φ(lower r)`
  commutes with every `ψ(upper c)`, then every `φ(upper s)` commutes with every
  corner point. This follows by conjugating with `φ(w)`.

The main lemma is `conj_upper_eq_of_weak`. Write `x(s) = φ(upper s)`,
`y(r) = φ(lower r)`, `p(c) = ψ(upper c)` and `q = cornerPoint φ ψ`. Assume:
- `ht`;
- `y` commutes with `p`;
- `p` commutes with `q`;
- the weak commutator: every `x(s) p(c) x(s)⁻¹` equals `p(c) q(f)` for some
  `f`;
- separation: `p(e) = q(d)` forces `p(e) = 1`.

Then `x(s) p(c) x(s)⁻¹ = p(c) q(s c)` exactly.

Proof, for `s ≠ 0` (the case `s = 0` is trivial):
1. Let `w_s = x(s) y(-s⁻¹) x(s)`. The first identity of the previous section
   gives `w_s = φ(diag s) φ(w)⁻¹`.
2. The torus and Weyl lemmas above then give the exact value
   `w_s p(c) w_s⁻¹ = q(s c)`.
3. Compute the same conjugate factor by factor. By the weak commutator,
   `x(s) p(c) x(s)⁻¹ = p(c) q(f₁)`. Conjugating by `y(-s⁻¹)` fixes `p(c)` and
   sends `q(f₁)` to `q(f₁) p(-f₂)`. This uses the weak commutator for
   `x(s⁻¹)` together with the Weyl conjugation formulas.
4. Use that `p` and `q` commute, then conjugate once more by `x(s)`. Here
   `x(s)` fixes `q(f₁)` by `commute_upper_cornerPoint_of`, and
   `x(s) p(c - f₂) x(s)⁻¹ = p(c - f₂) q(f₃)` by the weak commutator. This
   gives `w_s p(c) w_s⁻¹ = p(c - f₂) q(f₃) q(f₁)`.
5. Comparing with step 2 shows that `p(c - f₂) = q(s c - f₁ - f₃)` is a corner
   point. By separation it is trivial, so `q(f₃) = 1`.
6. Then step 4 reads `q(s c) = q(f₁)`, which gives the claim.

## Weak relations (section `Weak`)

`WeakTernaryRelations φ₁ φ₂` is a `Prop` structure with 13 fields. Write
`x₃ = cornerPoint φ₁ φ₂` and `x₃' = cornerPoint φ₂ φ₁`. The fields are:

- `torus_upper`: `φ₁(diag u) φ₂(upper t) φ₁(diag u)⁻¹ = φ₂(upper (u⁻¹ t))`;
- `torus_lower`: `φ₁(diag u) φ₂(lower t) φ₁(diag u)⁻¹ = φ₂(lower (u t))`;
- `torus_upper'`: the first relation with `φ₁` and `φ₂` exchanged;
- `weyl_torus`: `φ₁(w) φ₂(diag u) φ₁(w)⁻¹ = φ₁(diag u) φ₂(diag u)`;
- `commute_lower_upper` and `commute_lower_upper'`: `φ₂(lower r)` commutes with
  `φ₁(upper c)`, and `φ₁(lower r)` commutes with `φ₂(upper c)`;
- `commute_upper_corner` and `commute_upper_corner'`: `φ₂(upper c)` commutes with
  `x₃(t)`, and `φ₁(upper c)` commutes with `x₃'(t)`;
- `commute_corner`: `φ₁(upper s)` commutes with `x₃(t)`;
- `weak_commutator` and `weak_commutator'`:
  `φ₁(upper s) φ₂(upper c) φ₁(upper s)⁻¹ = φ₂(upper c) x₃(f)` for some `f`, and
  the same with `φ₁`, `φ₂` exchanged and `x₃'` in place of `x₃`;
- `separation` and `separation'`: `φ₂(upper e) = x₃(d)` implies
  `φ₂(upper e) = 1`, and the same with `φ₁`, `φ₂` exchanged and `x₃'` in
  place of `x₃`.

In `SL₃(F)` with the block embeddings, all of these hold. There `x₃(t)` and
`x₃'(-t)` are both the elementary matrix with entry `t` in position `(0, 2)`. The structure is an
internal hypothesis package, not a transcription of a source definition.

Consequences, in namespace `WeakTernaryRelations`:

- `conj_upper`: `φ₁(upper s) φ₂(upper c) φ₁(upper s)⁻¹ = φ₂(upper c) x₃(s c)`.
  This is `conj_upper_eq_of_weak`.
- `conj_upper'`: the same with `φ₁`, `φ₂` exchanged and `x₃'` in place of
  `x₃`.
- `commutator`: `φ₂(upper c) φ₁(upper s) φ₂(upper c)⁻¹ = φ₁(upper s) x₃(-(c s))`.
  This is the `commutator` field of `TernaryRelations`.
- `weyl_conj_upper'`: `φ₂(w) φ₁(upper t) φ₂(w)⁻¹ = x₃(t)`. It compares
  `conj_upper'` and `commutator` at `c = 1`.
- `lower_corner`: `φ₂(lower c) x₃(t) φ₂(lower c)⁻¹ = x₃(t) φ₁(upper (-(c t)))`.
  The proof writes `φ₂(lower c)` as a `φ₂(w)⁻¹`-conjugate of `φ₂(upper (-c))`.
- `weyl_mul_weyl_conj_upper`:
  `(φ₁(w) φ₂(w)) φ₁(upper t) (φ₁(w) φ₂(w))⁻¹ = φ₂(upper t)`.

The remaining results take the extra hypothesis `hlower`: for every `t`,
`(φ₁(w) φ₂(w)) φ₁(lower t) (φ₁(w) φ₂(w))⁻¹ = φ₂(lower t)`.

- `braid`: `φ₁(w) φ₂(w) φ₁(w) = φ₂(w) φ₁(w) φ₂(w)`. Proof: by
  `weyl_mul_weyl_conj_upper`, `hlower` and `BinaryPresentation.hom_ext`,
  conjugation by `φ₁(w) φ₂(w)` composed with `φ₁` equals `φ₂`. Evaluate this
  at `w`.
- `ternaryRelations`: the nine fields of `TernaryRelations φ₁ φ₂`. Six of them
  are copied (`torus_upper`, `torus_lower`, `weyl_torus`,
  `commute_upper_corner`, `commute_lower_upper`, `commute_corner`); the other
  three are `commutator`, `lower_corner` and `braid` above.
- `exists_lift`: there is `Φ : SL₃(F) →* H` with `Φ.comp left = φ₁` and
  `Φ.comp right = φ₂`. This is `TernaryRelations.exists_lift`.

## Provenance

Internal. `WeakTernaryRelations` is an auxiliary hypothesis package for the proof of
the Library statement `Langlands.GroupScheme.AdjacentSimpleRootSpecialLinearStatement`.
The trick of computing a conjugate by `x(s) y(-s⁻¹) x(s) = h(s) w⁻¹` in two ways
is the standard way commutator constants are fixed in Chevalley groups. It is
implemented here from scratch, and no source is cited.
