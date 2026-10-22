# Semisimplicity ascends from a normal subgroup of finite index

Author: Worker 261. This file states a proposition. It proves nothing and
assumes no theorem as data.

`Langlands.FiniteIndexSemisimplicityAscent` quantifies over:

- every field `R` of characteristic zero (`[Field R] [CharZero R]`), in
  universe `uR`;
- every group `G` in universe `uG`;
- every `R`-module `V` (`[AddCommGroup V] [Module R V]`) in universe `uV`;
- every subgroup `H : Subgroup G` with `[H.Normal]` and `[H.FiniteIndex]`;
- every representation `ρ : Representation R G V`.

The three universes are independent. The statement says: if
`Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)` holds, then
`Representation.IsSemisimpleRepresentation ρ` holds.

## Exact meaning of the terms

All terms are Mathlib's. Nothing is redefined here.

- `Representation R G V` is Mathlib's `G →* (V →ₗ[R] V)`.
- `ρ.comp H.subtype` composes `ρ` with the inclusion monoid homomorphism
  `H.subtype : H →* G`. It is the restriction of `ρ` to `H`, a representation
  of `H` on the same space `V`.
- `Representation.IsSemisimpleRepresentation ρ` is Mathlib's abbreviation for
  `ComplementedLattice (Subrepresentation ρ)`. So every subrepresentation of
  `ρ` has a complementary subrepresentation, which is the same as complete
  reducibility (see the provenance section). Mathlib's
  `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule` shows it is
  the same as semisimplicity of `ρ.asModule` over the group algebra `R[G]`.
- `Subgroup.Normal H` is Mathlib's normality: `H` is closed under
  conjugation by every element of `G`.
- `Subgroup.FiniteIndex H` is Mathlib's class `H.index ≠ 0`. Mathlib's
  `Subgroup.index` is `0` exactly when the index is infinite, so this says
  `G ⧸ H` is finite.
- `CharZero R` says the map from `ℕ` to `R` is injective. So the index of
  `H` is a nonzero, and hence invertible, element of `R`.

Nothing else is assumed: there is no topology on `G` and no smoothness. `G` need
not be finite, and `V` need not be finite-dimensional. There is no
irreducibility or finite-length hypothesis. The hypothesis `H.Normal` is part of
the statement, as in the source. The statement makes no claim about subgroups
that are not normal.

## Complex coefficients

Lemma 2.9(a) itself is the complex case. It is the instance
`FiniteIndexSemisimplicityAscent.{0, uG, uV}` at `R := ℂ`, because
`ℂ : Type` carries `Field` and `CharZero` instances. The group and carrier
universes `uG` and `uV` stay arbitrary. During development, an `example` that
applies `h : FiniteIndexSemisimplicityAscent.{0, uG, uV}` to
`ℂ G V H ρ` for an arbitrary `G : Type uG` and `V : Type uV` compiled in a
private draft. That check is not part of this file.

## Provenance

This is a derived statement. It is an algebraic generalization of a source
lemma whose coefficients are complex.

Source: I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys 31:3
(1976), 1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`,
SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Worker 261 read printed pages 15–17 (PDF pages 15–17) and page 37 in the
registered original.

- **Conventions (§2, p. 15).** Representations `(π, G, E)` act on complex
  vector spaces. The source says: "All vector spaces that we encounter are
  treated without any topology."
- **2.7 Lemma–Definition (p. 16).** A module `E` over a `ℂ`-algebra is
  *completely reducible* if it satisfies three equivalent conditions. One of
  them, 2.7(c), is: "Each submodule `E' ⊂ E` has an invariant complement
  `E''` such that `E = E' ⊕ E''`." This condition is Mathlib's
  `ComplementedLattice (Subrepresentation ρ)`, and so it is
  `IsSemisimpleRepresentation`.
- **2.9 Lemma (a) (p. 17).** "Let `G` be a group, `H` a normal subgroup of `G`
  of finite index, and `(π, G, E)` a representation. a) If `π|H` is completely
  reducible, then `π` is also completely reducible." Here `G` is an arbitrary
  group, with no topology. Part (b), about irreducible `π`, is not stated
  here.
- **Proof of 2.9(a) (p. 17).** Take coset representatives `g₁, …, g_l` of
  `G/H`. A `G`-submodule `E₁` has an `H`-complement `E₁'`. Let `A` be the
  projection onto `E₁` along `E₁'`. Set
  `A₀ = (1/l) Σᵢ π(gᵢ) A π(gᵢ)⁻¹`. Then `A₀` projects `E` onto `E₁` and
  commutes with `G`. So `Ker A₀` is a `G`-invariant complement of `E₁`.

The step from `ℂ` to any field of characteristic zero is our own
generalization. It is not a quotation. The averaging only divides by the index
`l = |G/H|`, and `l` is invertible in every field of characteristic zero. The
rest of the argument is linear algebra that holds over any field. It needs no
dimension bound, and the index is finite by `H.FiniteIndex`. The universe
independence is also our own formal generality. The intended proof is the
source's averaging argument over `R`. That route explains the statement. It is
not a proof shipped with it; the proof is a separate task.

## Use in BZ76 Proposition 3.30(2)

Proposition 3.30 (p. 37) says that an irreducible cuspidal subfactor of an
admissible `E` is isomorphic to a submodule of `E`, and also to a factor
module. Step (2) treats the case where `π(z)` is scalar for all `z` in the
center `Z`: "Then `E` is a completely reducible `G°·Z`-module, and since
`G°·Z` has finite index in `G`, `E` is completely reducible as a `G`-module
(see 2.9). The required assertion follows immediately from this."

This statement is the 2.9(a) step there. Take `H` to be the subgroup
`G° · Z`. It is normal in `G` because `G°` is normal and `Z` is central. A
consumer applies the statement to the underlying `Representation` of a smooth
representation. Lemma 2.9 uses no topology, so smoothness plays no role in
this step. Finite index of `G° · Z`, and the complete reducibility of the
restriction from step (1), are separate inputs. They are not part of this
statement. This file does not state Proposition 3.30 or any cuspidality or
admissibility result.

## Dependencies

The file imports `Mathlib.GroupTheory.Index` (for `Subgroup.FiniteIndex`) and
`Mathlib.RepresentationTheory.Semisimple` (for
`Representation.IsSemisimpleRepresentation`). It imports no Library module and
modifies no published pair. Lean service environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
