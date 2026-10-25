# The norm of an included idele class, and lifting ideles through the norm

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves two
facts about the published maps on Mathlib's actual adeles, ideles and idele
classes of number fields: the norm-of-inclusion power law, and a criterion
for an idele of `K` to be a norm from `L`. It imports
[IdeleClassNormLawsStatement](IdeleClassNormLawsStatement.md) and
[FinitePlaceDegreeTransfer](FinitePlaceDegreeTransfer.md) and changes none of
the imported definitions. Throughout, `K : Type u` and `L : Type v` are number
fields in independent universes with `Algebra K L`.

## The norm-of-inclusion power law

- `completionMap_under_eq p q x`: for a finite place `q` of `L` lying over `p`,
  the completed embedding `FiniteExtension.completionMap (q.under (𝓞 K)) q`,
  applied to the coordinate of `x` at `q.under (𝓞 K)`, equals
  `FiniteExtension.completionMap p q (x p)`. These are the maps used by
  [Inclusion](Inclusion.md) and by the local norms of [Norm](Norm.md); the proof
  substitutes the equality `q.under (𝓞 K) = p` and closes by `rfl`.
- `infiniteCompletionMap_comap_eq p q x`: the infinite analogue. For an infinite
  place `q` of `L` lying over `p`, `infiniteCompletionMap (algebraMap K L) q`
  applied to `x (q.comap (algebraMap K L))` equals Mathlib's
  `NumberField.LiesOver.completionMap (x p)`; after substituting
  `InfinitePlace.LiesOver.comap_eq q p`, the two maps agree definitionally.
- `finiteAdeleNorm_finiteAdeleInclusion x`: `finiteAdeleNorm (finiteAdeleInclusion x)
  = x ^ Module.finrank K L` for every finite adele `x` of `K`. At a place `p`,
  each factor is the local determinant norm of a base scalar, which is
  `x p ^ [L_q : K_p]` by `FiniteExtension.localNorm_algebraMap`; the product is
  `x p ^ Σ_q [L_q : K_p]`, and `finiteLocalDegree_sum` identifies the exponent
  with `[L : K]`.
- `infiniteAdeleNorm_infiniteAdeleMap x`: the same identity for infinite adeles,
  by `InfiniteExtension.localNorm_algebraMap` and `infiniteLocalDegree_sum`.
- `adeleNorm_adeleInclusion x` and `ideleNorm_ideleInclusion a`: the identity
  for adeles (componentwise) and for ideles (on underlying adeles).
- `ideleClassNormInclusionPower : IdeleClassNormInclusionPower.{u, v}`: for every
  idele class `x` of `K`,
  `ideleClassNorm (ideleClassInclusion x) = x ^ Module.finrank K L`. The proof
  reduces to representatives with `QuotientGroup.induction_on`,
  `ideleClassInclusion_mk` and `ideleClassNorm_mk`.

This proves exactly the published proposition
`IdeleClassNormInclusionPower` of
[IdeleClassNormLawsStatement](IdeleClassNormLawsStatement.md), at independent
universes `u, v`.

## Ideles from local units

For a number field `E : Type v`:

- `ideleOfLocalUnits a c hc hc'` is the idele with infinite coordinates the units
  `a w` of `w.Completion` and finite coordinates the units `c w` of
  `w.adicCompletion E`. The hypotheses `hc` and `hc'` say that `c w` and its
  inverse are integral at all but finitely many finite places, which is exactly
  what is needed for both to be finite adeles. The simp lemmas
  `ideleOfLocalUnits_infinite` and `ideleOfLocalUnits_finite` read off the
  coordinates of the underlying adele.
- `finiteUnitTransport h x` and `infiniteUnitTransport h x` transport a local
  unit along an equality `h` of finite, respectively infinite, places.
  `finiteUnitTransport_inv` and `finiteUnitTransport_mem_iff` say that transport
  commutes with inversion and preserves integrality.

## The lifting criterion

Fix choice functions `wf : ∀ p, FinitePlacesAbove L p` and
`wi : ∀ v, InfinitePlacesAbove L v`, choosing one place of `L` above every
place of `K`.

- `liftFiniteCoordinates wf c q` is the unit `c (q.under (𝓞 K))`, transported to
  `q`, when `q` is the chosen place above `q.under (𝓞 K)`, and `1` otherwise.
  `liftInfiniteCoordinates wi d w` is defined in the same way from
  `w.comap (algebraMap K L)`.
- `liftFiniteCoordinates_self` and `liftInfiniteCoordinates_self` give the value
  `c p`, respectively `d v`, at the chosen place; `liftFiniteCoordinates_of_ne`
  and `liftInfiniteCoordinates_of_ne` give `1` at every other place above `p`,
  respectively `v`.
- `liftFiniteCoordinates_eventually`: if `c p` and its inverse are integral for
  all but finitely many `p`, then the same holds for the lifted coordinates at
  all but finitely many `q`. The proof pulls the hypothesis back along
  `tendsto_under_cofinite`.
- `mem_range_ideleNorm_of_local wf wi a c hc hcn d hdn` is the criterion. Let
  `a` be an idele of `K`. Suppose that for every finite place `p` the local norm
  `FiniteExtension.localNorm p (wf p).1 (c p)` equals the `p`-coordinate of `a`,
  that for every infinite place `v` the local norm
  `InfiniteExtension.localNorm v (wi v).1 (d v)` equals the `v`-coordinate of
  `a`, and that the finite units `c p` satisfy the almost-everywhere integrality
  hypothesis above. Then `a` lies in the range of `ideleNorm`. The preimage is
  `ideleOfLocalUnits` of the lifted coordinates. At each place of `K`, the
  norm is a product over the places above it. All factors except the one at
  the chosen place are local norms of `1`, so `Finset.prod_eq_single` leaves
  the prescribed local norm.

## Sources and provenance

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Chapter VI §1, the first lemma on printed p.20 (PDF p.29), registered original
`artin-tate-2009-class-field-theory`. Its proof ends: "The norm index divides a
power of the degree because for any `a ∈ C_k`, `a^m ∈ N_{E/k} C_E`." The Lean
theorem `ideleClassNormInclusionPower` supplies this fact for the published
maps, with `m = Module.finrank K L`; the derivation from local degrees is the
one described in [IdeleClassNormLawsStatement](IdeleClassNormLawsStatement.md).
The same proof bounds `(J^S_k : N J^S_K)` by local norm indices. That bound
uses the fact that an idele whose coordinates are local norms is a global
norm. `mem_range_ideleNorm_of_local` is a Lean form of that fact. Its
formulation with one chosen place above each place, the idele constructor and
the transport maps are internal infrastructure for the Library maps; the cited
source does not mention them.
