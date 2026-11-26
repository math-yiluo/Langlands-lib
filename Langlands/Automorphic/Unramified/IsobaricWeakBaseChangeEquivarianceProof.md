# Equivariance of attached weak base change under compatible automorphisms

`Langlands.Automorphic.Unramified.isobaricWeakBaseChangeEquivariance` proves
`IsobaricWeakBaseChangeEquivarianceStatement` with its universe parameters
`uF, uE, uV, uW`. Let `E/F` be an extension of number fields, and let `τF` and `τE`
be ring automorphisms of `F` and `E` with `τE ∘ algebraMap = algebraMap ∘ τF`.
Suppose the isobaric data `DE` over `E` are a weak base change of `DF` over `F`.
Pull back every constituent of both data along the inverse automorphism, keeping
repetitions. Then the image of `DE` is again a weak base change of the image of `DF`.

The proof transports the given witnesses. Neither the field extension nor the
automorphisms are assumed Galois or cyclic.

## The implemented proof

The witness of `IsobaricData.IsWeakBaseChangeOf DE DF` consists of a rank equation
`h`, a system `s` attached to `DF`, a system `t` attached to `DE`, and the numerical
relation `SpectralSystem.IsArithmeticWeakBaseChangeOf (h ▸ t) s`. The proof
constructs a witness of the same form for the pulled-back data in four steps.

1. **Places above a base place.** Write `e : K ≃+* K'` and `f : L ≃+* L'` for
   isomorphisms of number fields that commute with the algebra maps `K → L` and
   `K' → L'`. `finitePlaceEquiv` sends a prime of `L'` to its preimage prime of `L`
   under `f`, and similarly for `e`.
   - `liesOver_finitePlaceEquiv_of_comm`: if `w` lies over `v`, then
     `finitePlaceEquiv f w` lies over `finitePlaceEquiv e v`. The proof restricts the
     commuting square to the rings of integers (`mapRingEquiv_algebraMap_of_comm`).
   - `inertiaDeg_finitePlaceEquiv_of_comm`: the residue degree of
     `finitePlaceEquiv f w` over `K` equals that of `w` over `K'`. The ring
     isomorphisms induce isomorphisms of the residue fields that are compatible with
     the residue field extensions, so `Algebra.finrank_eq_of_equiv_equiv` applies.
   - `ramificationIdx_finitePlaceEquiv_of_comm`: the ramification index of
     `finitePlaceEquiv f w` over `K` equals that of `w` over `K'`. In a Dedekind
     domain the ramification index is the multiplicity of the prime in the extended
     ideal. The isomorphism of ideal monoids induced by `f` preserves this
     multiplicity (`multiplicity_map_eq`), and it carries one extended ideal to the
     other.

   `finitePlaceEquiv_symm` identifies `finitePlaceEquiv g.symm` with
   `(finitePlaceEquiv g).symm`, and `map_finitePlaceEquiv_asIdeal` recovers a place
   from the ideal of its preimage.

2. **The numerical relation.**
   `SpectralSystem.IsArithmeticWeakBaseChangeOf.reindex_of_comm` shows the
   following. If `t` over `L` is an arithmetic weak base change of `s` over `K`, then
   `t.reindex (finitePlaceEquiv f).symm` over `L'` is an arithmetic weak base change of
   `s.reindex (finitePlaceEquiv e).symm` over `K'`.
   `finitePlaceEquiv e` is injective, so the cofinite set of good base places for
   `t, s` pulls back to a cofinite set of places `v` of `K'`. Fix such a `v` and a
   place `w` of `L'` above `v`. Then `finitePlaceEquiv f w` is a place of `L` above
   `finitePlaceEquiv e v`, where the hypothesis applies. The reindexed systems are
   defined at `v` and `w`, the ramification index is one, and the eigenvalue
   relation holds at `w`. For the last two, the exponent is rewritten with Step 1.

3. **Attachment to the pulled-back data.**
   `IsobaricData.HasSpectralSystem.reindex_arithmeticComap` assumes that `s` is
   attached to `D` over `L` and that `e : K ≃+* L`. It shows that `s` reindexed along
   `finitePlaceEquiv e`, after a cast to the rank of `D.arithmeticComap e`, is attached
   to `D.arithmeticComap e`. Unfolding the attachment of `s` gives an enumeration
   `σ` of the constituents, attached cuspidal systems `t j`, and cofinite agreement
   of Euler polynomials between `finiteSum t` and `s`. The pulled-back enumeration
   `j ↦ (σ j).arithmeticComap e` enumerates the pulled-back data
   (`IsobaricData.map_arithmeticComap_eq`). For each `j`, the published theorem
   `cuspidalSpectralArithmeticComap` attaches exactly `(t j).reindex (finitePlaceEquiv e)`
   to `(σ j).arithmeticComap e`, through the arithmetic pullback of an actual cuspidal
   presentation. The remaining agreement of Euler polynomials follows from three facts:
   - the finite sum of the reindexed systems has the Euler polynomials of the
     reindexed finite sum (`finiteSum_reindex_sameEulerPolynomials`);
   - reindexing preserves cofinite agreement (`SameEulerPolynomials.reindex`);
   - a rank cast changes no Euler polynomial (`sameEulerPolynomials_eqRec`).

4. **Assembly.** Step 3 is applied to `DF` with `τF.symm` and to `DE` with `τE.symm`.
   Step 2 is applied with `e = τF` and `f = τE`, where the compatibility hypothesis of
   the statement is the commuting square. `finitePlaceEquiv_symm` rewrites
   `(finitePlaceEquiv τ).symm` to `finitePlaceEquiv τ.symm`, so the systems from
   Steps 2 and 3 agree. The rank equation of the pulled-back data follows from
   `IsobaricData.rank_arithmeticComap` and `h`. After substitution of the rank
   equations, `isArithmeticWeakBaseChangeOf_eqRec_reindex` identifies the cast
   systems with the reindexed ones.

The proofs of the residue-degree, ramification-index and lies-over lemmas follow
arguments that `Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport`
contains as private lemmas, and that
`Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison` contains as
`Langlands.Global.Harris.finitePlaceEquiv_liesOver`. Here they are stated publicly
for primes with a lies-over instance. They are reproved so that this module does not
import those modules.

## Sources

The statement is the weak part of Arthur–Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120
(1989), Chapter 3, Proposition 4.4(iii), printed pp. 210–211 (PDF pp. 224–225). There,
`τ ∈ Gal(E/L)` for a diagram of Galois extensions `E ⊃ F ⊃ L` with `E/F` cyclic, and
`τ` and its restriction to `F` form the compatible pair. Weak base change is
Definition 1.1 with the Hecke eigenvalue relation (1.1), printed p. 199 (PDF p. 213):
at a place `w` above an unramified finite place `v`, the eigenvalues of the lift at
`w` are those of `π` at `v` raised to the residue degree. Arthur–Clozel deduce (iii)
from the local analogue in §1.6.2, through character identities of unramified
representations. The Lean proof transports relation (1.1) directly. It shows that the
compatible pair of automorphisms matches the places above each base place, with
their ramification indices and residue degrees. The statement covers any compatible
pair of automorphisms and isobaric data with several constituents. The registered
source is `arthur-clozel-1989-base-change`.
