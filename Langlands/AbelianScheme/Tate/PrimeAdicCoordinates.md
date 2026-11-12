# Compatible residue coordinates on the actual prime-adic Tate module

Author: Worker 3366.

The construction is pure algebra about the existing inverse system, carried out in namespace
`Langlands.GroupScheme.Tate.PrimeAdic.GeometricRank` for an arbitrary
commutative group object `G` over `S`, base object `T`, rank `r` and prime `p`.
The universe of `S` is arbitrary. The hypothesis `hL` is a residue-module equivalence from
`Fin r → ZMod (p ^ n)` to `Level G T (p ^ n)`, together with cardinality
`(p ^ n) ^ r`, for every level `n`.

1. **Kernel of a transition.** `levelInclusion` is the inclusion of the
   level-`p` torsion subgroup into level `p ^ (n + 1)`, and it is injective
   (`levelInclusion_injective`). Since a successive transition is
   multiplication by `p` on underlying sections
   (`toSection_transition_succ`), its kernel is exactly the image of this
   inclusion (`ker_transition_eq_range`).
2. **Transitions are surjective (`transition_surjective`).** The kernel
   has `p ^ r` elements by the count at level `p`. The first isomorphism
   theorem and Lagrange's theorem give
   `|range| · p ^ r = (p ^ (n + 1)) ^ r`, so the range has `(p ^ n) ^ r`
   elements, the whole of the finite level `p ^ n`
   (`finite_level`).
3. **Compatible residue bases (`exists_compatible_bases`).** A family
   `b : Fin r → Level G T (p ^ n)` is a *residue basis* (`IsResidueBasis`)
   when `Fintype.linearCombination (ZMod (p ^ n)) b` is bijective. The set
   `Bases G T p r n` of these is nonempty (the image of the standard basis
   under the given equivalence, `bases_nonempty`) and finite
   (`bases_finite`). A successive transition sends a residue basis to a
   residue basis (`isResidueBasis_transition`): its coordinate map is
   surjective because the transition is surjective and commutes with the
   residue actions (`transition_zmod_smul`), and a surjection between
   finite types of equal cardinality is bijective. These restriction maps
   form an inverse system `basisSystem : ℕᵒᵖ ⥤ Type u`
   (`Functor.ofOpSequence`) of finite nonempty sets, and Mathlib's
   Kőnig-type lemma `nonempty_sections_of_finite_inverse_system` produces
   residue bases `c n` at all levels with
   `transition (c (n + 1) i) = c n i`.
4. **`p`-adic coordinates.** `coordinates` is the `ℤ_[p]`-linear map
   `(Fin r → ℤ_[p]) → Integral G T p` obtained from the published universal
   property `lift` applied to the compatible maps
   `Fintype.linearCombination ℤ_[p] (c n)`; compatibility follows from
   `transition_smul` and the compatibility of the bases. Its level-`n`
   component is the residue coordinate map of `c n` applied to the
   residues `PadicInt.toZModPow n` of the coordinates
   (`evaluation_coordinates`, by definition).
   - *Injective* (`coordinates_injective`): if the image vanishes, every
     residue of every coordinate vanishes by injectivity of the residue
     coordinate maps, so each coordinate is zero by
     `PadicInt.ext_of_toZModPow`.
   - *Surjective* (`coordinates_surjective`): for a coherent sequence `x`,
     the residue coordinates `k n` of its components are compatible under
     the reductions `ZMod (p ^ (n + 1)) → ZMod (p ^ n)` by injectivity of the
     residue coordinate maps. `exists_padicInt` turns each compatible
     sequence of residues into a `p`-adic integer, via
     `PadicInt.ofIntSeq` and `PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub`
     applied to the representatives `(k n).val`. These integers are a
     preimage of `x`.

   `integral_linearEquiv` packages the bijection as
   `Nonempty ((Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p)`.

The shared rational-rank theorem is
`Langlands.GroupScheme.Tate.PrimeAdic.rational_finrank_of_linearEquiv` in
[PrimeAdicFreeness](PrimeAdicFreeness.md). Its identical copy was consolidated there.

This is the generic construction from the independently accepted geometric-rank proof.
The geometric specialization is in
[GeometricPrimeAdicRankProof](GeometricPrimeAdicRankProof.md), using the published
finite-level `geometricTorsionRank`. The construction here uses Kőnig's lemma and
`PadicInt.ofIntSeq`; `PrimeAdicFreeness` retains its separately reviewed residue-basis
predicate and construction through `PadicInt.lift`.

The chosen equivalence is noncanonical. No continuity, monodromy compatibility or
Weil-pairing normalization is asserted. The level hypothesis remains explicit.
The source context is Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter X
(10.3), as documented in [GeometricPrimeAdicRankStatement](GeometricPrimeAdicRankStatement.md).
