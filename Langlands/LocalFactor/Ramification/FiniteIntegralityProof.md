# Integrality of the Artin and Swan conductors of a finite Galois representation

Module `Langlands.LocalFactor.Ramification.FiniteIntegralityProof`, namespace
`Langlands.Ramification.Padic`; auxiliary declarations in
`Langlands.Ramification.Padic.FiniteIntegrality`.

This module proves the published proposition
`Langlands.Ramification.Padic.FiniteGaloisConductorIntegralityStatement` (module
`Langlands.LocalFactor.Ramification.FiniteStatement`). The theorem is
`Langlands.Ramification.Padic.finiteGaloisConductorIntegrality`.

## Statement proved

For every prime `p`, every p-adic field `F : PadicField.{uL} p` with topological data `T`, every
field `K : Type uK` in the scalar tower `ℚ_p → K → F`, and every finite-dimensional complex vector
space `V : Type uV` (the three universes independent): if `F/K` is Galois, then for every
representation `ρ` of `G = F.Carrier ≃ₐ[K] F.Carrier` on `V`, the Artin and Swan expressions of
`ρ` are natural numbers.

```lean
theorem Langlands.Ramification.Padic.finiteGaloisConductorIntegrality.{uK, uL, uV}
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorIntegralityStatement T K (V := V)
```

where the statement unfolds to

```lean
∀ [IsGalois K F.Carrier] (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V),
  (∃ a : ℕ, artinConductor T K ρ = (a : ℚ)) ∧ (∃ s : ℕ, swanConductor T K ρ = (s : ℚ))
```

The binders are those of the statement in its order: `{p} [Fact p.Prime] {F} (T) (K)`, the
three instances on `K`, then `{V}` with its instances. `artinConductor T K` and
`swanConductor T K` are the Library's rational sums
`Σ_{i≥0} |G_i|/|G_0| · codim V^{G_i}` and `Σ_{i≥1} …` for the action of `G` on the integers of
`F` (module `Langlands.LocalFactor.Ramification.Galois`).

## Proof outline

1. *The functional.* With the integer-ring action of `G` installed,
   `virtualArtin T K : VirtualRep ℂ G →+ ℂ` is the Artin functional
   `f ↦ |G_0|⁻¹ Σ_g i_G(g)(f 1 − f g)` (`Ramification.artinFunctional`, module
   `Langlands.LocalFactor.Ramification.ConductorFunctional`) composed with the character
   `FiniteRep.virtualCharacter`. On the class of a representation `σ` it is `a_K(σ)`
   (`virtualArtin_ofClassOfRepresentation`, from `artinFunctional_character` and
   `FiniteRep.character_classOfRepresentation`); on the trivial representation it is `0`
   (`virtualArtin_one`: the character is constant).
2. *The generators.* Deligne's degree-zero form of Brauer's theorem in the Library,
   `FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer`, says that the virtual representations of
   degree zero are the integral span of the classes
   `virtualInduce S ([oneDimensional χ] − [oneDimensional χ'])` for subgroups `S` and characters
   `χ, χ'` of `S`. On such a class the functional is
   `a_K(Ind_S χ) − a_K(Ind_S χ')` (the induced class is the class of Mathlib's
   `Representation.ind S.subtype`, by the definitions of `FiniteRep.induce` and
   `FiniteRep.induceRep`), an integer by `exists_int_artinConductor_ind_sub` (module
   `Langlands.LocalFactor.Ramification.InducedRankOneDifference`).
3. *Span induction.* The preimage under the functional of the image of `ℤ` is a subgroup; it
   contains the generators, hence their span (`Submodule.span_le`), hence
   `x = [ρ] − (dim V) · [1]`, which has degree `χ_ρ(1) − dim V = 0`
   (`Representation.char_one`, `FiniteRep.character_oneDimensional`). Its value is
   `a_K(ρ) − dim V · 0 = a_K(ρ)`. So `a_K(ρ)` is an integer `z` (`exists_int_artinConductor`).
4. *Natural numbers.* `a_K(ρ) ≥ 0` (`Padic.artinConductor_nonneg`), so `a_K(ρ) = z.toNat`. By
   `Padic.artinConductor_eq_tame_add_swan`, `sw_K(ρ) = a_K(ρ) − c` with
   `c = codim V^{G_0} ∈ ℕ`, and `sw_K(ρ) ≥ 0` (`Padic.swanConductor_nonneg`), so `c ≤ z.toNat`
   and `sw_K(ρ) = z.toNat − c`.

## Declarations, in order

In `Langlands.Ramification.Padic.FiniteIntegrality`, for `T` and `K` as above:

- `virtualArtin T K [Fintype G] : VirtualRep ℂ G →+ ℂ`.
- `virtualArtin_ofClass`, `virtualArtin_ofClassOfRepresentation`, `virtualArtin_one`.
- `exists_int_artinConductor [IsGalois K F.Carrier] (ρ) : ∃ z : ℤ, artinConductor T K ρ = (z : ℚ)`.

In `Langlands.Ramification.Padic`:

- `finiteGaloisConductorIntegrality` — the statement above.

## Relation to the integrality theorem for Weil representations

The Library's integrality theorems for Weil representations over a p-adic field are derived
from this one. `Langlands.LocalFactor.Ramification.ArtinExponent` extends it to representations
of the inertia group, the form in which presentations of Weil representations use the conductor:
it applies `finiteGaloisConductorIntegrality` over the fixed field of inertia, over which the
extension is Galois (`Padic.exists_nat_inertiaArtinConductor`,
`Padic.exists_nat_inertiaSwanConductor`, `Padic.exists_nat_artinConductorOfQuotient`,
`Padic.exists_nat_swanConductorOfQuotient`). From these,
`Langlands.Henniart.weilConductorIntegrality` (module
`Langlands.Correspondence.HenniartWeilConductorIntegralityProof`) proves that every finite inertia
presentation with surjective inertia restriction of a representation of the local Weil group has
natural Artin and Swan expressions, and that every continuous representation has such a
presentation. `Langlands.Henniart.weilArtinConductorExistence` (module
`Langlands.Correspondence.HenniartWeilArtinConductorExistenceProof`: every irreducible Weil class
over a p-adic field has some finite inertia presentation whose Artin expression is a natural
number) is the second clause of `weilConductorIntegrality` applied to a representative of the
class. The argument of this module works with the finite Galois group itself, so no continuity,
common closure or choice of a presenting field enters, and the conclusion holds for every
representation of the Galois group. Rank one comes from the Hasse–Arf theorem
(`Langlands.LocalFactor.Ramification.RankOneConductorIntegrality`).

## Sources

Serre, *Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`): Theorem 1′
(printed page 99) is the Artin half; Proposition 2 and Corollary 1′ (pages 100–101) identify the
conductor with the weighted codimension sum, which is the Library's definition; Proposition 4
with its corollary (page 101) is the induction formula; the proof of Theorem 1′ (page 102) reduces
to induced characters by Brauer's theorem. Deligne, *Les constantes des équations fonctionnelles
des fonctions L* (1973) (literature ID `deligne-1973-local-constants`): Proposition 1.5 (printed
page 510), the degree-zero form of Brauer's theorem, which lets the term `dim ψ · a(Ind 1)` of the
Library's induction formula cancel; §4.5, equation (4.5.4) (printed page 538), Artin as Swan plus
the inertia codimension, for the Swan half.

The argument was compared with `ArtinConductorBrauer.lean` of the repository `riemann-hypothesis`
at commit `f1f6d65`, which proves the theorem through the Artin character and the different; no
text is taken from it.
