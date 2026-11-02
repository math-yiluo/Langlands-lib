import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Category.ConstituentDichotomy
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-!
# Cuspidality, cuspidal series and Aubert's support categories `Alg({I})`

For the generic standard families `P M U : Finset ι → Subgroup G` of
`Langlands.Aubert.General`, with actual normalized induction, normalized Jacquet
restriction and conjugation transport, this module defines:

* cuspidality relative to a family of semidirect decompositions, and its two
  instances: cuspidality for `G` (Aubert 1995, p. 2181, after [BZ, §2.4]) and for a
  standard Levi `M J` with the standard parabolics `(P I ∩ M J) = M I ⋉ (U I ∩ M J)`,
  `I ⊆ J`, of `leviAlternatingOperator`;
* the cuspidal series `𝔈(I)` of Aubert's Notation 1.6 (p. 2181);
* the full smooth support category `Alg({I})` of the 1996 erratum (p. 4687).

The Weyl association of the erratum, `v ∈ W` with `v(I) ⊆ S`, enters through a
relation `IsAssociate I J n` on index sets and elements of `G`, supplied by the
structural framework. The proved laws are intrinsic: closure of `Alg({I})` under
actual subquotients, isomorphisms and extensions, membership of the defining
inductions, and, when the identity represents `I ↦ I`, of `i^G_{L_I}(σ)` and of
`𝔈(I)`. No cuspidal-support theorem is asserted here.
-/

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uK uG uV

section Cuspidal

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H]

/-- Cuspidality relative to a family of semidirect decompositions `P k = M k ⋉ U k`
of `H`: the normalized Jacquet module along every member of the family vanishes. -/
def IsCuspidalFor {κ : Type uK} (P M U : κ → Subgroup H)
    (h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k))
    (hU : ∀ k, IsClosed (U k : Set H)) (A : SmoothRep.{0, uG, uV} ℂ H) : Prop :=
  ∀ k, Subsingleton ((jacquetFunctor.{uG, uV} (h k) (hU k)).obj A)

end Cuspidal

section Standard

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))

/-- Aubert, p. 2181 (after [BZ, §2.4]): a smooth representation of `G` is
cuspidal when `r^G_{L_I}(π) = 0` for every proper subset `I ⊊ S`, where `S` is
the full index set `Finset.univ`. -/
def IsCuspidal [Fintype ι] (A : SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  IsCuspidalFor (fun I : {I : Finset ι // I ≠ Finset.univ} => P I)
    (fun I => M I) (fun I => U I) (fun I => h I) (fun I => hU I) A

/-- Cuspidality for the standard Levi `M J`: `r^{M_J}_{M_I}(σ) = 0` for every
proper subset `I ⊊ J`. The parabolic of `M J` attached to `I ⊆ J` is
`(P I) ∩ M J = (M I) ⋉ (U I ∩ M J)`, read inside `M J`; these are the
decompositions `hJ` of `leviAlternatingOperator`. -/
def IsLeviCuspidal (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))
    (σ : SmoothRep.{0, uG, uV} ℂ (M J)) : Prop :=
  letI := hM.locallyCompactSpace
  IsCuspidalFor (fun I : {I : Finset J // I ≠ Finset.univ} => (P (leviIndex J I)).subgroupOf (M J))
    (fun I => (M (leviIndex J I)).subgroupOf (M J))
    (fun I => (U (leviIndex J I)).subgroupOf (M J)) (fun I => hJ I)
    (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val) σ

/-- Aubert's Notation 1.6, p. 2181: `π ∈ 𝔈(I)` when `π` is irreducible and is a
subquotient of a normalized induced representation `i^G_{L_I}(σ)` with `σ` an
irreducible cuspidal representation of the standard Levi `L_I = M I`. -/
def IsInCuspidalSeries (I : Finset ι) (hM : IsClosed (M I : Set G))
    (hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
    (π : SmoothRep.{0, uG, max uG uV} ℂ G) : Prop :=
  π.IsIrreducible ∧
    ∃ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
      σ.IsIrreducible ∧ IsLeviCuspidal P M U hU I hM hI σ ∧
        SmoothRep.IsSubquotient π
          ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ)

/-- The full smooth support category `Alg({I})` of the 1996 erratum, p. 4687: a
smooth representation `E` of `G` belongs to it when every irreducible
subquotient of `E` is a subquotient of an induced representation
`i^G_{L_{v(I)}}(Ad(v)(σ))`, where `σ` is an irreducible cuspidal representation of
the standard Levi `L_I = M I` and `v ∈ W` satisfies `v(I) ⊂ S ∩ Φ⁺`, that is
`v(I) ⊆ S`.

The pair `(v, v(I))` is encoded by `IsAssociate I J n`: the element `n` of `G`
represents a Weyl element `v` with `v(I) = J`. The membership condition `hn`
records `M J = n (M I) n⁻¹`, and `Ad(v)(σ)` is the conjugation transport
`x ↦ σ(n⁻¹ x n)`. No finite-length condition is imposed on `E`. -/
def IsInSupportCategory (IsAssociate : Finset ι → Finset ι → G → Prop) (I : Finset ι)
    (hM : IsClosed (M I : Set G))
    (hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
    (E : SmoothRep.{0, uG, max uG uV} ℂ G) : Prop :=
  ∀ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible → SmoothRep.IsSubquotient π E →
    ∃ (J : Finset ι) (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧
        ∃ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
          σ.IsIrreducible ∧ IsLeviCuspidal P M U hU I hM hI σ ∧
            SmoothRep.IsSubquotient π
              ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj
                ((conjugationFunctor n hn).obj σ))

variable {P M U h hU}
variable {IsAssociate : Finset ι → Finset ι → G → Prop} {I : Finset ι}
  {hM : IsClosed (M I : Set G)}
  {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
    ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}

/-- `Alg({I})` is closed under actual subquotients. -/
theorem IsInSupportCategory.of_isSubquotient {E F : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hE : IsInSupportCategory P M U h hU IsAssociate I hM hI E)
    (hFE : SmoothRep.IsSubquotient F E) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI F :=
  fun π hπ hπF => hE π hπ (smoothSubquotientTransitivity ℂ G E F π hπF hFE)

/-- `Alg({I})` is closed under isomorphism. -/
theorem IsInSupportCategory.of_iso {E F : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hE : IsInSupportCategory P M U h hU IsAssociate I hM hI E) (e : F ≅ E) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI F :=
  fun π hπ hπF => hE π hπ (hπF.of_iso_right e)

/-- `Alg({I})` is closed under extensions: if an invariant subrepresentation and
the corresponding quotient lie in it, so does the representation. -/
theorem IsInSupportCategory.of_subrepresentation_quotient
    {E : SmoothRep.{0, uG, max uG uV} ℂ G} (S : Subrepresentation E.representation)
    (hS : IsInSupportCategory P M U h hU IsAssociate I hM hI (SmoothRep.subrepresentation E S))
    (hQ : IsInSupportCategory P M U h hU IsAssociate I hM hI (SmoothRep.quotient E S)) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI E :=
  fun π hπ hπE => (SmoothRep.irreducibleSubquotient_dichotomy hπ hπE S).elim (hS π hπ) (hQ π hπ)

/-- Every normalized induction `i^G_{L_J}(Ad(v)(σ))` occurring in the definition
lies in `Alg({I})`. -/
theorem isInSupportCategory_inducedConjugate (J : Finset ι) (n : G)
    (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I) (hJ : IsAssociate I J n)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)) (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I hM hI σ) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI
      ((normalizedInductionFunctor.{uG, max uG uV} (h J) (hU J)).obj
        ((conjugationFunctor n hn).obj σ)) :=
  fun _ _ hπ => ⟨J, n, hn, hJ, σ, hσ, hc, hπ⟩

end Standard

section Identity

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation transport by the identity element is isomorphic to the identity:
the identity linear map intertwines `x ↦ σ(1⁻¹ x 1)` with `σ`. -/
noncomputable def conjugationFunctorOneIso {L : Subgroup G}
    (hn : ∀ x : G, x ∈ L ↔ (1 : G)⁻¹ * x * 1 ∈ L) (σ : SmoothRep.{0, uG, uV} ℂ L) :
    (conjugationFunctor 1 hn).obj σ ≅ σ :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) fun x => by
    have hx : conjugationEquiv 1 hn x = x := Subtype.ext (by simp)
    ext v
    change σ.representation (conjugationEquiv 1 hn x) v = σ.representation x v
    rw [hx])

end Identity

section Bridge

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
variable {IsAssociate : Finset ι → Finset ι → G → Prop} {I : Finset ι}
  {hM : IsClosed (M I : Set G)}
  {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
    ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}

/-- If the identity element represents the association `I ↦ I`, the normalized
cuspidal induction `i^G_{L_I}(σ)` lies in `Alg({I})`. -/
theorem isInSupportCategory_cuspidalInduction (hrefl : IsAssociate I I 1)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)) (hσ : σ.IsIrreducible)
    (hc : IsLeviCuspidal P M U hU I hM hI σ) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI
      ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).obj σ) := by
  have hn : ∀ x : G, x ∈ M I ↔ (1 : G)⁻¹ * x * 1 ∈ M I := fun x => by simp
  exact (isInSupportCategory_inducedConjugate I 1 hn hrefl σ hσ hc).of_iso
    ((normalizedInductionFunctor.{uG, max uG uV} (h I) (hU I)).mapIso
      (conjugationFunctorOneIso hn σ).symm)

/-- Under the same identity association, Aubert's cuspidal series `𝔈(I)` lies in
`Alg({I})`. -/
theorem IsInCuspidalSeries.isInSupportCategory (hrefl : IsAssociate I I 1)
    {π : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hπ : IsInCuspidalSeries P M U h hU I hM hI π) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI π := by
  obtain ⟨-, σ, hσ, hc, hπσ⟩ := hπ
  exact (isInSupportCategory_cuspidalInduction hrefl σ hσ hc).of_isSubquotient hπσ

end Bridge

end Langlands.Aubert.General
