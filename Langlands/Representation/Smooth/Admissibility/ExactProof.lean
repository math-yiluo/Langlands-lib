import Langlands.Representation.Smooth.Admissibility.ExactStatement
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Compact.SurjectivityProof
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Admissibility in a smooth short exact sequence

Fixed vectors of an arbitrary subgroup are exact in the middle of a short exact
sequence; compact-open averaging gives surjectivity on the right. Finite
generation then passes along the resulting exact sequences, and cofinality of
compact open subgroups extends it to every open subgroup.
-/

namespace Langlands

universe uG uU uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {U : Type uU} {V : Type uV} {W : Type uW}
variable [AddCommGroup U] [Module ℂ U]
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable {rho : Representation ℂ G U} {sigma : Representation ℂ G V}
  {tau : Representation ℂ G W}

/-- For every subgroup, the fixed vectors of an exact pair of intertwiners with
injective first map form an exact pair of linear maps. -/
theorem fixedVectorMap_exact [IsTopologicalGroup G] (i : rho.IntertwiningMap sigma)
    (p : sigma.IntertwiningMap tau) (hi : Function.Injective i)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (K : Subgroup G) :
    Function.Exact (Compact.fixedVectorMap rho sigma i K)
      (Compact.fixedVectorMap sigma tau p K) := by
  intro v
  constructor
  · intro hv
    have hker : v.val ∈ LinearMap.ker p.toLinearMap := congrArg Subtype.val hv
    rw [← hexact] at hker
    obtain ⟨u, hu⟩ := hker
    have hu' : i u = v.val := hu
    refine ⟨⟨u, ?_⟩, Subtype.ext hu'⟩
    change ∀ k : K, rho (k : G) u = u
    intro k
    apply hi
    rw [i.isIntertwining, hu']
    exact v.property k
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    change p (i u.val) = 0
    have hmem : i u.val ∈ LinearMap.range i.toLinearMap := ⟨u.val, rfl⟩
    rw [hexact] at hmem
    exact hmem

/-- In the short exact sequence, admissibility of the middle term is equivalent
to admissibility of both ends. -/
theorem isAdmissible_iff_of_shortExact [IsTopologicalGroup G]
    (hcofinal : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H)
    (i : rho.IntertwiningMap sigma) (p : sigma.IntertwiningMap tau)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (hsigma : IsSmooth sigma) :
    IsAdmissible sigma ↔ IsAdmissible rho ∧ IsAdmissible tau := by
  let S : Set (OpenSubgroup G) := {K | IsCompact (K : Set G)}
  have hS : ∀ H : OpenSubgroup G, ∃ K ∈ S, K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := hcofinal H
    exact ⟨K, hK, hKH⟩
  have htau : IsSmooth tau := isSmooth_of_surjective p hp hsigma
  have hsurj : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Function.Surjective (Compact.fixedVectorMap sigma tau p K.toSubgroup) :=
    fun K hK => Compact.fixedVectorSurjectivity.{uG, uV, uW} G V W sigma tau
      hsigma htau K hK p hp
  constructor
  · intro hadm
    refine ⟨isAdmissible_of_injective i hi hadm, ?_⟩
    rw [isAdmissible_iff_of_cofinal S hS]
    refine ⟨htau, fun K hK => ?_⟩
    let : Module.Finite ℂ (fixedVectors sigma K.toSubgroup) := hadm.2 K
    exact Module.Finite.of_surjective _ (hsurj K hK)
  · rintro ⟨hrho, htauAdm⟩
    rw [isAdmissible_iff_of_cofinal S hS]
    refine ⟨hsigma, fun K hK => ?_⟩
    let : Module.Finite ℂ (fixedVectors rho K.toSubgroup) := hrho.2 K
    let : Module.Finite ℂ (fixedVectors tau K.toSubgroup) := htauAdm.2 K
    exact Module.Finite.of_exact (fixedVectorMap_exact i p hi hexact K.toSubgroup)
      (hsurj K hK)

/-- Proof of `AdmissibleShortExactStatement`. -/
theorem admissibleShortExact :
    AdmissibleShortExactStatement (G := G) (U := U) (V := V) (W := W) := by
  intro _ hcofinal rho sigma tau i p hi hp hexact hsigma
  exact isAdmissible_iff_of_shortExact hcofinal i p hi hp hexact hsigma

end Langlands
