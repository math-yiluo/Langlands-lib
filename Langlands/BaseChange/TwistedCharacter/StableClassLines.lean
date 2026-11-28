import Langlands.BaseChange.TwistedInductionSpans
import Langlands.BaseChange.TwistedCharacter.EquivariantLine
import Langlands.BaseChange.TwistedCharacter.LinearIndependence
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.Classification.SegmentHeadJacquetReduction
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! # Twisted character distributions indexed by stable irreducible classes -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory MeasureTheory HarmonicAnalysis

universe uG z

section Classes

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The classes of irreducible admissible representations with carrier in universe `z` that
contain a representation with a twisting isomorphism for `θ`. -/
abbrev StableIrreducibleClass (θ : G ≃* G) :=
  {c : SmoothDualClass.{0,uG,z} (k := ℂ) (G := G) //
    ∃ A : IrreducibleAdmissibleRep.{0,uG,z} (k := ℂ) (G := G), SmoothDualClass.ofRep A = c ∧
    Nonempty (A.obj.representation.Equiv (A.obj.representation.comp θ.toMonoidHom))}

theorem smoothDualClass_ofRep_eq_iff {A B : IrreducibleAdmissibleRep.{0,uG,z} (k := ℂ) (G := G)} :
    SmoothDualClass.ofRep A = SmoothDualClass.ofRep B ↔
      Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  constructor
  · intro h
    obtain ⟨e⟩ : Nonempty (A ≅ B) := Quotient.exact h
    exact ⟨SmoothRep.equivOfIso
      ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)⟩
  · rintro ⟨e⟩
    apply Quotient.sound
    exact ⟨ObjectProperty.isoMk (irreducibleAdmissibleProperty (k := ℂ) (G := G))
      (SmoothRep.mkIso e)⟩

variable (θ : G ≃* G)

/-- The chosen representative of a stable class. -/
def StableIrreducibleClass.rep (c : StableIrreducibleClass.{uG,z} θ) :
    IrreducibleAdmissibleRep.{0,uG,z} (k := ℂ) (G := G) :=
  c.property.choose

/-- The chosen twisting isomorphism of the representative. -/
def StableIrreducibleClass.intertwiner (c : StableIrreducibleClass.{uG,z} θ) :
    (c.rep θ).obj.representation.Equiv
      ((c.rep θ).obj.representation.comp θ.toMonoidHom) :=
  c.property.choose_spec.2.some

theorem StableIrreducibleClass.ofRep_rep (c : StableIrreducibleClass.{uG,z} θ) :
    SmoothDualClass.ofRep (c.rep θ) = c.val :=
  c.property.choose_spec.1

/-- The class of an irreducible admissible representation with a twisting isomorphism. -/
def StableIrreducibleClass.mk {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : IsAdmissible π) (hirr : π.IsIrreducible)
    (A : π.Equiv (π.comp θ.toMonoidHom)) : StableIrreducibleClass.{uG,z} θ :=
  ⟨SmoothDualClass.ofRep ⟨SmoothRep.of π hπ.1, hirr, hπ⟩, ⟨SmoothRep.of π hπ.1, hirr, hπ⟩, rfl, ⟨A⟩⟩

theorem StableIrreducibleClass.nonempty_rep_equiv_mk {V : Type z} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : IsAdmissible π) (hirr : π.IsIrreducible)
    (A : π.Equiv (π.comp θ.toMonoidHom)) :
    Nonempty (((StableIrreducibleClass.mk θ π hπ hirr A).rep θ).obj.representation.Equiv π) :=
  smoothDualClass_ofRep_eq_iff (B := ⟨SmoothRep.of π hπ.1, hirr, hπ⟩) |>.mp
    (StableIrreducibleClass.ofRep_rep θ _)

theorem StableIrreducibleClass.eq_of_equiv (c d : StableIrreducibleClass.{uG,z} θ)
    (h : Nonempty ((c.rep θ).obj.representation.Equiv (d.rep θ).obj.representation)) : c = d :=
  Subtype.ext ((c.ofRep_rep θ).symm.trans
    ((smoothDualClass_ofRep_eq_iff.mpr h).trans (d.ofRep_rep θ)))

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- The twisted trace of the chosen representative of a stable class, with its chosen twisting
isomorphism. -/
def StableIrreducibleClass.trace (c : StableIrreducibleClass.{uG,z} θ) : Distribution G :=
  twistedDistribution μ (c.rep θ).obj.representation (c.rep θ).property.2
    (c.intertwiner θ).toLinearMap

/-- The twisted trace of an irreducible admissible representation, with any twisting
isomorphism, is a scalar multiple of the twisted trace of the chosen representative of its
class. -/
theorem twistedDistribution_eq_smul_stableIrreducibleClass_trace {W : Type z} [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ G W) (hπ : IsAdmissible π)
    (A : π.Equiv (π.comp θ.toMonoidHom)) (c : StableIrreducibleClass.{uG,z} θ)
    (hc : Nonempty ((c.rep θ).obj.representation.Equiv π)) :
    ∃ a : ℂ, twistedDistribution μ π hπ A.toLinearMap = a • c.trace θ μ :=
  exists_twistedDistribution_eq_smul_of_equiv μ θ (c.rep θ).property.2 (c.rep θ).property.1 hπ
    hc.some (c.intertwiner θ) A

end Classes

section Independence

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (θ : G ≃* G) (μ : Measure G) [μ.IsHaarMeasure]

theorem linearIndependent_stableIrreducibleClass_trace
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K) :
    LinearIndependent ℂ
      (fun c : StableIrreducibleClass.{uG,z} θ => StableIrreducibleClass.trace θ μ c) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  let A (i : s) : IrreducibleAdmissibleRep.{0,uG,z} (k := ℂ) (G := G) := i.val.rep θ
  let ρ (i : s) : Representation ℂ G (A i).obj := (A i).obj.representation
  let T (i : s) : (ρ i).Equiv ((ρ i).comp θ.toMonoidHom) := i.val.intertwiner θ
  exact twistedDistribution_linearIndependent μ θ hθ ρ (fun i => (A i).property.2)
    (fun i => (A i).property.1) (fun i j hij h => hij (Subtype.ext
      (StableIrreducibleClass.eq_of_equiv θ i.val j.val h)))
    (fun i => (T i).toLinearMap) (fun i g => (T i).isIntertwining' g) (fun i => (T i).injective)

end Independence

section HeadStability

variable {G : Type uG} [Group G] {V W : Type z} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The irreducible head of a representation with a twisting isomorphism has a twisting
isomorphism. -/
theorem nonempty_twistingEquiv_of_isIrreducibleHead (θ : G ≃* G) {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (A : ρ.Equiv (ρ.comp θ.toMonoidHom))
    (h : Classification.IsIrreducibleHead ρ π) :
    Nonempty (π.Equiv (π.comp θ.toMonoidHom)) := by
  obtain ⟨hπ, q, hq, hker⟩ := h
  let q₁ : ρ.IntertwiningMap (π.comp θ.toMonoidHom) :=
    ⟨q.toLinearMap ∘ₗ A.toLinearMap, fun g => LinearMap.ext fun v => by
      change q (A (ρ g v)) = π (θ g) (q (A v))
      rw [← q.isIntertwining]
      exact congrArg q (LinearMap.congr_fun (A.isIntertwining' g) v)⟩
  have hq₁ : Function.Surjective q₁ := hq.comp A.surjective
  have hirr' : Representation.IsIrreducible (π.comp θ.toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π θ).mpr hπ
  have hk := hker W (π.comp θ.toMonoidHom) hirr' q₁ hq₁
  exact Classification.SegmentHeadJacquetReduction.nonempty_equiv_of_ker_eq q hq q₁ hq₁ hk.symm

/-- An irreducible representation is equivalent to its irreducible head. -/
theorem nonempty_equiv_of_isIrreducibleHead_of_isIrreducible {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (hρ : ρ.IsIrreducible) (h : Classification.IsIrreducibleHead ρ π) :
    Nonempty (ρ.Equiv π) := by
  obtain ⟨hπ, q, hq, -⟩ := h
  have hinj : Function.Injective q := by
    let := hρ
    rcases Representation.IsIrreducible.injective_or_eq_zero q with h | h
    · exact h
    · exfalso
      let := hπ
      let : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
      obtain ⟨w', hw'⟩ := exists_ne (0 : W)
      obtain ⟨v', rfl⟩ := hq w'
      exact hw' (by rw [h]; rfl)
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective q.toLinearMap ⟨hinj, hq⟩)
    (fun g => q.isIntertwining' g)⟩

end HeadStability

end Langlands.BaseChange
