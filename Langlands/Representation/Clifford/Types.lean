import Langlands.Representation.Clifford.Determinant
import Langlands.Representation.Clifford.OpenExtension
import Langlands.Weil.Representation.InductionTopology
import Langlands.Weil.Representation.ContinuityBridgeProof
import Langlands.Weil.Representation.ContinuityProof

/-!
# Continuous irreducible representations over a normal subgroup
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

section Continuity

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [NonarchimedeanGroup G]

/-- On a compact nonarchimedean group, continuity of a finite-dimensional complex
representation is equivalent to openness of its kernel. -/
theorem isContinuous_iff_isOpen_ker (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    A.IsContinuous ↔ IsOpen (A.representation.ker : Set G) := by
  let I : OpenSubgroup G := ⊤
  have htop : IsTopologicalGroup I := inferInstanceAs (IsTopologicalGroup (I : Subgroup G))
  have hnon : NonarchimedeanGroup I := by
    refine { toIsTopologicalGroup := htop, is_nonarchimedean := ?_ }
    intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    obtain ⟨K, hKV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
    refine ⟨K.comap I.toSubgroup.subtype continuous_subtype_val, ?_⟩
    exact (Set.preimage_mono hKV).trans hVU
  have hcpt : CompactSpace I := by
    apply isCompact_iff_compactSpace.mp
    have : ((I : Subgroup G) : Set G) = Set.univ := rfl
    rw [show ((I : OpenSubgroup G) : Set G) = Set.univ from rfl]
    exact isCompact_univ
  exact ((Weil.bundledRepresentationContinuity_iff.mpr Weil.representationContinuity) G I A).2.2.2.1

end Continuity

section Transport

variable {G : Type uG} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
  {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- Transport a representation along a linear equivalence of carriers. -/
def transportRep (e : X ≃ₗ[ℂ] Y) (ρ : Representation ℂ G X) : Representation ℂ G Y where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The transported representation is equivalent to the original one. -/
def transportEquiv (e : X ≃ₗ[ℂ] Y) (ρ : Representation ℂ G X) :
    Representation.Equiv ρ (transportRep e ρ) where
  toLinearEquiv := e
  isIntertwining' g := by ext; simp [transportRep]

end Transport

section CoindObj

variable {G : Type uG} [Group G] (H : Subgroup G) [H.FiniteIndex]
variable {V : Type uW} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Coset coordinates of equivariant functions, indexed by a finite type in universe zero. -/
def coindCoordEquiv (θ : Representation ℂ H V) :
    coindV H.subtype θ ≃ₗ[ℂ] (Fin (Fintype.card (Induction.Cosets H)) → V) :=
  (Induction.coordinates H (FiniteRepresentation.of θ)).trans
    (LinearEquiv.funCongrLeft ℂ V (Fintype.equivFin (Induction.Cosets H)).symm)

/-- The coinduced representation on a carrier in the universe of `V`. -/
def coindRep (θ : Representation ℂ H V) :
    Representation ℂ G (Fin (Fintype.card (Induction.Cosets H)) → V) :=
  transportRep (coindCoordEquiv H θ) (θ.coind H.subtype)

/-- The coinduced representation as a finite-dimensional representation with carrier in the
universe of `V`. -/
def coindObj (θ : Representation ℂ H V) : FiniteRepresentation.{0, uG, uW} ℂ G :=
  FiniteRepresentation.of (coindRep H θ)

/-- The comparison with the coinduction on equivariant functions. -/
def coindObjEquiv (θ : Representation ℂ H V) :
    Representation.Equiv (θ.coind H.subtype) (coindObj H θ).representation :=
  transportEquiv (coindCoordEquiv H θ) (θ.coind H.subtype)

theorem finrank_coindObj (θ : Representation ℂ H V) :
    Module.finrank ℂ (coindObj H θ) = H.index * Module.finrank ℂ V := by
  change Module.finrank ℂ (Fin (Fintype.card (Induction.Cosets H)) → V) = _
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card]
  rfl

theorem ker_coindRep (τ : Representation ℂ H V) :
    (coindRep H τ).ker = (τ.coind H.subtype).ker := by
  ext g
  constructor
  · intro hg
    have h1 := MonoidHom.mem_ker.mp hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro f
    have h2 := LinearMap.congr_fun h1 (coindCoordEquiv H τ f)
    change coindCoordEquiv H τ (τ.coind H.subtype g ((coindCoordEquiv H τ).symm
      (coindCoordEquiv H τ f))) = coindCoordEquiv H τ f at h2
    simpa using h2
  · intro hg
    have h1 := MonoidHom.mem_ker.mp hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro f
    change coindCoordEquiv H τ (τ.coind H.subtype g ((coindCoordEquiv H τ).symm f)) = f
    rw [h1]
    simp

end CoindObj

end Langlands.Clifford
