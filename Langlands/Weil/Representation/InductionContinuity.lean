import Langlands.Weil.Representation.InductionTopology
import Langlands.WeilDeligne.InductionAlong

/-!
# Usual-topology continuity of restriction and finite-index induction

Continuity is the usual-topology condition `IsContinuous`, into the module
topology on complex endomorphisms. Restriction along a continuous homomorphism
preserves it. Induction from an open finite-index subgroup preserves it: near
the identity the induced action is block diagonal in coset coordinates, and
continuity at the identity suffices for a homomorphism of groups.
-/

noncomputable section

universe uG uH uV

namespace Langlands.FiniteRepresentation

open InductionAlong

section Restriction

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction along a continuous homomorphism preserves usual-topology continuity. -/
theorem isContinuous_restrict (φ : H →* G) (hφ : Continuous φ)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.IsContinuous) :
    (restrict φ A).IsContinuous := by
  let _ : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  have hA' : Continuous A.representation := hA
  exact (hA'.comp hφ :)

/-- Restriction of usual-topology continuous representations. -/
def continuousRestrict (φ : H →* G) (hφ : Continuous φ)
    (A : ContinuousObjects.{uG, uV} G) : ContinuousObjects.{uH, uV} H :=
  ⟨restrict φ A.val, isContinuous_restrict φ hφ A.property⟩

/-- Restriction on genuine classes of usual-topology continuous representations. -/
def continuousRestrictClass (φ : H →* G) (hφ : Continuous φ) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) →
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.IsContinuous) :=
  Quotient.map (continuousRestrict φ hφ) (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

end Restriction

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Induction from an open finite-index subgroup preserves usual-topology
continuity. On the open neighbourhood of the identity where every coset
conjugate `q.out * g * q.out⁻¹` lies in `S`, the induced action in coset
coordinates is the block-diagonal operator with these conjugates acting. -/
theorem isContinuous_induce (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    {A : FiniteRepresentation.{0, uG, uV} ℂ S} (hA : A.IsContinuous) :
    (induce S A).IsContinuous := by
  classical
  let Q := Induction.Cosets S
  let _ : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  have : IsModuleTopology ℂ (Module.End ℂ A) := ⟨rfl⟩
  let _ : TopologicalSpace (Module.End ℂ (induce S A)) :=
    moduleTopology ℂ (Module.End ℂ (induce S A))
  have : IsModuleTopology ℂ (Module.End ℂ (induce S A)) := ⟨rfl⟩
  have : IsTopologicalRing (Module.End ℂ (induce S A)) :=
    IsModuleTopology.isTopologicalRing ℂ (Module.End ℂ (induce S A))
  have hA' : Continuous A.representation := hA
  let c := Induction.coordinates S A
  -- Block-diagonal operators in coset coordinates, transported to the induced space.
  let diag : (Q → Module.End ℂ A) →ₗ[ℂ] Module.End ℂ (Q → A) :=
    { toFun := fun T => LinearMap.pi fun q => (T q).comp (LinearMap.proj q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let F : (Q → Module.End ℂ A) →ₗ[ℂ] Module.End ℂ (induce S A) :=
    c.symm.conj.toLinearMap ∘ₗ diag
  have hF : Continuous F := IsModuleTopology.continuous_of_linearMap F
  let U : Set G := ⋂ q : Q, (fun h => q.out * h * q.out⁻¹) ⁻¹' (S : Set G)
  have hU : IsOpen U := isOpen_iInter_of_finite fun q =>
    hS.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have h1 : (1 : G) ∈ U := by
    apply Set.mem_iInter.mpr
    intro q
    change q.out * 1 * q.out⁻¹ ∈ S
    simp
  have hmem : ∀ u : U, ∀ q : Q, q.out * (u : G) * q.out⁻¹ ∈ S :=
    fun u q => Set.mem_iInter.mp u.property q
  have key : ∀ u : U, (induce S A).representation u =
      F (fun q => A.representation ⟨q.out * (u : G) * q.out⁻¹, hmem u q⟩) := by
    intro u
    apply LinearMap.ext
    intro f
    apply c.injective
    change c ((induce S A).representation u f) =
      c (c.symm (diag (fun q => A.representation ⟨q.out * (u : G) * q.out⁻¹, hmem u q⟩)
        (c f)))
    rw [LinearEquiv.apply_symm_apply]
    funext q
    change f.val (q.out * (u : G)) =
      A.representation ⟨q.out * (u : G) * q.out⁻¹, hmem u q⟩ (f.val q.out)
    have hf := f.property ⟨q.out * (u : G) * q.out⁻¹, hmem u q⟩ q.out
    refine Eq.trans ?_ hf
    simp [mul_assoc]
  have hcont : ContinuousOn (induce S A).representation U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : U.domRestrict (induce S A).representation =
        F ∘ fun u : U => fun q => A.representation ⟨q.out * (u : G) * q.out⁻¹, hmem u q⟩ := by
      funext u
      exact key u
    rw [heq]
    refine hF.comp (continuous_pi fun q => hA'.comp ?_)
    exact Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  change Continuous (induce S A).representation
  exact continuous_of_continuousAt_one _ (hcont.continuousAt (hU.mem_nhds h1))

/-- Actual induction on usual-topology continuous objects. -/
def continuousInduce (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G))
    (A : ContinuousObjects.{uG, uV} S) : ContinuousObjects.{uG, max uG uV} G :=
  ⟨induce S A.val, isContinuous_induce S hS A.property⟩

/-- Induction on genuine classes of usual-topology continuous representations. -/
def continuousInduceClass (S : Subgroup G) [S.FiniteIndex] (hS : IsOpen (S : Set G)) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ S => A.IsContinuous) →
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G => A.IsContinuous) :=
  Quotient.map (continuousInduce S hS) (fun _ _ ⟨e⟩ => ⟨induceEquiv S e⟩)

variable {H : Type uH} [Group H] [TopologicalSpace H]

/-- Induction along an open embedding with finite-index range preserves
usual-topology continuity. -/
theorem isContinuous_induceAlong (ι : H →* G) (hι : Topology.IsOpenEmbedding ι)
    [ι.range.FiniteIndex] {A : FiniteRepresentation.{0, uH, uV} ℂ H} (hA : A.IsContinuous) :
    (induceAlong ι hι.injective A).IsContinuous :=
  isContinuous_induce ι.range (isOpen_range ι hι)
    (isContinuous_restrict (rangeInverse ι hι.injective)
      (continuous_rangeInverse ι hι.isEmbedding) hA)

/-- Induction along an open embedding on usual-topology continuous objects. -/
def continuousInduceAlong (ι : H →* G) (hι : Topology.IsOpenEmbedding ι)
    [ι.range.FiniteIndex] (A : ContinuousObjects.{uH, uV} H) :
    ContinuousObjects.{uG, max uG uV} G :=
  ⟨induceAlong ι hι.injective A.val, isContinuous_induceAlong ι hι A.property⟩

/-- Induction along an open embedding on genuine classes of usual-topology
continuous representations. -/
def continuousInduceAlongClass (ι : H →* G) (hι : Topology.IsOpenEmbedding ι)
    [ι.range.FiniteIndex] :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.IsContinuous) →
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G => A.IsContinuous) :=
  Quotient.map (continuousInduceAlong ι hι)
    (fun _ _ ⟨e⟩ => ⟨induceAlongEquiv ι hι.injective e⟩)

end Induction

end Langlands.FiniteRepresentation
