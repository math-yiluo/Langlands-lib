import Langlands.Weil.Representation.InductionDimensionProof
import Langlands.Weil.Representation.FiniteIndexRestrictionSemisimplicityProof

/-!
# Semisimplicity of actual finite-index induction

Normal-core restriction and finite coset evaluations prove preservation;
surjective evaluation at one proves reflection. The finite-index comparison
transports the result to Mathlib's tensor/coinvariant induction.
-/

noncomputable section

namespace Langlands.Weil

universe uG uV

namespace InductionSemisimplicity

open scoped MonoidAlgebra
open Representation
open FiniteRepresentation.Induction

variable {k G : Type*} [Field k] [Group G]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Semisimplicity passes to a surjective intertwining image. -/
theorem semisimple_of_surjective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : IsSemisimpleRepresentation ρ) : IsSemisimpleRepresentation σ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hρ ⊢
  let := hρ
  exact IsSemisimpleModule.of_surjective (IntertwiningMap.equivLinearMapAsModule _ _ f) hf

/-- Semisimplicity is invariant under an equivalence of representations. -/
theorem semisimple_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : IsSemisimpleRepresentation ρ ↔ IsSemisimpleRepresentation σ :=
  ⟨semisimple_of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective,
    semisimple_of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective⟩

variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)

/-- Conjugation followed by inclusion into the inducing subgroup. -/
def conjugateInclusion (g : G) : N →* H where
  toFun n := ⟨g * n * g⁻¹, hNH (Subgroup.Normal.conj_mem (H := N) inferInstance (n : G) n.2 g)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

/-- Conjugation does not change the image of restriction to a normal subgroup. -/
theorem range_conjugate (ρ : Representation k H V) (g : G) :
    Set.range (ρ.comp (conjugateInclusion H N hNH g)) =
      Set.range (ρ.comp (N.subgroupOf H).subtype) := by
  ext T
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨conjugateInclusion H N hNH g n,
      Subgroup.Normal.conj_mem (H := N) inferInstance (n : G) n.2 g⟩, rfl⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨g⁻¹ * (n : H) * g,
      Subgroup.Normal.conj_mem' (H := N) inferInstance _ n.2 g⟩, ?_⟩
    change ρ _ = ρ (n : H)
    congr 1
    apply Subtype.ext
    simp [conjugateInclusion, mul_assoc]

/-- Evaluation at `g` intertwines normal-subgroup translation with conjugation. -/
def evaluation (ρ : Representation k H V) (g : G) :
    IntertwiningMap ((ρ.coind H.subtype).comp N.subtype)
      (ρ.comp (conjugateInclusion H N hNH g)) where
  toLinearMap := (LinearMap.proj g).comp (coindV H.subtype ρ).subtype
  isIntertwining' n := by
    ext f
    change f.val (g * n) = ρ (conjugateInclusion H N hNH g n) (f.val g)
    have h := f.property (conjugateInclusion H N hNH g n) g
    simpa [conjugateInclusion, mul_assoc] using h

/-- Evaluation at one is an intertwiner from restricted coinduction onto the input. -/
def evaluationOne (ρ : Representation k H V) :
    IntertwiningMap ((ρ.coind H.subtype).comp H.subtype) ρ where
  toLinearMap := (LinearMap.proj 1).comp (coindV H.subtype ρ).subtype
  isIntertwining' h := by
    ext f
    change f.val (1 * (h : G)) = ρ h (f.val 1)
    simpa using f.property h 1

/-- Coset coordinates show that evaluation at one is surjective. -/
theorem evaluationOne_surjective [FiniteDimensional k V] (ρ : Representation k H V) :
    Function.Surjective (evaluationOne H ρ) := by
  intro v
  let A := FiniteRepresentation.of ρ
  let e := coordinates H A
  refine ⟨e.symm (fun _ => ρ (factor H 1)⁻¹ v), ?_⟩
  change ρ (factor H 1) (ρ (factor H 1)⁻¹ v) = v
  exact Representation.self_inv_apply ρ _ v

/-- The coinduced representation restricted to the normal core embeds in the
finite product of the conjugate restrictions of the inducing representation. -/
theorem coind_semisimple {G : Type uG} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsSemisimpleRepresentation ρ) :
    IsSemisimpleRepresentation (ρ.coind H.subtype) := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let N := H.normalCore
  have hNH : N ≤ H := H.normalCore_le
  have hN : IsSemisimpleRepresentation (ρ.comp (N.subgroupOf H).subtype) :=
    (representationFiniteIndexRestrictionSemisimplicity H (N.subgroupOf H) V ρ).2 hρ
  let τ : Representation ℂ N (coindV H.subtype ρ) :=
    (ρ.coind H.subtype).comp N.subtype
  let σ (q : Cosets H) : Representation ℂ N V :=
    ρ.comp (conjugateInclusion H N hNH q.out)
  have hσ (q : Cosets H) : IsSemisimpleRepresentation (σ q) :=
    (FiniteIndexRestrictionSemisimplicity.isSemisimpleRepresentation_iff_of_range_eq
      _ _ (range_conjugate H N hNH ρ q.out)).2 hN
  have (q : Cosets H) : IsSemisimpleModule ℂ[N] (σ q).asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1 (hσ q)
  let f : τ.asModule →ₗ[ℂ[N]] (∀ q : Cosets H, (σ q).asModule) :=
    LinearMap.pi fun q =>
      IntertwiningMap.equivLinearMapAsModule _ _ (evaluation H N hNH ρ q.out)
  have hf : Function.Injective f := by
    intro x y h
    apply (coordinates H (FiniteRepresentation.of ρ)).injective
    exact funext fun q => congrFun h q
  have hτ : IsSemisimpleRepresentation τ := by
    rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    exact IsSemisimpleModule.of_injective f hf
  exact finiteIndexSemisimplicityAscent ℂ G (coindV H.subtype ρ) N
    (ρ.coind H.subtype) hτ

end InductionSemisimplicity

open InductionSemisimplicity in
/-- Actual finite-index induction preserves and reflects semisimplicity. -/
theorem representationInductionSemisimplicity :
    RepresentationInductionSemisimplicity.{uG, uV} := by
  intro G _ H _ V _ _ _ ρ
  classical
  let e : (ρ.ind H.subtype).Equiv (ρ.coind H.subtype) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))
  rw [semisimple_equiv e]
  constructor
  · intro h
    have : FiniteDimensional ℂ (Representation.IndV H.subtype ρ) :=
      (representationInductionDimension G H V ρ).1
    have : FiniteDimensional ℂ (Representation.coindV H.subtype ρ) :=
      Module.Finite.equiv e.toLinearEquiv
    have hH := (representationFiniteIndexRestrictionSemisimplicity G H
      (Representation.coindV H.subtype ρ) (ρ.coind H.subtype)).2 h
    exact semisimple_of_surjective (evaluationOne H ρ) (evaluationOne_surjective H ρ) hH
  · exact coind_semisimple H ρ

-- The entire unapplied theorem has the named target at independent universes.
example : RepresentationInductionSemisimplicity.{uG, uV} :=
  @representationInductionSemisimplicity.{uG, uV}

-- Check the entire constant also against the fully unfolded formula.
example :
    ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
      (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ H V),
      Representation.IsSemisimpleRepresentation (ρ.ind H.subtype) ↔
        Representation.IsSemisimpleRepresentation ρ :=
  @representationInductionSemisimplicity.{uG, uV}

end Langlands.Weil
