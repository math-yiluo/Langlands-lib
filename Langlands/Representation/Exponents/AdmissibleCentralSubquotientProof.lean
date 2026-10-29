import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Exponents.AdmissibleCentralSubquotientStatement
import Langlands.Representation.Exponents.FiniteActionSpectrumProof
import Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Local detection of a central scalar subquotient

Proof of `AdmissibleCentralSubquotientStatement` by finite fixed vectors
and compact averaging. Derived from Worker 429's central-local probe;
the route was suggested by Worker 84 and checked informally by Worker 728.
-/

noncomputable section

namespace Langlands

universe uG uA uV uW

-- Central operators are genuine G-intertwiners, so compact averaging commutes.
private theorem central_average_commute
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type uA) [CommGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (c : A →* Subgroup.center G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (a : A) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ (c a : G) v) =
      ρ (c a : G) (Compact.averageMap ρ hρ K hK v) := by
  let f : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ (c a : G)
      isIntertwining' := fun g => by
        change ρ (c a : G) * ρ g = ρ g * ρ (c a : G)
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (c a).property g] }
  exact (LinearMap.congr_fun
    (Compact.averageMap_commute ρ ρ hρ hρ K hK f) v).symm

-- A scalar quotient's character has open kernel in the supplied topology.
-- This needs smoothness and continuity, without any finite-dimensional argument.
private theorem scalar_open_kernel
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (c : A →* Subgroup.center G) (hc : Continuous c)
    (χ : A →* ℂˣ) (U : Subrepresentation ρ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (q : U.toSubmodule →ₗ[ℂ] W) (hq : Function.Surjective q)
    (hscalar : ∀ (a : A) (u : U.toSubmodule),
      q (U.toRepresentation (c a : G) u) = (χ a : ℂ) • q u) :
    IsOpen (χ.ker : Set A) := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨u, hu⟩ := hq w
  have hqu : q u ≠ 0 := by rwa [hu]
  obtain ⟨K, hK⟩ := hρ (u : V)
  let f : A →* G := (Subgroup.center G).subtype.comp c
  have hf : Continuous f := continuous_subtype_val.comp hc
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup.comap f) ?_
    (K.isOpen.preimage hf)
  intro a ha
  have hfix : U.toRepresentation (c a : G) u = u :=
    Subtype.ext (hK ⟨c a, ha⟩)
  change χ a = 1
  apply Units.ext
  apply smul_left_injective ℂ hqu
  change (χ a : ℂ) • q u = (1 : ℂ) • q u
  rw [← hscalar a u, hfix, one_smul]

private theorem finite_scalar_detector
    (A : Type uA) [CommGroup A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ A V) (χ : A →* ℂˣ) (U : Subrepresentation ρ)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (q : U.toSubmodule →ₗ[ℂ] W) (hq : Function.Surjective q)
    (hscalar : ∀ (a : A) (u : U.toSubmodule),
      q (U.toRepresentation a u) = (χ a : ℂ) • q u) :
    commutativeCharacterSpace (commutativeTranspose ρ) χ 1 ≠ ⊥ := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hfin : Module.Finite ℂ
      (Submodule.span ℂ (Set.range (commutativeTranspose ρ))) := inferInstance
  have hspan := (finiteActionCommutativeSpectrum A (Module.Dual ℂ V)
    (commutativeTranspose ρ) hfin (IsLocallyConstant.of_discrete _)).2.2
  exact (scalarSubquotientDualSpectrum ℂ A V ρ
    (fun ψ => IsOpen (ψ.ker : Set A) ∧
      commutativeCharacterSpace (commutativeTranspose ρ) ψ 1 ≠ ⊥)
    hspan χ U W q hq hscalar).2

/-- A nonzero central scalar subquotient of an admissible representation has
open character kernel and occurs in the full transpose dual. -/
theorem admissibleCentralSubquotient :
    AdmissibleCentralSubquotientStatement.{uG, uA, uV, uW} := by
  classical
  intro G _ _ _ hcofinal A _ _ _ V _ _ ρ c hc hρ χ U W _ _ _ q hq hscalar
  refine ⟨scalar_open_kernel G A V ρ hρ.1 c hc χ U W q hq hscalar, ?_⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨u, hu⟩ := hq w
  have hqu : q u ≠ 0 := by rwa [hu]
  obtain ⟨H, hH⟩ := hρ.1 (u : V)
  obtain ⟨K, hKcompact, hKH⟩ := hcofinal H
  have hKu : (u : V) ∈ fixedVectors ρ K.toSubgroup :=
    fun k => hH ⟨k, hKH k.property⟩
  let f : A →* G := (Subgroup.center G).subtype.comp c
  let S : Subrepresentation (ρ.comp f) :=
    { toSubmodule := fixedVectors ρ K.toSubgroup
      apply_mem_toSubmodule := fun a v hv k => by
        change ρ (k : G) (ρ (c a : G) v) = ρ (c a : G) v
        calc
          _ = ρ (c a : G) (ρ (k : G) v) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
              Subgroup.mem_center_iff.mp (c a).property (k : G)]
          _ = _ := congrArg (ρ (c a : G)) (hv k) }
  let : Module.Finite ℂ S.toSubmodule := hρ.2 K
  let U₀ : Subrepresentation S.toRepresentation :=
    { toSubmodule := U.toSubmodule.comap S.toSubmodule.subtype
      apply_mem_toSubmodule := fun a _ hv =>
        U.apply_mem_toSubmodule (c a : G) hv }
  let incl : U₀.toSubmodule →ₗ[ℂ] U.toSubmodule :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q₀ : U₀.toSubmodule →ₗ[ℂ] W := q.comp incl
  let u₀ : U₀.toSubmodule := ⟨⟨u.val, hKu⟩, u.property⟩
  have hq₀ : q₀ u₀ ≠ 0 := hqu
  let : Nontrivial q₀.range :=
    ⟨⟨q₀.rangeRestrict u₀, 0, fun h => hq₀ (congrArg Subtype.val h)⟩⟩
  have hscalar₀ (a : A) (v : U₀.toSubmodule) :
      q₀.rangeRestrict (U₀.toRepresentation a v) =
        (χ a : ℂ) • q₀.rangeRestrict v := by
    apply Subtype.ext
    exact hscalar a (incl v)
  have hdet := finite_scalar_detector A S.toSubmodule S.toRepresentation χ U₀
    q₀.range q₀.rangeRestrict q₀.surjective_rangeRestrict hscalar₀
  obtain ⟨φ, hφ, hφne⟩ := FiniteActionSpectrum.subrepresentation_exists_ne_zero hdet
  have hφact := (mem_commutativeCharacterSpace_one _ χ φ).mp hφ
  let P : V →ₗ[ℂ] S.toSubmodule :=
    (Compact.averageMap ρ hρ.1 K hKcompact).codRestrict S.toSubmodule
      (Compact.averageMap_mem_fixedVectors ρ hρ.1 K hKcompact)
  have hPid (v : S.toSubmodule) : P v.val = v := by
    apply Subtype.ext
    exact Compact.averageMap_id ρ hρ.1 K hKcompact v.val v.property
  have hPcomm (a : A) (v : V) :
      P (ρ (c a : G) v) = S.toRepresentation a (P v) := by
    apply Subtype.ext
    exact central_average_commute G A V ρ hρ.1 c K hKcompact a v
  let ψ : Module.Dual ℂ V := φ.comp P
  have hψne : ψ ≠ 0 := by
    intro he
    apply hφne
    ext v
    have h := congrArg (fun ℓ : Module.Dual ℂ V => ℓ v.val) he
    change φ (P v.val) = 0 at h
    simpa only [hPid v, LinearMap.zero_apply] using h
  have hψmem : ψ ∈ commutativeCharacterSpace (commutativeTranspose (ρ.comp f)) χ 1 := by
    apply (mem_commutativeCharacterSpace_one _ χ ψ).mpr
    intro a
    ext v
    simp only [commutativeTranspose_apply, LinearMap.smul_apply]
    change φ (P (ρ (c a : G) v)) = (χ a : ℂ) • φ (P v)
    rw [hPcomm]
    have he := congrArg (fun ℓ : Module.Dual ℂ S.toSubmodule => ℓ (P v)) (hφact a)
    simpa only [commutativeTranspose_apply, LinearMap.smul_apply] using he
  intro hb
  apply hψne
  exact FiniteActionSpectrum.subrepresentation_mem_bot_iff.mp (hb ▸ hψmem)

end Langlands
