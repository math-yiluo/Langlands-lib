import Langlands.BaseChange.TwistedCharacter.EquivariantLine
import Langlands.BaseChange.TwistedCharacter.LinearIndependence
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SubquotientProof

/-! # Twisted trace interpolation on an unramified orbit at fixed central character -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory GeneralLinear

universe uG uV uW u v

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `π` is in the unramified twist orbit of `ρ` under characters invariant by `θ`. -/
def IsUnramifiedTwistOf (θ : G ≃* G) (ρ : Representation ℂ G V) (π : Representation ℂ G W) :
    Prop := ∃ ψ : G →* ℂˣ, IsUnramifiedCharacter ψ ∧ (∀ g, ψ (θ g) = ψ g) ∧
      Nonempty (π.Equiv (twist ψ ρ))

end Orbit

section Interpolation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Interpolation on one twist orbit at fixed central character. Choose one representative per
isomorphism class of the central-character-preserving twists inequivalent to the base
representation, and use finite-family twisted trace interpolation with the base pair
itself. The resulting test function has trace `1` at the base pair and `0` at every
inequivalent pair in the orbit with the given central character. -/
theorem exists_twistOrbit_test_values (θ : G ≃* G)
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K)
    (hfinite : Finite {ψ : G →* ℂˣ // IsUnramifiedCharacter ψ ∧ Subgroup.center G ≤ ψ.ker})
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (χ : Subgroup.center G →* ℂˣ) (hχ : HasCentralCharacterRep ρ χ)
    (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    ∃ f : SchwartzBruhat G, twistedDistribution μ ρ hρ A.toLinearMap f = 1 ∧
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
        (hπ : IsAdmissible π), HasCentralCharacterRep π χ → IsEmpty (π.Equiv ρ) →
        IsUnramifiedTwistOf θ ρ π → ∀ B : π.Equiv (π.comp θ.toMonoidHom),
          twistedDistribution μ π hπ B.toLinearMap f = 0 := by
  classical
  let S := {ψ : G →* ℂˣ // IsUnramifiedCharacter ψ ∧ (∀ g, ψ (θ g) = ψ g) ∧
    Subgroup.center G ≤ ψ.ker ∧ IsEmpty ((twist ψ ρ).Equiv ρ)}
  have : Finite S := Finite.of_injective
    (fun ψ : S => (⟨ψ.val, ψ.property.1, ψ.property.2.2.1⟩ :
      {ψ : G →* ℂˣ // IsUnramifiedCharacter ψ ∧ Subgroup.center G ≤ ψ.ker}))
    (fun _ _ h => Subtype.ext (congrArg (fun x :
      {ψ : G →* ℂˣ // IsUnramifiedCharacter ψ ∧ Subgroup.center G ≤ ψ.ker} => x.val) h))
  let s : Setoid S :=
    { r := fun a b => Nonempty ((twist a.val ρ).Equiv (twist b.val ρ))
      iseqv := ⟨fun a => ⟨Representation.Equiv.refl _⟩,
        fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩ }
  let ι := Option (Quotient s)
  let : Fintype ι := Fintype.ofFinite ι
  let R : ι → Representation ℂ G V := fun i => i.elim ρ fun q => twist q.out.val ρ
  have hR (i : ι) : IsAdmissible (R i) := by
    cases i with
    | none => exact hρ
    | some q => exact (isAdmissible_twist_iff q.out.val ρ q.out.property.1.isOpen_ker).mpr hρ
  have hI (i : ι) : (R i).IsIrreducible := by
    cases i with
    | none => exact hirr
    | some q => exact (isIrreducible_twist_iff q.out.val ρ).mpr hirr
  let D (i : ι) : (R i).Equiv ((R i).comp θ.toMonoidHom) := match i with
    | none => A
    | some q => twistTwistedIntertwiner θ q.out.val q.out.property.2.1 A
  have hne : Pairwise (fun i j => ¬ Nonempty ((R i).Equiv (R j))) := by
    intro i j hij ⟨e⟩
    apply hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some q => exact (q.out.property.2.2.2.false e.symm).elim
    | some q =>
      cases j with
      | none => exact (q.out.property.2.2.2.false e).elim
      | some q' =>
        have ht : s.r q.out q'.out := ⟨e⟩
        exact congrArg Option.some ((Quotient.out_eq q).symm.trans
          ((Quotient.sound ht).trans (Quotient.out_eq q')))
  obtain ⟨f, hf⟩ := exists_twistedDistribution_test_values μ θ hθ R hR hI hne
    (fun i => (D i).toLinearMap) (fun i g => (D i).isIntertwining' g) (fun i => (D i).injective)
    (fun i => if i = none then 1 else 0)
  refine ⟨f, ?_, ?_⟩
  · exact (hf (none : ι)).trans (by simp)
  · intro W _ _ π hπ hχπ hneπ hOrb B
    obtain ⟨ψ, hψ, hψθ, ⟨e⟩⟩ := hOrb
    have : Nontrivial V := CharacterSeparation.nontrivial_of_isIrreducible hirr
    let a : S := ⟨ψ, hψ, hψθ, center_le_ker_of_equiv_twist_same_centralCharacter hχ hχπ e,
      ⟨fun e' => hneπ.false (e.trans e')⟩⟩
    let q : Quotient s := Quotient.mk s a
    have ht : s.r q.out a := Quotient.exact (Quotient.out_eq q)
    obtain ⟨a0⟩ := ht
    let repEquiv : (R (some q)).Equiv π := a0.trans e.symm
    obtain ⟨b, hb⟩ := exists_twistedDistribution_eq_smul_of_equiv μ θ (hR (some q))
      (hI (some q)) hπ repEquiv (D (some q)) B
    have h0 : twistedDistribution μ (R (some q)) (hR (some q)) (D (some q)).toLinearMap f = 0 := by
      exact (hf (some q)).trans (by simp)
    rw [hb, LinearMap.smul_apply, h0, smul_zero]

end Interpolation

section Entrywise

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- Iteration of the entrywise automorphism is entrywise application of a power. -/
theorem entrywiseAut_iterate_eq_pow (σ : E ≃ₐ[F] E) (n N : ℕ) (g : GeneralLinear n E) :
    (⇑(entrywiseAut σ n))^[N] g = entrywiseAut (σ ^ N) n g := by
  induction N with
  | zero => simp [entrywiseAut_one_apply]
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', entrywiseAut_mul_apply]

end Entrywise

end Langlands.BaseChange
