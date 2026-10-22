import Langlands.Weil.Local.RepresentationStatements
import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Representation.ContinuityBridgeProof
import Langlands.Weil.Representation.FiniteImageExtensionProof
import Langlands.Weil.Representation.UnramifiedReductionProof

/-! # Galois type and commuting correction on the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

/-- The existing local Galois-type and same-carrier unique-extension statement. -/
theorem localWeilGaloisTypeFor {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    LocalWeilGaloisTypeFor.{u, v} F := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let := LocalClassField.absoluteGaloisNonarchimedean F.Carrier
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  intro A
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  have extension (hc : A.IsContinuous) (hf : A.HasFiniteImage) :
      ∃! τ : Representation ℂ (Field.absoluteGaloisGroup F.Carrier) A,
        (FiniteRepresentation.of τ).IsContinuous ∧
          τ.comp (localProjection F).toMonoidHom = A.representation := by
    obtain ⟨τ, ⟨hτc, hτr⟩, hτuniq⟩ :=
      (finiteImageExtension (Field.absoluteGaloisGroup F.Carrier)
        (localResidueDegree F) (localResidueDegree_surjective F)
        A A.representation ((FiniteRepresentation.isContinuous_of_iff _).mp hc)).mp hf
    refine ⟨τ, ⟨(FiniteRepresentation.isContinuous_of_iff _).mpr hτc, hτr⟩, ?_⟩
    intro τ' hτ'
    exact hτuniq τ' ⟨(FiniteRepresentation.isContinuous_of_iff _).mp hτ'.1, hτ'.2⟩
  refine ⟨⟨?_, ?_⟩, extension⟩
  · rintro ⟨τ, hτc, hτr⟩
    have hc := (FiniteRepresentation.isContinuous_of_iff τ).mp hτc
    have hAc : Continuous (fun w : localWeilGroup F =>
        (A.representation w).toContinuousLinearMap) := by
      have hcomp := hc.comp (localProjection F).continuous
      change Continuous (fun w : localWeilGroup F =>
        ((τ.comp (localProjection F).toMonoidHom) w).toContinuousLinearMap) at hcomp
      rwa [hτr] at hcomp
    refine ⟨(FiniteRepresentation.isContinuous_of_iff _).mpr hAc, ?_⟩
    have hf := continuous_compact_nonarchimedean_representation_finite_range
      (Field.absoluteGaloisGroup F.Carrier) A τ hc
    apply hf.subset
    rintro _ ⟨w, rfl⟩
    exact ⟨localProjection F w, DFunLike.congr_fun hτr w⟩
  · rintro ⟨hc, hf⟩
    exact (extension hc hf).exists

/-- The existing same-carrier commuting unramified-correction statement. -/
theorem localWeilUnramifiedCorrectionFor {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : LocalWeilUnramifiedCorrectionFor.{u, v} F := by
  let : CompactSpace (localDegree F).toMonoidHom.ker := isCompact_iff_compactSpace.mp
    (localInertia_isCompact F)
  let := localWeilGroup_nonarchimedean F
  intro A hc
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  obtain ⟨τ, σ, hτc, hτi, hcomm, hprod, hσc, hσf⟩ :=
    (unramifiedReduction (localWeilGroup F) (localDegree F).toMonoidHom
      (localDegree_surjective F) (localInertia_isOpen F) A A.representation
      ((FiniteRepresentation.isContinuous_of_iff _).mp hc)).1
  have hσc' : (FiniteRepresentation.of σ).IsContinuous :=
    (FiniteRepresentation.isContinuous_of_iff σ).mpr hσc
  exact ⟨τ, σ, (FiniteRepresentation.isContinuous_of_iff τ).mpr hτc,
    hτi, hcomm, hprod, hσc', hσf,
    ((localWeilGaloisTypeFor F (FiniteRepresentation.of σ)).1).mpr ⟨hσc', hσf⟩⟩

end Langlands.Weil.Local
