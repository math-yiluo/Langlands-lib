import Langlands.Global.CuspidalTestExpansion.PieceTranslates
import Langlands.Global.CuspidalTestExpansion.PieceExponent

/-! # Splitting an intertwining integral along an exponent decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

variable {I₁ J : StandardIndex F G fam.i fam.ν} {n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {c : fam.M J ⟶ fam.M I₁} {π : fam.P J ⟶ fam.M J} {K : Subgroup (AdelicGroupPoints F G)}
  [IsClosedImmersion (fam.p I₁).hom.hom.left]

set_option maxHeartbeats 1600000 in
/-- Let `f = ∑_{ν ∈ s} c_ν` be a finite sum of continuous, `U_{I₁}(𝔸)`-invariant functions with
unnormalized exponents `ν` along `I₁` and polynomial degree at most `k`, and suppose the
intertwining integrand of `f` is integrable at every argument. Then the intertwining integral of
`f_λ` is the sum of those of the `(c_ν)_λ`; each summand has unnormalized exponent
`n(ν + λ) + offset` along `J` with polynomial degree at most `k`, and is a finite combination of
positive split translates along `J` of the intertwining integral of `f`. -/
theorem intertwiningIntegral_exponentExpansion
    (hW : IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c)
    (hK : IsIwasawaCompact (fam.p I₁) K) (offset : ComplexCharacterParameter F (fam.P J))
    (hoffset : ∀ (h : AdelicGroupPoints F G → ℂ), Continuous h →
        IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) h →
        ∀ (ν lam : ComplexCharacterParameter F (fam.P I₁)) (k : ℕ),
        fam.HasPolynomialOrbit I₁ ν k h →
        (∀ b ∈ fam.positiveSplitComponent I₁, ∀ y,
          Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
              (fam.unnormalizedAction I₁ b h) lam y)
            (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
              (innerAdelicPoint F G n))) →
        fam.HasPolynomialOrbit J (weylParameter (fam.l I₁) c π (ν + lam) + offset) k
          (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h lam))
    {f : AdelicGroupPoints F G → ℂ} (hfc : Continuous f)
    (hfU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) f)
    (lam : ComplexCharacterParameter F (fam.P I₁))
    (hf : ∀ y, Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam y)
      (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
        (innerAdelicPoint F G n)))
    (s : Finset (ComplexCharacterParameter F (fam.P I₁)))
    (comp : ComplexCharacterParameter F (fam.P I₁) → AdelicGroupPoints F G → ℂ)
    (hsum : f = ∑ ν ∈ s, comp ν) (hcc : ∀ ν ∈ s, Continuous (comp ν))
    (hcU : ∀ ν ∈ s,
      IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) (comp ν))
    (k : ℕ) (hcexp : ∀ ν ∈ s, fam.HasPolynomialOrbit I₁ ν k (comp ν)) :
    hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam =
        ∑ ν ∈ s, hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n (comp ν) lam ∧
      ∀ ν ∈ s,
        fam.HasPolynomialOrbit J (weylParameter (fam.l I₁) c π (ν + lam) + offset) k
            (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n (comp ν) lam) ∧
          hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n (comp ν) lam ∈
            fam.translateSpan J (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam) := by
  classical
  have hmem : ∀ ν ∈ s, comp ν ∈ fam.translateSpan I₁ f := by
    intro ν hν
    have h := fam.mem_translateSpan_of_sum I₁ s comp (fun ν' hν' => ⟨k, hcexp ν' hν'⟩) ν hν
    rwa [← hsum] at h
  have hint : ∀ ν ∈ s, ∀ y, Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J)
      n (comp ν) lam y) (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
        (innerAdelicPoint F G n)) := fun ν hν y =>
    fam.integrable_intertwiningIntegrand_of_mem_translateSpan hW hK hfc hfU lam hf (hmem ν hν) y
  refine ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩
  · funext y
    have hsplit : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam y =
        fun q => ∑ ν ∈ s, hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
          (comp ν) lam y q := by
      funext q
      simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, hsum,
        Finset.sum_apply, Finset.sum_mul]
    simp only [IsIwasawaCompact.intertwiningIntegral, Finset.sum_apply, hsplit]
    exact integral_finsetSum s fun ν hν => hint ν hν y
  · apply hoffset (comp ν) (hcc ν hν) (hcU ν hν) ν lam k (hcexp ν hν)
    intro b hb y
    exact fam.integrable_intertwiningIntegrand_of_mem_translateSpan hW hK hfc hfU lam hf
      (fam.splitComponentRepresentation_mem_translateSpan I₁ f ⟨b, hb⟩ (hmem ν hν)) y
  · exact fam.intertwiningIntegral_mem_translateSpan hW hK hfc hfU lam hf (hmem ν hν)

end Langlands.Global.StandardParabolicFamily
