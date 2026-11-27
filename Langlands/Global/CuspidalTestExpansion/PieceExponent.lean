import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicIntertwiningClosedQuotient
import Langlands.Global.AdelicWeylPositiveTransport
import Langlands.Global.AdelicExponentPolynomialIntegral
import Langlands.Global.AdelicStandardPositiveLog
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicExponentPolynomials

/-! # Exponents of intertwined generalized eigenfunctions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν

variable {I₁ J : StandardIndex F G fam.i fam.ν} {n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {c : fam.M J ⟶ fam.M I₁} {π : fam.P J ⟶ fam.M J} {K : Subgroup (AdelicGroupPoints F G)}
  [IsClosedImmersion (fam.p I₁).hom.hom.left]

variable {fam} in
/-- A polynomial orbit condition of degree at most `k` holds in every larger degree. -/
theorem HasPolynomialOrbit.mono {lam : ComplexCharacterParameter F (fam.P J)} {k m : ℕ}
    {h : AdelicGroupPoints F G → ℂ} (hk : fam.HasPolynomialOrbit J lam k h) (hkm : k ≤ m) :
    fam.HasPolynomialOrbit J lam m h := by
  intro g
  obtain ⟨p, hp, hpv⟩ := hk g
  refine ⟨p, Submodule.span_mono ?_ hp, hpv⟩
  rintro _ ⟨j, hj, ℓ, rfl⟩
  exact ⟨j, hj.trans hkm, ℓ, rfl⟩

set_option maxHeartbeats 1600000 in
/-- For a Weyl conjugation `n M_{I₁} n⁻¹ = M_J`, there is one target parameter `offset` such that
the intertwining integral over `(U_J(F) ∩ n U_{I₁}(𝔸) n⁻¹) \ U_J(𝔸)` of the twist `h_λ` of a
continuous, left `U_{I₁}(𝔸)`-invariant function `h` with unnormalized exponent `ν` along `I₁` and
polynomial degree at most `k` has unnormalized exponent `n(ν + λ) + offset` along `J`
(`weylParameter (fam.l I₁) c π (ν + λ) + offset`), again with polynomial degree at most `k`,
provided the integrands of all positive left translates of `h` are integrable. The proof takes
as offset the parameter whose power at each point `x_Q` of `𝔄_{P_J}` is the Haar factor of
conjugation by `x_Q` on `U_J(𝔸)` divided by that of its restriction to the closed adelic
stabilizer `(U_J ∩ n U_{I₁} n⁻¹)(𝔸)` (`intertwiningHaarOffset`). -/
theorem exists_offset_hasPolynomialOrbit_intertwiningIntegral
    (hW : IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c)
    (hπ : fam.l J ≫ π = 𝟙 (fam.M J)) (hK : IsIwasawaCompact (fam.p I₁) K) :
    ∃ offset : ComplexCharacterParameter F (fam.P J),
      ∀ (h : AdelicGroupPoints F G → ℂ), Continuous h →
        IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) h →
        ∀ (ν lam : ComplexCharacterParameter F (fam.P I₁)) (k : ℕ),
        fam.HasPolynomialOrbit I₁ ν k h →
        (∀ b ∈ fam.positiveSplitComponent I₁, ∀ y,
          Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
              (fam.unnormalizedAction I₁ b h) lam y)
            (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
              (innerAdelicPoint F G n))) →
        fam.HasPolynomialOrbit J (weylParameter (fam.l I₁) c π (ν + lam) + offset) k
          (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h lam) := by
  classical
  have hVr := (fam.isUnipotentRadical J).1
  have hUr := (fam.isUnipotentRadical I₁).1
  have : IsAffineHom (fam.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
  have : Smooth (fam.U J).X.hom := hVr.smooth
  have : LocallyOfFiniteType (fam.U J).X.hom := inferInstance
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have hi : IsClosedSubgroup (fam.iU I₁ ≫ fam.p I₁) := fam.closedU I₁
  obtain ⟨offset, hoff⟩ := intertwiningHaarOffset (iU := fam.iU I₁) (iV := fam.iU J) r hW
    hUr.isNormal hVr.isNormal hi hVr.isUnipotent
  refine ⟨offset, fun h hc hinv ν lam k hk hint => ?_⟩
  obtain ⟨hfin, eLog, heLog⟩ := fam.standardPositiveLog I₁
  intro g
  let μ' := intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
    (innerAdelicPoint F G n)
  let Vₐ := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
  let z : LeftCosetSpace (intertwiningRationalSubgroup F (fam.p I₁) (fam.iU I₁)
      (fam.iU J ≫ fam.p J) (innerAdelicPoint F G n)) → AdelicGroupPoints F G :=
    fun q => (innerAdelicPoint F G n)⁻¹ * ((Quotient.out q : Vₐ) : AdelicGroupPoints F G) * g
  choose Qz hQz hQval using fun q => hk (z q)
  let f : _ → RealCharacterDual F (fam.P I₁) → ℂ :=
    fun q T => hK.heightPower lam (z q) * Qz q T
  have hfpoly (q) : f q ∈ polynomialFunctions (RealCharacterDual F (fam.P I₁)) k :=
    Submodule.smul_mem _ _ (hQz q)
  have hpp_one (μ₁ μ₂ : ComplexCharacterParameter F (fam.P I₁)) (y : AdelicGroupPoints F (fam.P I₁))
      (hμ : μ₁ + μ₂ = 0) : parameterPower F (fam.P I₁) μ₁ y * parameterPower F (fam.P I₁) μ₂ y = 1 := by
    rw [← parameterPower_add, hμ]
    simp [parameterPower]
  -- each value of the parameterized polynomial is an integrand of a positive translate
  have hfint (T : RealCharacterDual F (fam.P I₁)) : Integrable (fun q => f q T) μ' := by
    let b := eLog.symm (Multiplicative.ofAdd T)
    have hb : characterLog F (fam.P I₁) b.val = T := by
      rw [← heLog b]
      simp [b]
    have hval (q) : f q T = parameterPower F (fam.P I₁) (-ν) b.val *
        hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
          (fam.unnormalizedAction I₁ b.val h) lam g q := by
      have := hQval q b.val b.property
      rw [hb] at this
      simp only [f, ← this, IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist]
      ring
    simp_rw [hval]
    exact (hint b.val b.property g).const_mul _
  have hPoly := exponentPolynomialIntegral k f μ' hfpoly hfint
  have : IsAffineHom (fam.M I₁).X.hom :=
    (fam.isCompatible I₁).levi.isConnectedReductive.isAffineHom
  let L := realCharacterDualMap F (fam.P J) (fam.P I₁) (π ≫ c ≫ fam.l I₁)
  refine ⟨_ ∘ L, polynomialFunctions_comp_linear L hPoly, fun x hx => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hx
  let tt : intrinsicSubgroup F (fam.A J) := ⟨t, ht⟩
  obtain ⟨hxP, hconj, hlog, hpow⟩ := weylPositiveTransport (fam.isCompatible I₁).splitComponent
    (fam.isCompatible J).splitComponent hW hπ tt
  let xQ := positivePointMap F (fam.P J) (fam.A J) (fam.a J ≫ fam.l J) tt
  let xP := map F (fam.P J) (fam.P I₁) (π ≫ c ≫ fam.l I₁) xQ
  change xP ∈ fam.positiveSplitComponent I₁ at hxP
  let aG := map F (fam.P J) G (fam.p J) xQ
  let α := positiveIntertwiningRadicalAction (q := fam.p J) (l' := fam.l J) (a := fam.a J)
    (fam.iU J) hVr.isNormal tt
  have hα := positiveIntertwiningRadicalAction_mem_stabilizer (a := fam.a J) (fam.iU I₁) (fam.iU J)
    hW hUr.isNormal hVr.isNormal tt
  have hconjI := intertwiningIntegralConjugation (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J) n
    hi hVr.smooth hVr.connectedSpace hVr.isUnipotent aG α hα (fun v => rfl) K hK h hc hinv
    hUr.isUnipotent lam g
  have hratio := hoff tt
  obtain ⟨hEq, -, -⟩ := hconjI
  have hxQ : pointMap F (fam.A J).toGrp (fam.P J) (Adeles F) (fam.a J ≫ fam.l J) t = xQ := rfl
  rw [hxQ]
  change hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h lam (aG * g) * _ = _
  rw [hEq, ← hratio]
  have hmoved : (fun q => hK.parameterTwist h lam
      ((innerAdelicPoint F G n)⁻¹ * aG * ((Quotient.out q : Vₐ) : AdelicGroupPoints F G) * g)) =
      fun q => parameterPower F (fam.P I₁) (ν + lam) xP *
        f q (L (characterLog F (fam.P J) xQ)) := by
    funext q
    have hsplit : (innerAdelicPoint F G n)⁻¹ * aG * ((Quotient.out q : Vₐ) : AdelicGroupPoints F G) *
        g = map F (fam.P I₁) G (fam.p I₁) xP * z q := by
      have hconj' : map F (fam.P I₁) G (fam.p I₁) xP =
          (innerAdelicPoint F G n)⁻¹ * aG * innerAdelicPoint F G n := hconj
      simp only [z]
      rw [hconj']
      group
    rw [hsplit]
    have hq := hQval q xP hxP
    rw [show characterLog F (fam.P I₁) xP = L (characterLog F (fam.P J) xQ) from hlog] at hq
    simp only [IsIwasawaCompact.parameterTwist, hK.heightPower_map_mul, f, ← hq,
      unnormalizedAction, parameterPower_add]
    have h1 := hpp_one ν (-ν) xP (add_neg_cancel ν)
    linear_combination (-(h (map F (fam.P I₁) G (fam.p I₁) xP * z q) *
      parameterPower F (fam.P I₁) lam xP * hK.heightPower lam (z q))) * h1
  rw [hmoved, integral_const_mul, ← hpow (ν + lam), Function.comp_apply]
  have h2 : parameterPower F (fam.P J) offset xQ *
      parameterPower F (fam.P J) (weylParameter (fam.l I₁) c π (ν + lam)) xQ *
      parameterPower F (fam.P J) (-(weylParameter (fam.l I₁) c π (ν + lam) + offset)) xQ = 1 := by
    rw [← parameterPower_add, ← parameterPower_add,
      show offset + weylParameter (fam.l I₁) c π (ν + lam) +
        -(weylParameter (fam.l I₁) c π (ν + lam) + offset) = 0 by abel]
    simp [parameterPower]
  linear_combination (∫ q, f q (L (characterLog F (fam.P J) xQ)) ∂μ') * h2

end Langlands.Global.StandardParabolicFamily
