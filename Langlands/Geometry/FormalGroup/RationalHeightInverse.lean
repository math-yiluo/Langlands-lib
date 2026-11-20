import Langlands.Geometry.FormalGroup.GlobalRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightComposition

/-! # Opposite signed kernel-rank heights for actual inverse maps -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {π : O} {q H : ℕ} {U : Opens (PrimeSpectrum R)}

namespace RationalSection.HeightPresentation

/-- The given numerator and denominator define a ranked tensor over the ring of
sections of the open, even when the original section only has local presentations. -/
def toOpenTensor {z : RationalSection F M N U} (P : HeightPresentation π q z)
    (hπ : algebraMap O F π ≠ 0) :
    RationalHom.GlobalHeightPresentation π q
      (((algebraMap O F π) ^ P.exponent)⁻¹ •
        (RationalHom.ofHom P.representative :
          (rationalHomPresheaf F M N).obj (op U))) where
  toScalarIsogenyPresentation :=
    RationalHom.ScalarIsogenyPresentation.ofDenominator π hπ P.exponent
      P.representative P.numerator.1
  numeratorHeight := P.numeratorHeight
  numeratorRank := P.numerator.2

/-- The ranked tensor gives the original section after sheafification. -/
theorem ofRational_openTensor {z : RationalSection F M N U} (P : HeightPresentation π q z)
    (hπ : algebraMap O F π ≠ 0) :
    ofRational U (((algebraMap O F π) ^ P.exponent)⁻¹ • RationalHom.ofHom P.representative) = z := by
  let a := (algebraMap O F π) ^ P.exponent
  have hcancel : a⁻¹ • ofIntegral U P.representative = z := by
    rw [← P.represents, inv_smul_smul₀ (pow_ne_zero _ hπ)]
  exact ((ofRational (F := F) (M := M) (N := N) U).map_smul
    a⁻¹ (RationalHom.ofHom P.representative)).trans hcancel

variable [IsDomain O] [IsFractionRing O F]

/-- On a nonempty open, the actual inverse section has a presentation of opposite
height when both formal modules have the same positive scalar height. -/
theorem exists_inverse [Nontrivial ((coefficientStructurePresheaf R).obj (op U))]
    (e : RationalSectionIso F M N U) (P : HeightPresentation π q e.hom)
    (hπ : algebraMap O F π ≠ 0) (hq : 2 ≤ q) (hH : 0 < H)
    (hM : (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H)
    (hN : (N.overAlgebra ((coefficientStructurePresheaf R).obj (op U))).HasPiHeight π q H) :
    ∃ Q : HeightPresentation π q e.inv, Q.index = -P.index := by
  let E := P.toOpenTensor hπ
  obtain ⟨t, ht, _⟩ := E.toScalarIsogenyPresentation.exists_quasiIsogeny
    hπ hM.piDivisible hN.piDivisible
  obtain ⟨G, hG⟩ := E.exists_inverse hπ (by omega) hH hM hN t ht
  have hf : ofRational U t.hom = e.hom := by
    rw [ht]
    exact P.ofRational_openTensor hπ
  have hi : ofRational U t.inv = e.inv := by
    apply e.inv_unique
    rw [← hf]
    exact (comp_ofRational (U := U) (M := M) (N := N) (P := M) t.inv t.hom).trans
      (congrArg (fun z => ofRational (F := F) (M := M) (N := M) U z) t.inv_hom)
  let Q : HeightPresentation π q e.inv :=
    { exponent := G.exponent
      representative := G.representative
      numeratorHeight := G.numeratorHeight
      denominatorHeight := G.exponent * H
      numerator := ⟨G.isIsogeny, G.numeratorRank⟩
      denominator := hN.scalarPower_height _
      represents := by
        rw [← hi]
        let a := (algebraMap O F π) ^ G.exponent
        let μ := ofRational (F := F) (M := N) (N := M) U
        change a • μ t.inv = μ (RationalHom.ofHom G.representative)
        exact (μ.map_smul a t.inv).symm.trans (congrArg (fun z => μ z) G.represents) }
  refine ⟨Q, ?_⟩
  have hP : E.index H = P.index := by
    change (P.numeratorHeight : ℤ) - (P.exponent : ℤ) * H =
      (P.numeratorHeight : ℤ) - (P.denominatorHeight : ℤ)
    rw [P.denominatorHeight_eq hq hM, Nat.cast_mul]
  simpa only [Q, index, RationalHom.GlobalHeightPresentation.index, Nat.cast_mul] using
    hG.trans (congrArg Neg.neg hP)

end RationalSection.HeightPresentation

namespace RationalSection.HasHeightFunction

variable [IsDomain O] [IsFractionRing O F]

/-- Pointwise negation of an actual rational section's height function is the
height function of its actual inverse. -/
theorem inverse (e : RationalSectionIso F M N U) (hπ : algebraMap O F π ≠ 0)
    (hq : 2 ≤ q) (hH : 0 < H) (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H)
    {s : U → ℤ} (hh : HasHeightFunction π q e.hom s) :
    HasHeightFunction π q e.inv (fun x => -s x) := by
  intro x
  obtain ⟨V, hxV, i, P, hP⟩ := hh x
  let T := (coefficientStructurePresheaf R).obj (op V)
  let φ : R →ₐ[O] T := IsScalarTower.toAlgHom O R T
  let : Nontrivial ((Spec.structureSheaf R).presheaf.stalk (x : PrimeSpectrum R)) :=
    IsLocalization.AtPrime.nontrivial _ x.val.asIdeal
  let : Nontrivial T :=
    ((Spec.structureSheaf R).presheaf.germ V (x : PrimeSpectrum R) hxV).hom.domain_nontrivial
  obtain ⟨Q, hQ⟩ := P.exists_inverse (e.restrict i) hπ hq hH (hM.map φ) (hN.map φ)
  exact ⟨V, hxV, i, Q, fun y => (congrArg Neg.neg (hP y)).trans hQ.symm⟩

end RationalSection.HasHeightFunction

namespace BasicAtlas.QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

/-- Negation holds on all the same cover tests of the actual inverse atlas map. -/
theorem inv_hasConstantChartHeight (e : QuasiIsogeny F X Y h)
    (hπ : algebraMap O F π ≠ 0) (hq : 2 ≤ q) (hH : 0 < H)
    (hX : ∀ b : X.opens, (X.chart b).HasPiHeight π q H)
    (hY : ∀ b : Y.opens, (Y.chart b).HasPiHeight π q H)
    {n : ℤ} (he : e.hom.HasConstantChartHeight π q n) :
    e.inv.HasConstantChartHeight π q (-n) := by
  intro A a ha
  let b := sourceChart h.symm a
  exact RationalSection.HasHeightFunction.inverse
    (RationalSectionIso.ofQuasiIsogeny (e.onChart A b ha) ⊤) hπ hq hH
    ((hX a).map (coefficientLift a.val A ha))
    ((hY b).map (coefficientLift a.val A ha)) (he A b ha)

end BasicAtlas.QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
