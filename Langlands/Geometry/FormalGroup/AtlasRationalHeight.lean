import Langlands.Geometry.FormalGroup.RationalHeight
import Langlands.Geometry.FormalGroup.ScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.SpecialAtlas
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism

/-! # Local kernel-rank height conditions on actual rational atlas maps -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace RationalSection.HasHeightFunction

/-- An actual integral isomorphism has local rank difference zero. -/
theorem ofIntegralIso (π : O) (q : ℕ) {U : Opens (PrimeSpectrum R)}
    (e : Iso (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))
      (N.overAlgebra ((coefficientStructurePresheaf R).obj (op U)))) :
    HasHeightFunction π q (ofIntegral U e.hom : RationalSection F M N U)
      (fun _ => 0) := by
  intro x
  let P : HeightPresentation π q (RationalSection.restrict (𝟙 U)
      (ofIntegral U e.hom : RationalSection F M N U)) := {
    exponent := 0
    representative := e.hom
    numeratorHeight := 0
    denominatorHeight := 0
    numerator := e.hasHeight_zero q
    denominator := by
      rw [pow_zero, scalarHom_one]
      exact (Iso.refl _).hasHeight_zero q
    represents := by rw [pow_zero, one_smul, restrict_id] }
  exact ⟨U, x.property, 𝟙 U, P, fun _ => rfl⟩

/-- The section of the rationalized global isomorphism has height zero. -/
theorem ofGlobalIso (π : O) (q : ℕ) (e : Iso M N) :
    HasHeightFunction π q (ofGlobal (RationalHom.ofHom (F := F) e.hom))
      (fun _ => 0) := by
  rw [ofGlobal_ofHom]
  exact ofIntegralIso π q
    (e.map (IsScalarTower.toAlgHom O R
      ((coefficientStructurePresheaf R).obj (op ⊤))))

end RationalSection.HasHeightFunction

namespace BasicAtlas.RationalHom

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens}

/-- The specified integer is the actual local kernel-rank difference on every
test extension of every target chart. Denominators may vary by neighbourhood. -/
def HasConstantChartHeight (f : BasicAtlas.RationalHom F X Y h)
    (π : O) (q : ℕ) (n : ℤ) : Prop :=
  ∀ (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)),
    RationalSection.HasHeightFunction π q
      (RationalSection.ofGlobal (onChart (X := X) (h := h) A b hb f))
      (fun _ => n)

namespace HasConstantChartHeight

variable {π : O} {q : ℕ} {n : ℤ}
variable {f : BasicAtlas.RationalHom F X Y h}

/-- Each chart section is locally a scalar multiple of an actual integral isogeny. -/
theorem isLocallyScalarIsogeny (hf : f.HasConstantChartHeight π q n)
    (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    RationalSection.IsLocallyScalarIsogeny π
      (RationalSection.ofGlobal (onChart (X := X) (h := h) A b hb f)) :=
  (hf A b hb).isLocallyScalarIsogeny

/-- The actual rank relation restricts to any open subset of a test chart. -/
theorem restrict (hf : f.HasConstantChartHeight π q n)
    (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (U : Opens (PrimeSpectrum A)) :
    RationalSection.HasHeightFunction π q
      (RationalSection.restrict (homOfLE (show U ≤ ⊤ from le_top))
        (RationalSection.ofGlobal (onChart (X := X) (h := h) A b hb f)))
      (fun _ => n) :=
  (hf A b hb).restrict _

/-- Source and target scalar divisibility upgrade the rank condition to the
existing genuine local quasi-isogeny on the whole test chart. -/
def localQuasiIsogeny (hf : f.HasConstantChartHeight π q n)
    (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (hX : ((X.chart (sourceChart h b)).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π)
    (hY : ((Y.chart b).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π) :
    LocalQuasiIsogeny F π
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val A hb)) ⊤ where
  scalar_ne_zero := hπ
  source_divisible := hX
  target_divisible := hY
  val := RationalSection.ofGlobal (onChart (X := X) (h := h) A b hb f)
  isLocal := hf.isLocallyScalarIsogeny A b hb

@[simp]
theorem localQuasiIsogeny_val (hf : f.HasConstantChartHeight π q n)
    (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (hX : ((X.chart (sourceChart h b)).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π)
    (hY : ((Y.chart b).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π) :
    (hf.localQuasiIsogeny hπ A b hb hX hY).val =
      RationalSection.ofGlobal (onChart (X := X) (h := h) A b hb f) := rfl

end HasConstantChartHeight

end BasicAtlas.RationalHom

namespace BasicAtlas.OrderAction

variable {D : Type w} [Ring D] [Algebra O D]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {h : X.opens = Y.opens}

/-- Rationalization of an actual full-order formal isomorphism satisfies the
local zero-height relation on every test chart. -/
theorem Iso.hasConstantChartHeight_zero (e : Iso E E' h) (π : O) (q : ℕ) :
    (RationalHom.ofHom (F := F) e.hom).val.HasConstantChartHeight π q 0 := by
  intro A b hb
  rw [RationalHom.ofHom_val, BasicAtlas.RationalHom.onChart_ofHom]
  exact RationalSection.HasHeightFunction.ofGlobalIso π q
    (e.onChart A b hb).toModuleIso

end BasicAtlas.OrderAction

end Langlands.FormalGroup.ModuleLaw
