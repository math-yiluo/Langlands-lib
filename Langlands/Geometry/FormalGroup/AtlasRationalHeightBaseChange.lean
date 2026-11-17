import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.AtlasRationalBaseChangeAlong

/-! # Actual local rational heights through coefficient extension -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom.HasConstantChartHeight

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {π : O} {q : ℕ} {n : ℤ}

section AlgebraTransport

variable {α : Algebra O R}
variable {X : @BasicAtlas O _ R _ α σ _} {Y : @BasicAtlas O _ R _ α τ _}
variable {h : X.opens = Y.opens}
variable {g : (letI := α; BasicAtlas.RationalHom F X Y h)}

/-- Retyping equal scalar structures preserves the actual local kernel-rank condition. -/
theorem reAlgebra (hg : (letI := α; g.HasConstantChartHeight π q n))
    (β : Algebra O R) (e : α = β) :
    (letI := β; (BasicAtlas.RationalHom.reAlgebra β e g).HasConstantChartHeight π q n) := by
  cases e
  exact hg

end AlgebraTransport

variable [Algebra O R] [Algebra O S]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {h : X.opens = Y.opens} {g : BasicAtlas.RationalHom F X Y h}

/-- Restricting each test algebra and changing its actual chart coordinates retains height. -/
theorem baseChange (hg : g.HasConstantChartHeight π q n) (T : CommAlgCat.{v} R) :
    (BasicAtlas.RationalHom.baseChange (X := X) (Y := Y) (h := h) T g).HasConstantChartHeight π q n := by
  intro A b hb
  rw [BasicAtlas.RationalHom.onChart_baseChange g T A b hb]
  have ht := (hg (BasicAtlas.restrictTest T A) (Y.baseSource T b)
    (Y.baseSource_unit T A b hb)).ofGlobal_isoTransport
      (baseSourceChartIso T h A b hb).symm (Y.baseChartIso T A b hb).symm
  have he := ModuleLaw.RationalHom.isoTransport_eq_comp
    (baseSourceChartIso T h A b hb).symm (Y.baseChartIso T A b hb).symm
    (BasicAtlas.RationalHom.onChart (X := X) (Y := Y) (h := h)
      (BasicAtlas.restrictTest T A) (Y.baseSource T b) (Y.baseSource_unit T A b hb) g)
  exact (congrArg
    (fun z => RationalSection.HasHeightFunction π q (RationalSection.ofGlobal z) (fun _ => n))
    he).mp ht

/-- The same signed kernel-rank height survives extension to supplied target scalars. -/
theorem baseChangeAlong (hg : g.HasConstantChartHeight π q n) (f : R →ₐ[O] S) :
    (BasicAtlas.RationalHom.baseChangeAlong (X := X) (Y := Y) (h := h) f g).HasConstantChartHeight π q n := by
  let T : CommAlgCat.{v} R := coefficientTest f
  exact (hg.baseChange T).reAlgebra _ (coefficientAlgebraAlong_eq f)

/-- The actual extended rational tensor gives a genuine local quasi-isogeny
on any test chart with the supplied scalar divisibility. -/
def baseChangedLocalQuasiIsogeny (hg : g.HasConstantChartHeight π q n)
    (f : R →ₐ[O] S) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val))
    (hX : (((X.baseChangeAlong f).chart
      (sourceChart (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (baseOpens_eq (coefficientTest f) h) b)).map
        (coefficientLift (O := O) b.val A hb)).IsPiDivisible π)
    (hY : (((Y.baseChangeAlong f).chart b).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π) :
    LocalQuasiIsogeny F π
      (((X.baseChangeAlong f).chart
        (sourceChart (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (baseOpens_eq (coefficientTest f) h) b)).map
          (coefficientLift (O := O) b.val A hb))
      (((Y.baseChangeAlong f).chart b).map (coefficientLift (O := O) b.val A hb)) ⊤ :=
  (hg.baseChangeAlong f).localQuasiIsogeny hπ A b hb hX hY

@[simp]
theorem baseChangedLocalQuasiIsogeny_val (hg : g.HasConstantChartHeight π q n)
    (f : R →ₐ[O] S) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val))
    (hX : (((X.baseChangeAlong f).chart
      (sourceChart (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (baseOpens_eq (coefficientTest f) h) b)).map
        (coefficientLift (O := O) b.val A hb)).IsPiDivisible π)
    (hY : (((Y.baseChangeAlong f).chart b).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π) :
    (hg.baseChangedLocalQuasiIsogeny f hπ A b hb hX hY).val =
      RationalSection.ofGlobal
        (BasicAtlas.RationalHom.onChart
          (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
          (h := baseOpens_eq (coefficientTest f) h) A b hb
          (BasicAtlas.RationalHom.baseChangeAlong (X := X) (Y := Y) (h := h) f g)) := rfl

/-- The constructed local extended map retains the prescribed signed height. -/
theorem baseChangedLocalQuasiIsogeny_height (hg : g.HasConstantChartHeight π q n)
    (f : R →ₐ[O] S) (hπ : algebraMap O F π ≠ 0)
    (A : CommAlgCat.{v} S) (b : (Y.baseChangeAlong f).opens)
    (hb : IsUnit (algebraMap S A b.val))
    (hX : (((X.baseChangeAlong f).chart
      (sourceChart (X := X.baseChangeAlong f) (Y := Y.baseChangeAlong f)
        (baseOpens_eq (coefficientTest f) h) b)).map
        (coefficientLift (O := O) b.val A hb)).IsPiDivisible π)
    (hY : (((Y.baseChangeAlong f).chart b).map
      (coefficientLift (O := O) b.val A hb)).IsPiDivisible π) :
    RationalSection.HasHeightFunction π q
      (hg.baseChangedLocalQuasiIsogeny f hπ A b hb hX hY).val (fun _ => n) :=
  hg.baseChangeAlong f A b hb

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom.HasConstantChartHeight
