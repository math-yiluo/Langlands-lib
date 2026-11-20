import Langlands.Geometry.FormalGroup.AtlasRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasLocalTests
import Langlands.Geometry.FormalGroup.ZariskiDescent
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic

/-! # Finite-cover detection for whole rational formal atlas maps -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory
open scoped TensorProduct

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The canonical chart test at the localization of the original base. -/
def principalChartAlgebra (r : R) : CommAlgCat.{v} R :=
  CommAlgCat.of R (Localization.Away r)

theorem principalChartAlgebra_unit (r : R) :
    IsUnit (algebraMap R (principalChartAlgebra r) r) := by
  change IsUnit (algebraMap R (Localization.Away r) r)
  exact IsLocalization.Away.algebraMap_isUnit r

set_option backward.isDefEq.respectTransparency false in
/-- A common principal subcover detects the whole integral atlas homomorphism by
its maps over the canonical localizations of the base. -/
theorem Hom.ext_onPrincipalSubcover (s : Set R) (hsub : s ⊆ Y.opens) (hs : Ideal.span s = ⊤)
    {f g : Hom X Y h}
    (e : ∀ a : s, f.hom (principalChartAlgebra a.val) ⟨a.val, hsub a.property⟩
      (principalChartAlgebra_unit a.val) = g.hom (principalChartAlgebra a.val)
        ⟨a.val, hsub a.property⟩ (principalChartAlgebra_unit a.val)) : f = g := by
  apply Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  have hsA : Ideal.span ((algebraMap R A) '' s) = ⊤ := by
    rw [← Ideal.map_span, hs, Ideal.map_top]
  apply CoordinateMap.ext_basic _ hsA
  rintro ⟨x, a, ha, rfl⟩
  let c : Y.opens := ⟨a, hsub ha⟩
  let B := Y.localAlgebra A c
  let : Algebra O B := coefficientAlgebra B
  let u := Y.localizationMap A c
  have hbB : IsUnit (algebraMap R B b.val) := by
    rw [← u.hom.commutes b.val]
    exact hb.map u.hom.toMonoidHom
  have hcB : IsUnit (algebraMap R B c.val) := Y.localUnit A c
  let v : principalChartAlgebra a ⟶ B :=
    CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R B) hcB)
  have e₀ := congrArg (fun m => m.toHom.toCoordinateMap) (e ⟨a, ha⟩)
  have ec : f.hom B c hcB = g.hom B c hcB := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    exact (f.natural v c (principalChartAlgebra_unit a) hcB).symm.trans
      ((congrArg (fun m => m.map v.hom.toRingHom) e₀).trans
        (g.natural v c (principalChartAlgebra_unit a) hcB))
  have et := (f.transition B b c hbB hcB).trans
    ((congrArg (fun m => m.comp (X.transition B (sourceChart h b) (sourceChart h c) hbB hcB).hom)
      ec).trans (g.transition B b c hbB hcB).symm)
  have eb := congrArg (fun m => (Y.transition B b c hbB hcB).inv.comp m) et
  simp only [← ModuleLaw.Hom.comp_assoc, ModuleLaw.Iso.inv_hom, ModuleLaw.Hom.id_comp] at eb
  exact (f.natural u b hb hbB).trans
    ((congrArg (fun m => m.toHom.toCoordinateMap) eb).trans (g.natural u b hb hbB).symm)

/-- The integral formal Hom on one canonical test of a chosen subset of the common cover. -/
abbrev Hom.PrincipalChartHom (s : Set R) (hsub : s ⊆ Y.opens) (a : s) :=
  ModuleLaw.Hom
    ((X.chart (sourceChart h ⟨a.val, hsub a.property⟩)).map
      (coefficientLift (O := O) a.val (principalChartAlgebra a.val) (principalChartAlgebra_unit a.val)))
    ((Y.chart ⟨a.val, hsub a.property⟩).map
      (coefficientLift (O := O) a.val (principalChartAlgebra a.val) (principalChartAlgebra_unit a.val)))

private def integralChartEvaluation (s : Set R) (hsub : s ⊆ Y.opens) :
    Hom X Y h →ₗ[O] ((a : s) → Hom.PrincipalChartHom (X := X) (h := h) s hsub a) :=
  LinearMap.pi (fun a => Hom.chartLinear (X := X) (h := h) (principalChartAlgebra a.val)
    ⟨a.val, hsub a.property⟩ (principalChartAlgebra_unit a.val))

private theorem integralChartEvaluation_injective (s : Set R) (hsub : s ⊆ Y.opens)
    (hs : Ideal.span s = ⊤) :
    Function.Injective (integralChartEvaluation (X := X) (h := h) s hsub) := by
  intro f g e
  exact Hom.ext_onPrincipalSubcover s hsub hs (fun a => congrFun e a)

variable {F : Type w} [Field F] [Algebra O F]

/-- Evaluate the whole rational formal map at the canonical principal tests of a chosen subset. -/
def RationalHom.principalChartEvaluation (s : Set R) (hsub : s ⊆ Y.opens) :
    RationalHom F X Y h →ₗ[F] ((a : s) → F ⊗[O] Hom.PrincipalChartHom (X := X) (h := h) s hsub a) :=
  (TensorProduct.piRightHom O F F (Hom.PrincipalChartHom (X := X) (h := h) s hsub)).comp
    ((integralChartEvaluation (X := X) (h := h) s hsub).baseChange F)

@[simp]
theorem RationalHom.principalChartEvaluation_apply (s : Set R) (hsub : s ⊆ Y.opens)
    (t : RationalHom F X Y h) (a : s) :
    RationalHom.principalChartEvaluation s hsub t a =
      RationalHom.onChart (F := F) (X := X) (h := h) (principalChartAlgebra a.val)
        ⟨a.val, hsub a.property⟩ (principalChartAlgebra_unit a.val) t := by
  induction t using TensorProduct.inductionOn with
  | tmul k m => rfl
  | add f g ef eg => simp only [map_add, Pi.add_apply, ef, eg]

/-- For flat scalar extension a finite principal subcover detects equality in the
whole rational atlas Hom. Finiteness lets tensoring commute with the chosen product. -/
theorem RationalHom.ext_onFinitePrincipalSubcover [Module.Flat O F]
    (s : Finset R) (hsub : (s : Set R) ⊆ Y.opens) (hs : Ideal.span (s : Set R) = ⊤)
    {f g : RationalHom F X Y h}
    (e : ∀ a : (s : Set R), RationalHom.onChart (F := F) (X := X) (h := h) (principalChartAlgebra a.val)
      ⟨a.val, hsub a.property⟩ (principalChartAlgebra_unit a.val) f =
      RationalHom.onChart (F := F) (X := X) (h := h) (principalChartAlgebra a.val)
        ⟨a.val, hsub a.property⟩ (principalChartAlgebra_unit a.val) g) : f = g := by
  classical
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := F)
    (integralChartEvaluation (X := X) (h := h) (s : Set R) hsub)
    (integralChartEvaluation_injective (X := X) (h := h) (s : Set R) hsub hs)
  apply (TensorProduct.piRight O F F (Hom.PrincipalChartHom (X := X) (h := h) (s : Set R) hsub)).injective
  change RationalHom.principalChartEvaluation (s : Set R) hsub f =
    RationalHom.principalChartEvaluation (s : Set R) hsub g
  funext a
  simpa only [RationalHom.principalChartEvaluation_apply] using e a

/-- The original chart evaluations jointly detect whole rational atlas maps. -/
theorem RationalHom.ext_onCharts [Module.Flat O F] {f g : RationalHom F X Y h}
    (e : ∀ (A : CommAlgCat.{v} R) (a : Y.opens) (ha : IsUnit (algebraMap R A a.val)),
      RationalHom.onChart (F := F) (X := X) (h := h) A a ha f =
        RationalHom.onChart (F := F) (X := X) (h := h) A a ha g) : f = g := by
  obtain ⟨s, hs, hm⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp Y.covers)
  apply RationalHom.ext_onFinitePrincipalSubcover s hs ((Ideal.eq_top_iff_one _).mpr hm)
  intro a
  exact e (principalChartAlgebra a.val) ⟨a.val, hs a.property⟩ (principalChartAlgebra_unit a.val)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
