import Langlands.AlgebraicGeometry.Modules.EqualCompositeTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Mul
import Langlands.AlgebraicGeometry.Modules.UnitAutomorphisms

/-! # Scalar cancellation in restrictions of tensor contractions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- The right tensor unitor carries a unit on the structure module to the same scalar. -/
lemma tensorRightUnitor_unitAut {X : Scheme.{u}} (L : X.Modules) (c : Γ(X, ⊤)ˣ) :
    tensorMap (𝟙 L) (unitAut (structureSheaf X) c).hom ≫
        (tensorRightUnitor L).hom =
      (tensorRightUnitor L).hom ≫ (unitAut L c).hom := by
  have hc : unitEndCoefficient (unitAut (structureSheaf X) c).hom ⊤ =
      (c : Γ(X, ⊤)) := by
    change (((c : Γ(X, ⊤)) • 𝟙 (structureSheaf X)).app ⊤
      (1 : Γ(X, ⊤))) = _
    simp only [global_smul_app]
    change X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) (c : Γ(X, ⊤)) * 1 = _
    simp
  have h := SerreVanishing.tensorMap_id_unitEnd L
    (unitAut (structureSheaf X) c).hom
  rw [hc] at h
  exact h

/-- Pullback preserves contraction with an actual structure-module coordinate. -/
lemma tensorContraction_pullback {X Y : Scheme.{u}} (r : X ⟶ Y)
    {A B L : Y.Modules} (a : A ⟶ L) (b : B ⟶ structureSheaf Y) :
    (Scheme.Modules.pullback r).map
        (tensorMap a b ≫ (tensorRightUnitor L).hom) =
      pullbackTensorComparisonApp r A B ≫
        tensorMap ((Scheme.Modules.pullback r).map a)
          ((Scheme.Modules.pullback r).map b ≫ (pullbackUnitIso r).hom) ≫
        (tensorRightUnitor ((Scheme.Modules.pullback r).obj L)).hom := by
  rw [Functor.map_comp, ← pullbackTensorRightUnitor X Y r L]
  rw [reassoc_of% (pullbackTensorComparisonApp_naturality r a b)]
  rw [← Category.assoc (tensorMap _ _) (tensorMap _ _), tensorMap_comp]
  simp only [Category.comp_id]

/-- A scalar on the line coordinate becomes the same scalar after contraction. -/
lemma tensorContraction_scaled {X : Scheme.{u}}
    {A B L K : X.Modules} (a : A ⟶ L) (b : B ⟶ structureSheaf X)
    (g : L ⟶ K) (c : Γ(X, ⊤)ˣ) :
    tensorMap a b ≫ (tensorRightUnitor L).hom ≫ g ≫ (unitAut K c).hom =
      tensorMap (a ≫ g) (b ≫ (unitAut (structureSheaf X) c).hom) ≫
        (tensorRightUnitor K).hom := by
  have ht :
      tensorMap (a ≫ g) (b ≫ (unitAut (structureSheaf X) c).hom) =
        tensorMap a b ≫ tensorMap g (𝟙 (structureSheaf X)) ≫
          tensorMap (𝟙 K) (unitAut (structureSheaf X) c).hom := by
    rw [tensorMap_comp, tensorMap_comp]
    simp
  rw [ht]
  simp only [Category.assoc]
  rw [tensorRightUnitor_unitAut, reassoc_of% (tensorRightUnitor_naturality g)]

/-- Contract two actual chart comparisons when the second one trivializes a line. -/
def tensorChartContractionIso {X T : Scheme.{u}} (j : T ⟶ X)
    {A B : X.Modules} {L : T.Modules}
    (a : (Scheme.Modules.pullback j).obj A ≅ L)
    (b : (Scheme.Modules.pullback j).obj B ≅ structureSheaf T) :
    (Scheme.Modules.pullback j).obj (tensorObj A B) ≅ L := by
  letI := pullbackTensorComparisonIsIso j
  exact (asIso (pullbackTensorComparison j)).app (A, B) ≪≫
    (tensorFunctor T).mapIso (a.prod b) ≪≫ tensorRightUnitor L

/-- The contraction isomorphism has the canonical tensor-comparison morphism. -/
lemma tensorChartContractionIso_hom {X T : Scheme.{u}} (j : T ⟶ X)
    {A B : X.Modules} {L : T.Modules}
    (a : (Scheme.Modules.pullback j).obj A ≅ L)
    (b : (Scheme.Modules.pullback j).obj B ≅ structureSheaf T) :
    (tensorChartContractionIso j a b).hom =
      pullbackTensorComparisonApp j A B ≫ tensorMap a.hom b.hom ≫
        (tensorRightUnitor L).hom := rfl

/-- Opposite coordinate scalars cancel in the restriction of a tensor contraction. -/
lemma tensorChartContractionIso_restrict {X U V : Scheme.{u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (r : U ⟶ V) (hr : r ≫ jV = jU)
    {A B : X.Modules} {LU : U.Modules} {LV : V.Modules}
    (aU : (Scheme.Modules.pullback jU).obj A ≅ LU)
    (aV : (Scheme.Modules.pullback jV).obj A ≅ LV)
    (bU : (Scheme.Modules.pullback jU).obj B ≅ structureSheaf U)
    (bV : (Scheme.Modules.pullback jV).obj B ≅ structureSheaf V)
    (γ : (Scheme.Modules.pullback r).obj LV ⟶ LU) (c : Γ(U, ⊤)ˣ)
    (ha : (Scheme.Modules.pullback r).map aV.hom ≫ γ =
      compHom r jV jU hr A ≫ aU.hom)
    (hb : (Scheme.Modules.pullback r).map bV.hom ≫ (pullbackUnitIso r).hom ≫
        (unitAut (structureSheaf U) c).hom =
      compHom r jV jU hr B ≫ bU.hom) :
    (Scheme.Modules.pullback r).map (tensorChartContractionIso jV aV bV).hom ≫
        γ ≫ (unitAut LU c).hom =
      compHom r jV jU hr (tensorObj A B) ≫
        (tensorChartContractionIso jU aU bU).hom := by
  rw [tensorChartContractionIso_hom, tensorChartContractionIso_hom,
    Functor.map_comp, tensorContraction_pullback]
  simp only [Category.assoc]
  rw [tensorContraction_scaled, ha]
  simp only [Category.assoc]
  rw [hb]
  rw [reassoc_of% (compHom_tensor r jV jU hr A B)]
  rw [← Category.assoc (tensorMap _ _) (tensorMap _ _), tensorMap_comp]

end Langlands.Scheme.Modules
