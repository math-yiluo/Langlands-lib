import Langlands.AlgebraicGeometry.FieldTwoAxisRigidityStatement
import Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidityProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Two-axis rigidity over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
private theorem algebraicallyClosedTensor
    (K : Type u) [Field K] [IsAlgClosed K]
    (Y Z P : Over (Spec (CommRingCat.of K)))
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    [Smooth Z.hom] [IsProper Z.hom] [GeometricallyConnected Z.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom]
    (y₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z)
    (p₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P)
    (g : Y ⊗ Z ⟶ P)
    (hy : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ g = toUnit Z ≫ p₀)
    (hz : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ g = toUnit Y ≫ p₀) :
    g = toUnit (Y ⊗ Z) ≫ p₀ := by
  let A := Y ⊗ Z
  let a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A := lift y₀ z₀
  let cross : A ⊗ A ⟶ A := lift (fst A A ≫ fst Y Z) (snd A A ≫ snd Y Z)
  let h : A ⊗ A ⟶ P := cross ≫ g
  have : Smooth A.hom := by dsimp [A]; infer_instance
  have : IsProper A.hom := by dsimp [A]; infer_instance
  have : GeometricallyConnected A.hom := by
    exact GeometricallyConnected.comp (pullback.fst Y.hom Z.hom) Y.hom
  have : GeometricallyIntegral A.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality
      K A.left A.hom inferInstance inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral (A ⊗ A).left := by dsimp; infer_instance
  have hyh : (a ▷ A) ≫ h = toUnit _ ≫ p₀ := by
    have hc : (a ▷ A) ≫ cross =
        (snd _ A ≫ snd Y Z) ≫ lift (toUnit Z ≫ y₀) (𝟙 Z) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [cross, Category.assoc, lift_fst, whiskerRight_fst_assoc,
          a, lift_fst, comp_toUnit_assoc]
        exact congrArg (fun f => f ≫ y₀) (toUnit_unique _ _)
      · simp [cross]
    dsimp [h]
    rw [← Category.assoc, hc, Category.assoc, hy]
    simp
  have hzh : (A ◁ a) ≫ h = toUnit _ ≫ p₀ := by
    have hc : (A ◁ a) ≫ cross =
        (fst A _ ≫ fst Y Z) ≫ lift (𝟙 Y) (toUnit Y ≫ z₀) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [cross]
      · simp only [cross, Category.assoc, lift_snd, whiskerLeft_snd_assoc,
          a, lift_snd, comp_toUnit_assoc]
        exact congrArg (fun f => f ≫ z₀) (toUnit_unique _ _)
    dsimp [h]
    rw [← Category.assoc, hc, Category.assoc, hz]
    simp
  have hh := Langlands.AbelianScheme.algebraicallyClosedTwoAxisRigidity K A P
    inferInstance inferInstance inferInstance inferInstance a p₀ h hyh hzh
  have hc : lift (𝟙 A) (𝟙 A) ≫ cross = 𝟙 A := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [cross, A]
  have heq := congrArg (fun f : A ⊗ A ⟶ P => lift (𝟙 A) (𝟙 A) ≫ f) hh
  simpa only [h, ← Category.assoc, hc, Category.id_comp, comp_toUnit] using heq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fieldTensor
    (K : Type u) [Field K]
    (Y Z P : Over (Spec (CommRingCat.of K)))
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    [Smooth Z.hom] [IsProper Z.hom] [GeometricallyConnected Z.hom]
    [IsSeparated P.hom] [LocallyOfFiniteType P.hom]
    (y₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z)
    (p₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P)
    (g : Y ⊗ Z ⟶ P)
    (hy : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ g = toUnit Z ≫ p₀)
    (hz : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ g = toUnit Y ≫ p₀) :
    g = toUnit (Y ⊗ Z) ≫ p₀ := by
  let b := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback b
  let Y' := F.obj Y
  let Z' := F.obj Z
  let P' := F.obj P
  have : Smooth Y'.hom := by dsimp [Y', F]; infer_instance
  have : IsProper Y'.hom := by dsimp [Y', F]; infer_instance
  have : GeometricallyConnected Y'.hom := by dsimp [Y', F]; infer_instance
  have : Smooth Z'.hom := by dsimp [Z', F]; infer_instance
  have : IsProper Z'.hom := by dsimp [Z', F]; infer_instance
  have : GeometricallyConnected Z'.hom := by dsimp [Z', F]; infer_instance
  have : IsSeparated P'.hom := by dsimp [P', F]; infer_instance
  have : LocallyOfFiniteType P'.hom := by dsimp [P', F]; infer_instance
  let y' : 𝟙_ _ ⟶ Y' := Functor.LaxMonoidal.ε F ≫ F.map y₀
  let z' : 𝟙_ _ ⟶ Z' := Functor.LaxMonoidal.ε F ≫ F.map z₀
  let p' : 𝟙_ _ ⟶ P' := Functor.LaxMonoidal.ε F ≫ F.map p₀
  let g' : Y' ⊗ Z' ⟶ P' := Functor.LaxMonoidal.μ F Y Z ≫ F.map g
  have hy' : lift (toUnit Z' ≫ y') (𝟙 Z') ≫ g' = toUnit Z' ≫ p' := by
    have he : lift (toUnit Z' ≫ y') (𝟙 Z') ≫ Functor.LaxMonoidal.μ F Y Z =
        F.map (lift (toUnit Z ≫ y₀) (𝟙 Z)) := by
      simpa only [y', Z', F.map_comp, F.map_id, Category.assoc,
        ← Functor.Monoidal.toUnit_ε_assoc] using
        (Functor.Monoidal.lift_μ (F := F) (toUnit Z ≫ y₀) (𝟙 Z))
    dsimp only [g']
    rw [← Category.assoc, he, ← F.map_comp, hy, F.map_comp]
    simp only [p', Z', Functor.Monoidal.toUnit_ε_assoc]
  have hz' : lift (𝟙 Y') (toUnit Y' ≫ z') ≫ g' = toUnit Y' ≫ p' := by
    have he : lift (𝟙 Y') (toUnit Y' ≫ z') ≫ Functor.LaxMonoidal.μ F Y Z =
        F.map (lift (𝟙 Y) (toUnit Y ≫ z₀)) := by
      simpa only [z', Y', F.map_comp, F.map_id, Category.assoc,
        ← Functor.Monoidal.toUnit_ε_assoc] using
        (Functor.Monoidal.lift_μ (F := F) (𝟙 Y) (toUnit Y ≫ z₀))
    dsimp only [g']
    rw [← Category.assoc, he, ← F.map_comp, hz, F.map_comp]
    simp only [p', Y', Functor.Monoidal.toUnit_ε_assoc]
  have hg' := algebraicallyClosedTensor (AlgebraicClosure K) Y' Z' P'
    y' z' p' g' hy' hz'
  apply F.map_injective
  apply (cancel_epi (Functor.Monoidal.μIso F Y Z).hom).mp
  simpa only [Functor.map_comp, g', p', Y', Z', Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.Monoidal.toUnit_ε_assoc, comp_toUnit_assoc] using hg'

set_option backward.defeqAttrib.useBackward true in
/-- Two-axis rigidity for smooth proper geometrically connected pointed products
over any field, with separated locally finite type target. -/
theorem fieldTwoAxisRigidity : FieldTwoAxisRigidityStatement.{u} := by
  intro K _ Y Z P hYS hYP hYC hZS hZP hZC hPS hPF y₀ z₀ p₀ g hy hz
  have := hYS
  have := hYP
  have := hYC
  have := hZS
  have := hZP
  have := hZC
  have := hPS
  have := hPF
  let e : Y ⊗ Z ≅ Y ⨯ Z :=
    { hom := prod.lift (fst Y Z) (snd Y Z)
      inv := lift (prod.fst : Y ⨯ Z ⟶ Y) (prod.snd : Y ⨯ Z ⟶ Z)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      inv_hom_id := by
        apply prod.hom_ext <;> simp }
  have hterminal (X : Over (Spec (CommRingCat.of K))) :
      toUnit X = Over.mkIdTerminal.from X := toUnit_unique _ _
  have hy' : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ (e.hom ≫ g) = toUnit Z ≫ p₀ := by
    have he : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ e.hom =
        prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z) := by
      apply prod.hom_ext <;> simp [e, hterminal]
    rw [← Category.assoc, he, hy, hterminal]
  have hz' : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ (e.hom ≫ g) = toUnit Y ≫ p₀ := by
    have he : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ e.hom =
        prod.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀) := by
      apply prod.hom_ext <;> simp [e, hterminal]
    rw [← Category.assoc, he, hz, hterminal]
  have ht := fieldTensor K Y Z P y₀ z₀ p₀ (e.hom ≫ g) hy' hz'
  have heq := congrArg (fun f : Y ⊗ Z ⟶ P => e.inv ≫ f) ht
  have hconstant : e.inv ≫ toUnit (Y ⊗ Z) =
      Over.mkIdTerminal.from (Y ⨯ Z) := toUnit_unique _ _
  simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp, hconstant] using heq

end Langlands.AlgebraicGeometry
