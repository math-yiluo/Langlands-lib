import Langlands.Sheaf.Equivariant.Godement.Complex
import Langlands.Sheaf.Equivariant.Godement.SpatialZero
import Langlands.Cohomology.CokernelComplex.LaxMap
import Langlands.Cohomology.ProperCompactComplexes

/-! # Actual spatial comparisons of equivariant Godement complexes -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Godement.Spatial

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The genuine higher comparison constructed from the spatial stalk map. -/
def complexMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ⟶
      (Langlands.Cohomology.ProperCompactComplexes.directImageComplex
        (ComplexShape.up ℕ) f hf).obj (complex R G X F) :=
  Langlands.Cohomology.CokernelComplex.Lax.complexMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- The actual chain comparison is natural in every original sheaf morphism. -/
def complexNatTrans :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ complexFunctor R G Y ⟶
      complexFunctor R G X ⋙
        Langlands.Cohomology.ProperCompactComplexes.directImageComplex
          (ComplexShape.up ℕ) f hf :=
  Langlands.Cohomology.CokernelComplex.Lax.functorMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf)

@[simp]
theorem complexNatTrans_app (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (complexNatTrans f hf).app F = complexMap f hf F := rfl

/-- Degree zero retains the original neighborhood-colimit stalk-family map. -/
@[simp]
theorem complexMap_f_zero (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (complexMap f hf F).f 0 = zeroMap f hf F :=
  Langlands.Cohomology.CokernelComplex.Lax.termMap_zero
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- The actual family of germs is preserved by the chain comparison. -/
@[reassoc]
theorem augmentation_complexMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    augmentation R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (complexMap f hf F).f 0 =
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).map (augmentation R G X F) :=
  Langlands.Cohomology.CokernelComplex.Lax.augmentation_complexMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- Naturality retains the full original transport-natural sheaf morphism. -/
@[reassoc]
theorem complexMap_naturality {F F' : TopologicalSheaf G X (ModuleCat.{u} R)}
    (a : F ⟶ F') :
    (complexFunctor R G Y).map ((DirectImage.sheaf f hf (ModuleCat.{u} R)).map a) ≫
        complexMap f hf F' =
      complexMap f hf F ≫
        (Langlands.Cohomology.ProperCompactComplexes.directImageComplex
          (ComplexShape.up ℕ) f hf).map ((complexFunctor R G X).map a) :=
  (complexNatTrans f hf).naturality a

@[simp]
theorem complexMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    complexMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 (complex R G X F) := by
  have h : zeroNatTrans (R := R) (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) =
      𝟙 (zeroFunctor R G X) := by
    apply NatTrans.ext
    funext F
    exact zeroMap_id F
  unfold complexMap
  simpa only [h, complex, complexFunctor,
    Langlands.Cohomology.ProperCompactComplexes.directImageComplex] using
      Langlands.Cohomology.CokernelComplex.Lax.complexMap_id
        (zeroFunctor R G X) (coaugmentation R G X) F

/-- All higher comparison maps retain spatial composition, in the stalk order. -/
theorem complexMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    complexMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      complexMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (Langlands.Cohomology.ProperCompactComplexes.directImageComplex
          (ComplexShape.up ℕ) g hg).map (complexMap f hf F) := by
  have h : zeroNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) =
      Langlands.Cohomology.CokernelComplex.Lax.compose
        (zeroNatTrans f hf) (zeroNatTrans g hg) := by
    apply NatTrans.ext
    funext F
    exact zeroMap_comp f hf g hg F
  unfold complexMap
  simpa only [h, complex, complexFunctor,
    Langlands.Cohomology.ProperCompactComplexes.directImageComplex] using
      Langlands.Cohomology.CokernelComplex.Lax.complexMap_comp
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf)
    (zeroNatTrans g hg) (coaugmentation_zeroMap g hg) F

end Langlands.Sheaf.Equivariant.Godement.Spatial
