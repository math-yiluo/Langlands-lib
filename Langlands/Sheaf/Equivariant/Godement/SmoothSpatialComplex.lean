import Langlands.Sheaf.Equivariant.Godement.SmoothSpatialZero
import Langlands.Cohomology.CokernelComplex.LaxNaturality

/-! # Actual spatial maps of the separate smooth Godement complex -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Sheaf.Equivariant.Godement.SmoothSpatial

open CategoryTheory

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Construct all higher spatial maps by actual cokernel descent from the
separate smooth Godement degree-zero map. -/
def complexMap (F : SmoothTopologicalSheaf R G X) :
    smoothComplex R G Y ((SmoothDirectImage.functor f hf).obj F) ⟶
      ((SmoothDirectImage.functor f hf).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (smoothComplex R G X F) :=
  Langlands.Cohomology.CokernelComplex.Lax.complexMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- The constructed chain map is natural in the original smooth sheaf. -/
def complexNatTrans :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothComplexFunctor R G Y ⟶
      smoothComplexFunctor R G X ⋙
        (SmoothDirectImage.functor f hf).mapHomologicalComplex (ComplexShape.up ℕ) :=
  Langlands.Cohomology.CokernelComplex.Lax.functorMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf)

@[simp]
theorem complexNatTrans_app (F : SmoothTopologicalSheaf R G X) :
    (complexNatTrans f hf).app F = complexMap f hf F := rfl

/-- Every degree is the constructed iterated-cokernel term comparison. -/
theorem complexMap_f (F : SmoothTopologicalSheaf R G X) (n : ℕ) :
    (complexMap f hf F).f n =
      (Langlands.Cohomology.CokernelComplex.Lax.termMap
        (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) n).app F := rfl

/-- Degree zero is exactly the actual separate smooth Godement spatial map. -/
@[simp]
theorem complexMap_f_zero (F : SmoothTopologicalSheaf R G X) :
    (complexMap f hf F).f 0 = zeroMap f hf F :=
  Langlands.Cohomology.CokernelComplex.Lax.termMap_zero
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- The chain map retains the original separate smooth Godement coaugmentation. -/
@[reassoc]
theorem augmentation_complexMap (F : SmoothTopologicalSheaf R G X) :
    smoothAugmentation R G Y ((SmoothDirectImage.functor f hf).obj F) ≫
        (complexMap f hf F).f 0 =
      (SmoothDirectImage.functor f hf).map (smoothAugmentation R G X F) :=
  Langlands.Cohomology.CokernelComplex.Lax.augmentation_complexMap
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf) F

/-- Naturality retains every original morphism of smooth equivariant sheaves. -/
@[reassoc]
theorem complexMap_naturality {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothComplexFunctor R G Y).map ((SmoothDirectImage.functor f hf).map a) ≫
        complexMap f hf F' =
      complexMap f hf F ≫
        ((SmoothDirectImage.functor f hf).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((smoothComplexFunctor R G X).map a) :=
  (complexNatTrans f hf).naturality a

/-- The full chain map respects the actual smooth-direct-image identity
comparison in every degree. -/
@[reassoc]
theorem complexMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothComplexFunctor R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        complexMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      (NatTrans.mapHomologicalComplex
        (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom
        (ComplexShape.up ℕ)).app (smoothComplex R G X F) := by
  have hα : ∀ K : SmoothTopologicalSheaf R G X,
      (smoothZeroFunctor R G X).map
          ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app K) ≫
          (zeroNatTrans (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)).app K =
        𝟙 ((smoothZeroFunctor R G X).obj K) ≫
          (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app
            ((smoothZeroFunctor R G X).obj K) := by
    intro K
    rw [Category.id_comp]
    exact zeroMap_id K
  have h := Langlands.Cohomology.CokernelComplex.Lax.complexMap_transformation
    (Φ := 𝟭 (SmoothTopologicalSheaf R G X))
    (Ψ := SmoothDirectImage.functor (R := R)
      (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl))
    (η := smoothCoaugmentation R G X) (η' := smoothCoaugmentation R G X)
    (𝟙 (smoothZeroFunctor R G X))
    (zeroNatTrans (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl))
    (SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom hα
    (fun K => Category.comp_id ((smoothCoaugmentation R G X).app K))
    (coaugmentation_zeroMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)) F
  erw [Langlands.Cohomology.CokernelComplex.Lax.complexMap_id
    (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) F, Category.id_comp] at h
  exact h

/-- All higher maps retain the lax comparison for composition of actual
smooth direct images. No invertibility of that comparison is needed. -/
@[reassoc]
theorem complexMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothComplexFunctor R G Z).map ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        complexMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      complexMap g hg ((SmoothDirectImage.functor f hf).obj F) ≫
        ((SmoothDirectImage.functor g hg).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (complexMap f hf F) ≫
        (NatTrans.mapHomologicalComplex (SmoothDirectImage.compMap f hf g hg)
          (ComplexShape.up ℕ)).app (smoothComplex R G X F) := by
  let hgf : ∀ (k : G) (x : X), (g.comp f) (k • x) = k • (g.comp f) x :=
    fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]
  have hα : ∀ K : SmoothTopologicalSheaf R G X,
      (smoothZeroFunctor R G Z).map ((SmoothDirectImage.compMap f hf g hg).app K) ≫
          (zeroNatTrans (g.comp f) hgf).app K =
        (Langlands.Cohomology.CokernelComplex.Lax.compose
          (zeroNatTrans f hf) (zeroNatTrans g hg)).app K ≫
          (SmoothDirectImage.compMap f hf g hg).app ((smoothZeroFunctor R G X).obj K) := by
    intro K
    exact zeroMap_comp f hf g hg K
  have h := Langlands.Cohomology.CokernelComplex.Lax.complexMap_transformation
    (Φ := SmoothDirectImage.functor (R := R) f hf ⋙ SmoothDirectImage.functor g hg)
    (Ψ := SmoothDirectImage.functor (R := R) (g.comp f) hgf)
    (η := smoothCoaugmentation R G X) (η' := smoothCoaugmentation R G Z)
    (Langlands.Cohomology.CokernelComplex.Lax.compose
      (zeroNatTrans f hf) (zeroNatTrans g hg))
    (zeroNatTrans (g.comp f) hgf) (SmoothDirectImage.compMap f hf g hg) hα
    (Langlands.Cohomology.CokernelComplex.Lax.compose_comm
      (zeroNatTrans f hf) (coaugmentation_zeroMap f hf)
      (zeroNatTrans g hg) (coaugmentation_zeroMap g hg))
    (coaugmentation_zeroMap (g.comp f) hgf) F
  erw [Langlands.Cohomology.CokernelComplex.Lax.complexMap_comp
    (zeroNatTrans f hf) (coaugmentation_zeroMap f hf)
    (zeroNatTrans g hg) (coaugmentation_zeroMap g hg) F] at h
  simpa only [complexMap, smoothComplex, smoothComplexFunctor, Category.assoc] using h

end Langlands.Sheaf.Equivariant.Godement.SmoothSpatial
