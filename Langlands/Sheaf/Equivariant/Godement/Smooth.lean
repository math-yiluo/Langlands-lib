import Langlands.Sheaf.Equivariant.Coinduction
import Langlands.Sheaf.Equivariant.SmoothAbelian
import Langlands.Sheaf.Equivariant.Godement.Underlying
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# The smooth equivariant Godement complex

Forgetting smoothness and equivariance has a right adjoint, the smooth part of
coinduction. Composing the ordinary Godement degree-zero functor over all
points of the space with this adjoint pair gives the degree-zero smooth
Godement functor. Its coaugmentation comes from the adjunction and is monic.
Iterating actual cokernels in the abelian category of smooth sheaves gives the
smooth Godement complex.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Godement

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- Forgetting smoothness and equivariance. -/
def smoothForget :
    SmoothTopologicalSheaf R G X ⥤ TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) :=
  smoothInclusion R G X ⋙ toSheaf G X (ModuleCat.{u} R)

/-- Smooth coinduction: coinduction followed by the smooth part. -/
def smoothCoinduction :
    TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X) ⥤ SmoothTopologicalSheaf R G X :=
  coinduction G X (ModuleCat.{u} R) ⋙ smoothCoreflector R

/-- Smooth coinduction is right adjoint to forgetting smoothness and equivariance. -/
def smoothCoinductionAdjunction : smoothForget R G X ⊣ smoothCoinduction R G X :=
  (smoothAdjunction R).comp (coinductionAdjunction G X (ModuleCat.{u} R))

instance smoothForget_faithful : (smoothForget R G X).Faithful :=
  inferInstanceAs (smoothInclusion R G X ⋙ toSheaf G X (ModuleCat.{u} R)).Faithful

instance smoothForget_additive : (smoothForget R G X).Additive :=
  have : (smoothInclusion R G X).Additive :=
    inferInstanceAs (smoothSheafProperty R G X).ι.Additive
  inferInstanceAs (smoothInclusion R G X ⋙ toSheaf G X (ModuleCat.{u} R)).Additive

instance smoothCoinduction_additive : (smoothCoinduction R G X).Additive :=
  (smoothCoinductionAdjunction R G X).right_adjoint_additive

/-- The degree-zero smooth Godement functor: forget, take the ordinary Godement
degree-zero sheaf over all points of the space, then coinduce smoothly. -/
def smoothZeroFunctor : SmoothTopologicalSheaf R G X ⥤ SmoothTopologicalSheaf R G X :=
  smoothForget R G X ⋙
    Sheaf.Godement.zeroFunctor (Cohomology.Flasque.spacePoints (TopCat.of X))
      (ModuleCat.{u} R) ⋙
    smoothCoinduction R G X

/-- The smooth Godement coaugmentation: the adjunction unit followed by the
smooth coinduction of the ordinary Godement coaugmentation. -/
def smoothCoaugmentation : 𝟭 (SmoothTopologicalSheaf R G X) ⟶ smoothZeroFunctor R G X :=
  (smoothCoinductionAdjunction R G X).unit ≫
    Functor.whiskerLeft (smoothForget R G X)
      (Functor.whiskerRight
        (Sheaf.Godement.coaugmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
          (ModuleCat.{u} R))
        (smoothCoinduction R G X))

/-- Each component of the smooth coaugmentation is the adjoint of the ordinary
Godement coaugmentation of the underlying sheaf. -/
theorem smoothCoaugmentation_app (F : SmoothTopologicalSheaf R G X) :
    (smoothCoaugmentation R G X).app F =
      (smoothCoinductionAdjunction R G X).homEquiv _ _
        ((Sheaf.Godement.coaugmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
          (ModuleCat.{u} R)).app ((smoothForget R G X).obj F)) :=
  ((smoothCoinductionAdjunction R G X).homEquiv_unit _ _ _).symm

/-- After forgetting, the smooth coaugmentation followed by the counit is the
ordinary Godement coaugmentation. -/
@[reassoc]
theorem smoothForget_map_smoothCoaugmentation (F : SmoothTopologicalSheaf R G X) :
    (smoothForget R G X).map ((smoothCoaugmentation R G X).app F) ≫
        (smoothCoinductionAdjunction R G X).counit.app _ =
      (Sheaf.Godement.coaugmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
        (ModuleCat.{u} R)).app ((smoothForget R G X).obj F) := by
  rw [smoothCoaugmentation_app]
  exact ((smoothCoinductionAdjunction R G X).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

omit [TopologicalSpace G] [IsTopologicalGroup G] [HasStableNeighbourhoods G X] in
variable {R G X} in
/-- The ordinary Godement coaugmentation over all points is monic on every
sheaf that underlies an equivariant module sheaf. -/
theorem mono_coaugmentation_toSheaf (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Mono ((Sheaf.Godement.coaugmentation (Cohomology.Flasque.spacePoints (TopCat.of X))
      (ModuleCat.{u} R)).app ((toSheaf G X (ModuleCat.{u} R)).obj F)) := by
  have h1 : Mono ((toSheaf G X (ModuleCat.{u} R)).map ((coaugmentation R G X).app F)) :=
    (toSheaf G X (ModuleCat.{u} R)).map_mono _
  have h2 : Mono ((zeroIso R G X).hom.app F) :=
    inferInstanceAs (Mono ((zeroIso R G X).app F).hom)
  rw [← zeroIso_comm F]
  exact @mono_comp _ _ _ _ _ _ h1 _ h2

instance mono_smoothCoaugmentation_app (F : SmoothTopologicalSheaf R G X) :
    Mono ((smoothCoaugmentation R G X).app F) := by
  have hm : Mono ((smoothForget R G X).map ((smoothCoaugmentation R G X).app F) ≫
      (smoothCoinductionAdjunction R G X).counit.app _) := by
    rw [smoothForget_map_smoothCoaugmentation]
    exact mono_coaugmentation_toSheaf ((smoothInclusion R G X).obj F)
  exact (smoothForget R G X).mono_of_mono_map (@mono_of_mono _ _ _ _ _ _ _ hm)

/-- The smooth Godement cokernel complex, functorial in the smooth sheaf. -/
def smoothComplexFunctor :
    SmoothTopologicalSheaf R G X ⥤ CochainComplex (SmoothTopologicalSheaf R G X) ℕ :=
  Cohomology.CokernelComplex.functor (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)

/-- The smooth Godement complex of one smooth sheaf. -/
abbrev smoothComplex (F : SmoothTopologicalSheaf R G X) :
    CochainComplex (SmoothTopologicalSheaf R G X) ℕ :=
  (smoothComplexFunctor R G X).obj F

/-- Degree zero is the degree-zero smooth Godement sheaf. -/
theorem smoothComplex_X_zero (F : SmoothTopologicalSheaf R G X) :
    (smoothComplex R G X F).X 0 = (smoothZeroFunctor R G X).obj F :=
  rfl

/-- The coaugmentation from the smooth sheaf into degree zero. -/
def smoothAugmentation (F : SmoothTopologicalSheaf R G X) :
    F ⟶ (smoothComplex R G X F).X 0 :=
  Cohomology.CokernelComplex.augmentation
    (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) F

theorem smoothAugmentation_eq (F : SmoothTopologicalSheaf R G X) :
    smoothAugmentation R G X F = (smoothCoaugmentation R G X).app F :=
  rfl

@[reassoc (attr := simp)]
theorem smoothAugmentation_d (F : SmoothTopologicalSheaf R G X) :
    smoothAugmentation R G X F ≫ (smoothComplex R G X F).d 0 1 = 0 :=
  Cohomology.CokernelComplex.augmentation_d _ _ F

instance (F : SmoothTopologicalSheaf R G X) : Mono (smoothAugmentation R G X F) :=
  mono_smoothCoaugmentation_app R G X F

end Langlands.Sheaf.Equivariant.Godement
