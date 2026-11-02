import Langlands.Sheaf.Equivariant.Godement.SpatialComplex
import Langlands.Cohomology.EquivariantGodementCohomology
import Langlands.Cohomology.LocalCompactComparison

/-! # Actual spatial maps on equivariant Godement section cohomology -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.EquivariantGodementCohomology.Spatial

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The actual spatial chain comparison followed by global sections. -/
def globalComplexMap :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ globalComplex R G Y ⟶
      globalComplex R G X :=
  Functor.whiskerRight (Godement.Spatial.complexNatTrans f hf)
      (EquivariantSections.globalComplex R G Y (ComplexShape.up ℕ)) ≫
    Functor.whiskerLeft (Godement.complexFunctor R G X)
      (ProperCompactComplexes.globalComplexIso (ComplexShape.up ℕ) f hf).hom

/-- Proper pullback of compact sections of the constructed Godement comparison. -/
def compactComplexMap (hp : IsProperMap f) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ compactComplex R G Y ⟶
      compactComplex R G X :=
  Functor.whiskerRight (Godement.Spatial.complexNatTrans f hf)
      (EquivariantSections.compactComplex R G Y (ComplexShape.up ℕ)) ≫
    Functor.whiskerLeft (Godement.complexFunctor R G X)
      (LocalCompactComparison.properComplex (ComplexShape.up ℕ) f hf hp)

/-- No higher comparison map is supplied: the input is the actual Godement map. -/
@[simp]
theorem compactComplexMap_app (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactComplexMap f hf hp).app F =
      LocalCompactComparison.pullbackComplex f hf hp (Godement.Spatial.complexMap f hf F) :=
  rfl

/-- In every degree the original global section is sent by the constructed sheaf map. -/
@[simp]
theorem compactComplexMap_apply (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) (n : ℕ)
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary
        ((Godement.complex R G Y
          ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).X n).obj)) :
    (((((compactComplexMap f hf hp).app F).f n).hom s)).val =
      (((Godement.Spatial.complexMap f hf F).f n).hom.app
        (Opposite.op ActionOpens.top)).hom s.val :=
  rfl

/-- Degree zero is the spatial neighborhood-colimit stalk-family map. -/
theorem compactComplexMap_apply_zero (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (s : Langlands.Sheaf.CompactSupport.submodule
      (CompactSections.ordinary
        ((Godement.complex R G Y
          ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).X 0).obj)) :
    (((((compactComplexMap f hf hp).app F).f 0).hom s)).val =
      ((Godement.Spatial.zeroMap f hf F).hom.app
        (Opposite.op ActionOpens.top)).hom s.val := by
  rw [compactComplexMap_apply, Godement.Spatial.complexMap_f_zero]
  rfl

/-- The local-vanishing and stalk-support conventions give the same Godement map. -/
theorem compactComplexMap_comparison (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (LocalCompactComparison.compactComplexIso R G Y (ComplexShape.up ℕ)).hom.app
        (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (compactComplexMap f hf hp).app F =
      ProperCompactComplexes.pullbackComplex f hf hp (Godement.Spatial.complexMap f hf F) ≫
        (LocalCompactComparison.compactComplexIso R G X (ComplexShape.up ℕ)).hom.app
          (Godement.complex R G X F) :=
  LocalCompactComparison.pullbackComplex_comparison f hf hp _

/-- Forgetting support recovers global sections of the actual spatial chain map. -/
theorem compactComplexMap_inclusion_triangle (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactComplexMap f hf hp).app F ≫
        (EquivariantSections.forgetSupportComplex R G X (ComplexShape.up ℕ)).app
          (Godement.complex R G X F) =
      (EquivariantSections.forgetSupportComplex R G Y (ComplexShape.up ℕ)).app
          (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (globalComplexMap f hf).app F :=
  LocalCompactComparison.pullbackComplex_inclusion_triangle f hf hp _

@[simp]
theorem compactComplexMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactComplexMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((compactComplex R G X).obj F) := by
  rw [compactComplexMap_app, Godement.Spatial.complexMap_id]
  exact LocalCompactComparison.pullbackComplex_id _

/-- Proper spatial Godement maps compose contravariantly. -/
theorem compactComplexMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactComplexMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (compactComplexMap g hg hq).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (compactComplexMap f hf hp).app F := by
  rw [compactComplexMap_app, Godement.Spatial.complexMap_comp]
  exact LocalCompactComparison.pullbackComplex_comp f hf g hg hp hq _ _

/-- Homology of the actual global Godement section map. -/
def globalCohomologyMap (q : ℕ) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ globalCohomology R G Y q ⟶
      globalCohomology R G X q :=
  Functor.whiskerRight (globalComplexMap f hf)
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q)

/-- Homology of the actual proper compact Godement section map. -/
def compactCohomologyMap (hp : IsProperMap f) (q : ℕ) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ compactCohomology R G Y q ⟶
      compactCohomology R G X q :=
  Functor.whiskerRight (compactComplexMap f hf hp)
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q)

@[simp]
theorem compactCohomologyMap_app (hp : IsProperMap f) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactCohomologyMap f hf hp q).app F =
      LocalCompactComparison.pullbackHomology f hf hp
        (Godement.Spatial.complexMap f hf F) q := rfl

/-- The proved support comparison also identifies the actual cohomology maps. -/
theorem compactCohomologyMap_comparison (hp : IsProperMap f) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (LocalCompactComparison.compactHomologyIso R G Y (ComplexShape.up ℕ) q).hom.app
        (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (compactCohomologyMap f hf hp q).app F =
      ProperCompactComplexes.pullbackHomology f hf hp (Godement.Spatial.complexMap f hf F) q ≫
        (LocalCompactComparison.compactHomologyIso R G X (ComplexShape.up ℕ) q).hom.app
          (Godement.complex R G X F) :=
  LocalCompactComparison.pullbackHomology_comparison f hf hp _ q

/-- The support-forgetting map is compatible with actual proper spatial cohomology. -/
theorem compactCohomologyMap_inclusion_triangle (hp : IsProperMap f) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactCohomologyMap f hf hp q).app F ≫ (forgetSupport R G X q).app F =
      (forgetSupport R G Y q).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (globalCohomologyMap f hf q).app F := by
  simpa only [compactCohomologyMap, globalCohomologyMap, forgetSupport,
    EquivariantSections.forgetSupportHomology, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using
      congrArg (fun k => (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map k)
        (compactComplexMap_inclusion_triangle f hf hp F)

@[simp]
theorem compactCohomologyMap_id (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactCohomologyMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id q).app F =
      𝟙 ((compactCohomology R G X q).obj F) := by
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [compactComplexMap_id]
  exact (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map_id _

theorem compactCohomologyMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (compactCohomologyMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) q).app F =
      (compactCohomologyMap g hg hq q).app
          ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (compactCohomologyMap f hf hp q).app F := by
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [compactComplexMap_comp f hf g hg hp hq F]
  exact (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map_comp _ _

end Langlands.Cohomology.EquivariantGodementCohomology.Spatial
