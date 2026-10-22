import Langlands.Sheaf.Equivariant.SmoothCompactSupport
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Complexes of equivariant sections

Actual equivariant sheaf differentials induce representation differentials.
The construction applies to supplied complexes; no assertion that a chosen
complex computes derived equivariant cohomology is built into the data.
-/

noncomputable section

namespace Langlands.Cohomology.EquivariantSections

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant

universe u uG uI uJ vJ

variable (R : Type u) [CommRing R]
variable (G : Type uG) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X]

instance : (sectionRepresentation R G X).Additive where
  map_add {F F'} {f g} := by
    ext s
    rfl

variable [ContinuousConstSMul G X]

instance : (CompactSections.functor R G X).Additive where
  map_add {F F'} {f g} := by
    ext s
    rfl

variable {I : Type uI} (c : ComplexShape I)

/-- Apply actual global section actions to each term and differential. -/
def globalComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (Rep.{u} R G) c :=
  (sectionRepresentation R G X).mapHomologicalComplex c

/-- Apply actual compact section actions to each term and differential. -/
def compactComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (Rep.{u} R G) c :=
  (CompactSections.functor R G X).mapHomologicalComplex c

/-- Forgetting support induces an actual natural chain map. -/
def forgetSupportComplex :
    compactComplex R G X c ⟶ globalComplex R G X c :=
  NatTrans.mapHomologicalComplex (CompactSections.inclusion R G X) c

/-- The actual homology representation of the global-section complex. -/
def globalHomology (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤ Rep.{u} R G :=
  globalComplex R G X c ⋙ homologyFunctor (Rep.{u} R G) c i

/-- The actual homology representation of the compact-section complex. -/
def compactHomology (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤ Rep.{u} R G :=
  compactComplex R G X c ⋙ homologyFunctor (Rep.{u} R G) c i

/-- The support-forgetting chain map induces a natural intertwiner on homology. -/
def forgetSupportHomology (i : I) :
    compactHomology R G X c i ⟶ globalHomology R G X c i :=
  Functor.whiskerRight (forgetSupportComplex R G X c) (homologyFunctor (Rep.{u} R G) c i)

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance : (SmoothCompactSections.functor R G X).Additive where
  map_add {F F'} {f g} := by
    ext s
    rfl

instance : (SmoothCompactSections.smoothFunctor R G X).Additive where
  map_add {F F'} {f g} := by
    ext s
    rfl

/-- The complex obtained by applying the constructed smooth compact-section functor. -/
def smoothCompactComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (Rep.{u} R G) c :=
  (SmoothCompactSections.functor R G X).mapHomologicalComplex c

/-- The same actual section complex, with every term bundled as a smooth representation. -/
def smoothCategoryComplex :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (Langlands.SmoothRep.{u, uG, u} R G) c :=
  (SmoothCompactSections.smoothFunctor R G X).mapHomologicalComplex c

/-- Forgetting the smoothness witnesses gives the original representation complex. -/
def smoothCategoryComplexToRepIso :
    smoothCategoryComplex R G X c ⋙
      (Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex c ≅
        smoothCompactComplex R G X c :=
  Functor.mapHomologicalComplexCompIso
    (SmoothCompactSections.smoothFunctorToRepIso R G X) c

/-- Each term of this complex carries the proved smooth representation. -/
theorem smooth_term
    (K : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    Langlands.IsSmooth (((smoothCompactComplex R G X c).obj K).X i).ρ :=
  SmoothCompactSections.isSmooth (K.X i).obj

/-- The termwise smooth inclusion is a natural chain map. -/
def forgetSmoothComplex :
    smoothCompactComplex R G X c ⟶ compactComplex R G X c :=
  NatTrans.mapHomologicalComplex (SmoothCompactSections.inclusion R G X) c

/-- Homology in the actual abelian category of algebraic representations. -/
def homologyOfSmoothComplex (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤ Rep.{u} R G :=
  smoothCompactComplex R G X c ⋙ homologyFunctor (Rep.{u} R G) c i

/-- Open fixing subgroups descend from smooth cycles to their homology classes. -/
theorem smooth_homology
    (K : HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) (i : I) :
    Langlands.IsSmooth ((homologyOfSmoothComplex R G X c i).obj K).ρ := by
  let L := (smoothCompactComplex R G X c).obj K
  have hcycles : Langlands.IsSmooth (L.cycles i).ρ := by
    intro z
    obtain ⟨H, hH⟩ := smooth_term R G X c K i ((L.iCycles i).hom z)
    refine ⟨H, ?_⟩
    intro h
    apply (Rep.mono_iff_injective (L.iCycles i)).1 inferInstance
    change (L.iCycles i).hom ((L.cycles i).ρ (h : G) z) =
      (L.iCycles i).hom z
    rw [(L.iCycles i).hom.isIntertwining]
    exact hH h
  intro z
  obtain ⟨w, rfl⟩ := (Rep.epi_iff_surjective (L.homologyπ i)).1 inferInstance z
  obtain ⟨H, hH⟩ := hcycles w
  refine ⟨H, ?_⟩
  intro h
  change (L.homology i).ρ (h : G) ((L.homologyπ i).hom w) =
    (L.homologyπ i).hom w
  rw [← (L.homologyπ i).hom.isIntertwining]
  exact congrArg (L.homologyπ i).hom (hH h)

/-- The constructed homology action, bundled using its proved smoothness. -/
def smoothCategoryHomology (i : I) :
    HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c ⥤
      Langlands.SmoothRep.{u, uG, u} R G :=
  (Langlands.smoothRepProperty R G).lift (homologyOfSmoothComplex R G X c i)
    (fun K => smooth_homology R G X c K i)

/-- The smooth homology functor has exactly the already constructed underlying action. -/
def smoothCategoryHomologyToRepIso (i : I) :
    smoothCategoryHomology R G X c i ⋙ Langlands.SmoothRep.toRep ≅
      homologyOfSmoothComplex R G X c i :=
  (Langlands.smoothRepProperty R G).liftCompιIso (homologyOfSmoothComplex R G X c i)
    (fun K => smooth_homology R G X c K i)

/-- The smooth inclusion induces a natural intertwiner on homology. -/
def forgetSmoothHomology (i : I) :
    homologyOfSmoothComplex R G X c i ⟶ compactHomology R G X c i :=
  Functor.whiskerRight (forgetSmoothComplex R G X c) (homologyFunctor (Rep.{u} R G) c i)

/-- Actual diagrams of sheaf complexes induce diagrams of section complexes. -/
def diagramFunctor (J : Type uJ) [Category.{vJ} J] :
    (J ⥤ HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) ⥤
      (J ⥤ HomologicalComplex (Rep.{u} R G) c) :=
  (Functor.whiskeringRight J _ _).obj (smoothCompactComplex R G X c)

/-- In particular, an inverse coefficient system is a genuine opposite-natural diagram. -/
def inverseSystemFunctor :
    (ℕᵒᵖ ⥤ HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex (Rep.{u} R G) c) :=
  diagramFunctor R G X c ℕᵒᵖ

/-- Inverse systems retain the constructed complexes in the smooth category itself. -/
def smoothCategoryInverseSystemFunctor :
    (ℕᵒᵖ ⥤ HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c) ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex (Langlands.SmoothRep.{u, uG, u} R G) c) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (smoothCategoryComplex R G X c)

end Langlands.Cohomology.EquivariantSections
