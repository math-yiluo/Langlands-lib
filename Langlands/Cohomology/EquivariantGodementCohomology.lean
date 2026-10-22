import Langlands.Sheaf.Equivariant.Godement.Complex
import Langlands.Cohomology.EquivariantDerivedSections

/-!
# Equivariant cohomology through the Godement complex

Global and compactly supported sections of the equivariant Godement complex
form complexes of representations of the acting group; their homology is the
Godement-route equivariant cohomology. In degree zero it recovers the section
representations, because the augmentation of any cokernel complex with monic
coaugmentation is a kernel of the first differential.
-/

noncomputable section

namespace Langlands.Cohomology.EquivariantGodementCohomology

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u uA vA uB vB

section General

variable {A : Type uA} [Category.{vA} A] [Abelian A] (T : A ⥤ A) (η : 𝟭 A ⟶ T)
variable [∀ M : A, Mono (η.app M)]

/-- With monic coaugmentation, the augmentation of the cokernel complex is a
kernel of its first differential. -/
def augmentationIsKernel (M : A) :
    IsLimit (KernelFork.ofι (CokernelComplex.augmentation T η M)
      (CokernelComplex.augmentation_d T η M)) := by
  let c := CokernelCofork.ofπ (cokernel.π (CokernelComplex.inclusion T η 0))
    (cokernel.condition (CokernelComplex.inclusion T η 0))
  have hc : IsColimit (c.map ((evaluation A A).obj M)) :=
    CokernelCofork.mapIsColimit c (cokernelIsCokernel _) ((evaluation A A).obj M)
  haveI : Mono (((evaluation A A).obj M).map (CokernelComplex.inclusion T η 0)) :=
    inferInstanceAs (Mono (η.app M))
  have hg : Mono ((CokernelComplex.inclusion T η 1).app M) :=
    inferInstanceAs (Mono (η.app ((CokernelComplex.residual T η 1).obj M)))
  exact isKernelCompMono (hg := hg) (Abelian.monoIsKernelOfCokernel _ hc)
    ((CokernelComplex.inclusion T η 1).app M)
    (by rw [CokernelComplex.complex_d]; rfl)

variable {B : Type uB} [Category.{vB} B] [Abelian B] (Φ : A ⥤ B)
variable [Φ.Additive] [PreservesFiniteLimits Φ]

/-- The cokernel complex followed by termwise application of a functor. -/
abbrev mappedComplex : A ⥤ CochainComplex B ℕ :=
  CokernelComplex.functor T η ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ)

/-- The image of the augmentation is the inclusion of degree-zero cycles. -/
def cyclesIso (M : A) : Φ.obj M ≅ ((mappedComplex T η Φ).obj M).cycles 0 :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (augmentationIsKernel T η M) Φ)
    (((mappedComplex T η Φ).obj M).cyclesIsKernel 0 1 (by simp))

@[reassoc (attr := simp)]
theorem cyclesIso_hom_iCycles (M : A) :
    (cyclesIso T η Φ M).hom ≫ ((mappedComplex T η Φ).obj M).iCycles 0 =
      Φ.map (CokernelComplex.augmentation T η M) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (KernelFork.mapIsLimit _ (augmentationIsKernel T η M) Φ)
    (((mappedComplex T η Φ).obj M).cyclesIsKernel 0 1 (by simp)) WalkingParallelPair.zero

@[reassoc]
theorem cyclesIso_naturality {M N : A} (f : M ⟶ N) :
    Φ.map f ≫ (cyclesIso T η Φ N).hom =
      (cyclesIso T η Φ M).hom ≫
        HomologicalComplex.cyclesMap ((mappedComplex T η Φ).map f) 0 := by
  rw [← cancel_mono (((mappedComplex T η Φ).obj N).iCycles 0), Category.assoc,
    Category.assoc, HomologicalComplex.cyclesMap_i, cyclesIso_hom_iCycles,
    ← Category.assoc (cyclesIso T η Φ M).hom, cyclesIso_hom_iCycles]
  change _ = Φ.map _ ≫ Φ.map (((CokernelComplex.functor T η).map f).f 0)
  rw [← Φ.map_comp, ← Φ.map_comp]
  congr 1
  exact η.naturality f

/-- The degree-zero cohomology of the mapped complex, objectwise. -/
def homologyIso (M : A) : Φ.obj M ≅ ((mappedComplex T η Φ).obj M).homology 0 :=
  cyclesIso T η Φ M ≪≫ ((mappedComplex T η Φ).obj M).isoHomologyπ₀

/-- A left exact functor applied to a cokernel complex with monic coaugmentation
has the functor itself as degree-zero cohomology. -/
def homologyZeroIso :
    mappedComplex T η Φ ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) 0 ≅ Φ :=
  (NatIso.ofComponents (homologyIso T η Φ) (fun {M N} f => by
    change Φ.map f ≫ (cyclesIso T η Φ N).hom ≫ ((mappedComplex T η Φ).obj N).homologyπ 0 =
      ((cyclesIso T η Φ M).hom ≫ ((mappedComplex T η Φ).obj M).homologyπ 0) ≫
        HomologicalComplex.homologyMap ((mappedComplex T η Φ).map f) 0
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    exact cyclesIso_naturality_assoc T η Φ f _)).symm

end General

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Global sections of the equivariant Godement complex, as a cochain complex of
representations. -/
def globalComplex :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ CochainComplex (Rep.{u} R G) ℕ :=
  Godement.complexFunctor R G X ⋙ EquivariantSections.globalComplex R G X (ComplexShape.up ℕ)

/-- Compactly supported sections of the equivariant Godement complex, as a
cochain complex of representations. -/
def compactComplex :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ CochainComplex (Rep.{u} R G) ℕ :=
  Godement.complexFunctor R G X ⋙ EquivariantSections.compactComplex R G X (ComplexShape.up ℕ)

/-- Degree `q` Godement cohomology, with its action of the group. -/
def globalCohomology (q : ℕ) : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  Godement.complexFunctor R G X ⋙
    EquivariantSections.globalHomology R G X (ComplexShape.up ℕ) q

/-- Degree `q` compactly supported Godement cohomology, with its action of the
group. -/
def compactCohomology (q : ℕ) : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  Godement.complexFunctor R G X ⋙
    EquivariantSections.compactHomology R G X (ComplexShape.up ℕ) q

/-- Forgetting support induces natural intertwiners in every degree. -/
def forgetSupport (q : ℕ) : compactCohomology R G X q ⟶ globalCohomology R G X q :=
  Functor.whiskerLeft (Godement.complexFunctor R G X)
    (EquivariantSections.forgetSupportHomology R G X (ComplexShape.up ℕ) q)

/-- In degree zero, Godement cohomology is the global section representation. -/
def globalCohomologyZeroIso : globalCohomology R G X 0 ≅ sectionRepresentation R G X :=
  homologyZeroIso (Godement.zeroFunctor R G X) (Godement.coaugmentation R G X)
    (sectionRepresentation R G X)

/-- In degree zero, compactly supported Godement cohomology is the compact
section representation. -/
def compactCohomologyZeroIso : compactCohomology R G X 0 ≅ CompactSections.functor R G X :=
  homologyZeroIso (Godement.zeroFunctor R G X) (Godement.coaugmentation R G X)
    (CompactSections.functor R G X)

/-- Diagrams of equivariant sheaves give diagrams of compactly supported
Godement cohomology representations. -/
def compactCohomologyDiagram (J : Type*) [Category J] (q : ℕ) :
    (J ⥤ TopologicalSheaf G X (ModuleCat.{u} R)) ⥤ (J ⥤ Rep.{u} R G) :=
  (Functor.whiskeringRight J _ _).obj (compactCohomology R G X q)

section Smooth

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smooth compact sections of the equivariant Godement complex, as a complex in
the category of smooth representations. -/
def smoothCompactComplex :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤
      CochainComplex (Langlands.SmoothRep.{u, u, u} R G) ℕ :=
  Godement.complexFunctor R G X ⋙
    EquivariantSections.smoothCategoryComplex R G X (ComplexShape.up ℕ)

/-- Degree `q` cohomology of the smooth compact sections of the equivariant
Godement complex, bundled with its proved smoothness. -/
def smoothCompactCohomology (q : ℕ) :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Langlands.SmoothRep.{u, u, u} R G :=
  Godement.complexFunctor R G X ⋙
    EquivariantSections.smoothCategoryHomology R G X (ComplexShape.up ℕ) q

/-- The smooth-part inclusion induces natural intertwiners into compactly
supported Godement cohomology. -/
def forgetSmooth (q : ℕ) :
    smoothCompactCohomology R G X q ⋙ Langlands.SmoothRep.toRep ⟶ compactCohomology R G X q :=
  Functor.whiskerLeft (Godement.complexFunctor R G X)
    ((EquivariantSections.smoothCategoryHomologyToRepIso R G X (ComplexShape.up ℕ) q).hom ≫
      EquivariantSections.forgetSmoothHomology R G X (ComplexShape.up ℕ) q)

end Smooth

end Langlands.Cohomology.EquivariantGodementCohomology
