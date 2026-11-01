import Langlands.Geometry.EtaleInverseImageExact
import Langlands.Cohomology.ExactDerivedHomology
import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Exact geometric inverse image on actual derived categories -/

noncomputable section

universe u wX wZ

namespace Langlands.Geometry.EtaleDerivedInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]

/-- Apply the actual exact inverse image to complexes and localize at
quasi-isomorphisms. No preservation of injectives is needed. -/
def functor : DerivedCategory (ModuleSheaf X R) ⥤ DerivedCategory (ModuleSheaf Z R) :=
  (inverseImage f R).mapDerivedCategory

instance functor_commShift : (functor f R).CommShift ℤ :=
  inferInstanceAs ((inverseImage f R).mapDerivedCategory.CommShift ℤ)

instance functor_isTriangulated : (functor f R).IsTriangulated :=
  inferInstanceAs ((inverseImage f R).mapDerivedCategory.IsTriangulated)

instance functor_linear : (functor f R).Linear R :=
  inferInstanceAs ((inverseImage f R).mapDerivedCategory.Linear R)

/-- The actual localization factor identifies the derived image of every
complex with its termwise geometric inverse image. -/
def factors :
    DerivedCategory.Q ⋙ functor f R ≅
      (inverseImage f R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (inverseImage f R).mapDerivedCategoryFactors

/-- Derived inverse image commutes with actual degree-n singleton complexes. -/
def singleIso (n : ℤ) :
    DerivedCategory.singleFunctor (ModuleSheaf X R) n ⋙ functor f R ≅
      inverseImage f R ⋙ DerivedCategory.singleFunctor (ModuleSheaf Z R) n :=
  (inverseImage f R).mapDerivedCategorySingleFunctor n

/-- Exact inverse image commutes naturally with every derived homology functor. -/
def homologyIso (q : ℤ) :
    functor f R ⋙ DerivedCategory.homologyFunctor (ModuleSheaf Z R) q ≅
      DerivedCategory.homologyFunctor (ModuleSheaf X R) q ⋙ inverseImage f R :=
  Langlands.Cohomology.exactDerivedHomologyIso (inverseImage f R) q

@[reassoc] theorem homologyIso_naturality (q : ℤ)
    {K L : DerivedCategory (ModuleSheaf X R)} (a : K ⟶ L) :
    (DerivedCategory.homologyFunctor (ModuleSheaf Z R) q).map ((functor f R).map a) ≫
        (homologyIso f R q).hom.app L =
      (homologyIso f R q).hom.app K ≫
        (inverseImage f R).map
          ((DerivedCategory.homologyFunctor (ModuleSheaf X R) q).map a) :=
  (homologyIso f R q).hom.naturality a

/-- The exact derived image preserves each lower cohomological bound. -/
theorem preservesLowerBound (K : DerivedCategory (ModuleSheaf X R))
    (n : ℤ) (hK : K.IsGE n) : ((functor f R).obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro q hq
  exact ((inverseImage f R).map_isZero (hK q hq)).of_iso ((homologyIso f R q).app K)

/-- It also preserves each upper cohomological bound. -/
theorem preservesUpperBound (K : DerivedCategory (ModuleSheaf X R))
    (n : ℤ) (hK : K.IsLE n) : ((functor f R).obj K).IsLE n := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro q hq
  exact ((inverseImage f R).map_isZero (hK q hq)).of_iso ((homologyIso f R q).app K)

/-- The same actual derived functor restricted to bounded-below objects.
The original lower bound is preserved, not supplied as comparison data. -/
def plusFunctor :
    DerivedCategory.Plus (ModuleSheaf X R) ⥤ DerivedCategory.Plus (ModuleSheaf Z R) :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ functor f R) (fun K => by
      obtain ⟨n, hn⟩ := K.property
      exact ⟨n, preservesLowerBound f R K.obj n hn⟩)

/-- Forgetting the proved bounded-below condition recovers the actual
unbounded derived inverse image. -/
def plusInclusionIso :
    plusFunctor f R ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ functor f R :=
  Iso.refl _

instance plusFunctor_commShift : (plusFunctor f R).CommShift ℤ := by
  dsimp only [plusFunctor]
  infer_instance

instance plusFunctor_isTriangulated : (plusFunctor f R).IsTriangulated := by
  dsimp only [plusFunctor]
  infer_instance

instance plusFunctor_linear : (plusFunctor f R).Linear R where
  map_smul a r := by
    apply (DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map_injective
    change (functor f R).map (r • a.hom) = r • (functor f R).map a.hom
    exact (functor f R).map_smul r a.hom

/-- On bounded-below derived objects, the same actual inverse image
commutes with homology naturally in every localized morphism. -/
def plusHomologyIso (q : ℤ) :
    plusFunctor f R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleSheaf Z R) q ≅
      DerivedCategory.Plus.homologyFunctor (ModuleSheaf X R) q ⋙ inverseImage f R :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι (homologyIso f R q)

/-- Termwise inverse image on bounded-below complexes computes the same
bounded-below derived functor. -/
def plusFactors :
    DerivedCategory.Plus.Q ⋙ plusFunctor f R ≅
      (inverseImage f R).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents
    (fun K => DerivedCategory.Plus.ι.preimageIso ((factors f R).app K.obj))
    (fun {_K _L} a => by
      apply (DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (factors f R).hom.naturality a.hom)

/-- The bounded-below inverse image also has the actual singleton comparison. -/
def plusSingleIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) n ⋙ plusFunctor f R ≅
      inverseImage f R ⋙ DerivedCategory.Plus.singleFunctor (ModuleSheaf Z R) n :=
  NatIso.ofComponents
    (fun F => DerivedCategory.Plus.ι.preimageIso ((singleIso f R n).app F))
    (fun {_F _G} a => by
      apply (DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (singleIso f R n).hom.naturality a)

end Langlands.Geometry.EtaleDerivedInverseImage
