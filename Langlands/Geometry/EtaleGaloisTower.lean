import Langlands.Geometry.EtaleGaloisAction
import Langlands.Geometry.EtaleDeckTowerColimit
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Finite Galois towers of base changes and smooth Galois actions on étale cohomology -/

noncomputable section

namespace Langlands.Geometry.EtaleGaloisTower

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleGaloisAction

universe u wS wR

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The base change of `X` to a finite Galois subextension `E`, as a scheme over `X` through the
first projection. -/
abbrev levelOver (E : FiniteGaloisIntermediateField K L) : Over X :=
  Over.mk (pullback.fst f (Spec.algebraMap K E))

/-- The automorphism of the base change to `E` induced by the restriction of `σ` to `E`, as a
morphism over `X`. -/
def levelAut (E : FiniteGaloisIntermediateField K L) (σ : L ≃ₐ[K] L) :
    levelOver f E ⟶ levelOver f E :=
  Over.homMk (baseChangeMap f (AlgEquiv.restrictNormalHom E σ)) (by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    erw [pullback.lift_fst]
    exact Category.comp_id _)

theorem levelAut_left (E : FiniteGaloisIntermediateField K L) (σ : L ≃ₐ[K] L) :
    (levelAut f E σ).left = baseChangeMap f (AlgEquiv.restrictNormalHom E σ) := rfl

theorem levelAut_mul (E : FiniteGaloisIntermediateField K L) (σ τ : L ≃ₐ[K] L) :
    levelAut f E (σ * τ) = levelAut f E σ ≫ levelAut f E τ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, levelAut_left, levelAut_left, levelAut_left, baseChangeMap_comp, map_mul]

theorem levelAut_one (E : FiniteGaloisIntermediateField K L) :
    levelAut f E 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [levelAut_left, map_one, baseChangeMap_one]
  rfl

/-- The action of `L ≃ₐ[K] L` on the base change to a finite Galois subextension, through
restriction to that subextension. -/
def levelAction (E : FiniteGaloisIntermediateField K L) : Action ((Over X)ᵒᵖ) (L ≃ₐ[K] L) where
  V := op (levelOver f E)
  ρ :=
    { toFun σ := (levelAut f E σ).op
      map_one' := by rw [levelAut_one]; rfl
      map_mul' σ τ := by
        rw [levelAut_mul]
        rfl }

variable {f} in
/-- The morphism of spectra induced by the inclusion `E ⊆ E'` of finite Galois subextensions. -/
def specInclusion {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E') :
    Spec (CommRingCat.of E') ⟶ Spec (CommRingCat.of E) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (E := (E : IntermediateField K L))
    (F := (E' : IntermediateField K L)) h).toRingHom)

theorem specInclusion_comp_algebraMap {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E') :
    specInclusion h ≫ Spec.algebraMap K E = Spec.algebraMap K E' := by
  rw [specInclusion, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1

theorem specInclusion_specMap {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E')
    (σ : L ≃ₐ[K] L) :
    specInclusion h ≫ specMap (AlgEquiv.restrictNormalHom E σ) =
      specMap (AlgEquiv.restrictNormalHom E' σ) ≫ specInclusion h := by
  rw [specInclusion, specMap, specMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change ((AlgEquiv.restrictNormalHom E σ) x : L) =
    ((AlgEquiv.restrictNormalHom E' σ) (IntermediateField.inclusion h x) : L)
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

theorem specInclusion_refl (E : FiniteGaloisIntermediateField K L) :
    specInclusion (le_refl E) = 𝟙 _ := by
  rw [specInclusion, ← Spec.map_id]
  congr 1

theorem specInclusion_trans {E E' E'' : FiniteGaloisIntermediateField K L} (h : E ≤ E')
    (h' : E' ≤ E'') :
    specInclusion (h.trans h') = specInclusion h' ≫ specInclusion h := by
  rw [specInclusion, specInclusion, specInclusion, ← Spec.map_comp]
  congr 1

/-- The transition morphism `X_{E'} ⟶ X_E` of base changes for `E ⊆ E'`. -/
def levelMapScheme {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E') :
    baseChange K E' f ⟶ baseChange K E f :=
  pullback.map f (Spec.algebraMap K E') f (Spec.algebraMap K E) (𝟙 X) (specInclusion h) (𝟙 _)
    (by simp) (by rw [Category.comp_id, specInclusion_comp_algebraMap])

/-- The transition morphism as a morphism over `X`. -/
def levelMap {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E') :
    levelOver f E' ⟶ levelOver f E :=
  Over.homMk (levelMapScheme f h) (by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    erw [pullback.lift_fst]
    exact Category.comp_id _)

theorem levelMap_left {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E') :
    (levelMap f h).left = levelMapScheme f h := rfl

/-- Transition morphisms are Galois-equivariant. -/
theorem levelMap_levelAut {E E' : FiniteGaloisIntermediateField K L} (h : E ≤ E')
    (σ : L ≃ₐ[K] L) :
    levelMap f h ≫ levelAut f E σ = levelAut f E' σ ≫ levelMap f h := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, levelMap_left, levelAut_left, levelAut_left,
    levelMapScheme, baseChangeMap, baseChangeMap, pullback.map_comp, pullback.map_comp]
  congr 1
  exact specInclusion_specMap h σ

theorem levelMap_refl (E : FiniteGaloisIntermediateField K L) :
    levelMap f (le_refl E) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [levelMap_left, levelMapScheme]
  simp only [specInclusion_refl]
  exact pullback.map_id

theorem levelMap_trans {E E' E'' : FiniteGaloisIntermediateField K L} (h : E ≤ E')
    (h' : E' ≤ E'') :
    levelMap f (h.trans h') = levelMap f h' ≫ levelMap f h := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, levelMap_left, levelMap_left, levelMap_left, levelMapScheme,
    levelMapScheme, levelMapScheme, pullback.map_comp]
  congr 1
  exact specInclusion_trans h h'

/-- The tower of base changes of `X` to the finite Galois subextensions of `L / K`, with the
action of `L ≃ₐ[K] L` through restriction and the transition morphisms of base change. -/
def galoisTower : FiniteGaloisIntermediateField K L ⥤ Action ((Over X)ᵒᵖ) (L ≃ₐ[K] L) where
  obj E := levelAction f E
  map {E E'} h :=
    { hom := (levelMap f (leOfHom h)).op
      comm σ := by
        change (levelAut f E σ).op ≫ (levelMap f (leOfHom h)).op =
          (levelMap f (leOfHom h)).op ≫ (levelAut f E' σ).op
        rw [← op_comp, ← op_comp, levelMap_levelAut] }
  map_id E := by
    apply Action.Hom.ext
    change (levelMap f (le_refl E)).op = 𝟙 _
    rw [levelMap_refl]
    rfl
  map_comp {E E' E''} h h' := by
    apply Action.Hom.ext
    change (levelMap f ((leOfHom h).trans (leOfHom h'))).op =
      (levelMap f (leOfHom h)).op ≫ (levelMap f (leOfHom h')).op
    rw [levelMap_trans, op_comp]

/-- The restriction of `σ` to `E` is trivial when `σ` fixes `E`. -/
theorem levelAut_eq_id_of_mem (E : FiniteGaloisIntermediateField K L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ (E : IntermediateField K L).fixingSubgroup) :
    levelAut f E σ = 𝟙 _ := by
  have h1 : AlgEquiv.restrictNormalHom E σ = 1 :=
    (AlgEquiv.restrictNormal_eq_one_iff (E : IntermediateField K L) σ).2
      ((IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ)
  apply Over.OverMorphism.ext
  rw [levelAut_left, h1, baseChangeMap_one]
  rfl

/-- For the Krull topology, the open subgroup fixing a finite Galois subextension `E` acts
trivially on the base change to `E`. -/
theorem isLevelwiseSmooth_galoisTower :
    EtaleCanonicalDeckTower.IsLevelwiseSmooth (galoisTower (L := L) f) := by
  intro E
  refine ⟨⟨(E : IntermediateField K L).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen (E : IntermediateField K L)⟩, ?_⟩
  intro σ hσ
  change (levelAut f E σ).op = 𝟙 _
  rw [levelAut_eq_id_of_mem f E hσ]
  rfl

section Cohomology

variable (L) (R : Type u) [CommRing R]
variable [∀ x : FiniteGaloisIntermediateField K L × SingleObj (L ≃ₐ[K] L),
  HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf
    ((EtaleCanonicalDeckTower.schemeDiagram (galoisTower (L := L) f)).obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Degree `q` étale cohomology of the base changes to finite Galois subextensions, with
coefficients pulled back from `X`, passed to the colimit over the subextensions: a smooth
representation of `L ≃ₐ[K] L` for the Krull topology, natural in the coefficient sheaf on `X`. -/
def smoothGaloisCohomologyFunctor (q : ℕ) :
    EtaleDerivedSections.ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R (L ≃ₐ[K] L) :=
  EtaleCanonicalDeckTower.smoothColimitCohomologyFunctor R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f) q

/-- Global sections of the base changes to finite Galois subextensions, passed to the colimit,
as a smooth representation. -/
def smoothGaloisSectionsFunctor :
    EtaleDerivedSections.ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R (L ≃ₐ[K] L) :=
  EtaleCanonicalDeckTower.smoothColimitSectionsFunctor R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f)

/-- Degree `q` cohomology of the base change to one finite Galois subextension `E`, as a smooth
representation on which the subgroup fixing `E` acts trivially. -/
def smoothGaloisLevelCohomologyFunctor (q : ℕ) (E : FiniteGaloisIntermediateField K L) :
    EtaleDerivedSections.ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R (L ≃ₐ[K] L) :=
  EtaleCanonicalDeckTower.smoothLevelCohomologyFunctor R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f) q E

/-- The map from the cohomology of the base change to `E` into the colimit. -/
def smoothGaloisLevelCohomologyι (q : ℕ) (E : FiniteGaloisIntermediateField K L) :
    smoothGaloisLevelCohomologyFunctor.{u, wS, wR} L f R q E ⟶
      smoothGaloisCohomologyFunctor.{u, wS, wR} L f R q :=
  EtaleCanonicalDeckTower.smoothLevelCohomologyι R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f) q E

/-- In degree zero, the colimit cohomology is the colimit of global sections. -/
def smoothGaloisCohomologyZeroIso :
    smoothGaloisCohomologyFunctor.{u, wS, wR} L f R 0 ≅
      smoothGaloisSectionsFunctor.{u, wS, wR} L f R :=
  EtaleCanonicalDeckTower.smoothColimitCohomologyZeroIso R (galoisTower f)
    (isLevelwiseSmooth_galoisTower f)

instance : Nonempty (FiniteGaloisIntermediateField K L) := ⟨⊥⟩

/-- Every colimit cohomology class comes from the base change to some finite Galois
subextension. -/
theorem galoisCohomology_exists_level (q : ℕ) (M : EtaleDerivedSections.ModuleSheaf X R)
    (x : ((EtaleCanonicalDeckTower.colimitCohomologyFunctor R (galoisTower (L := L) f) q).obj
      M).V) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : (((EtaleCanonicalDeckTower.cohomologyFunctor R (galoisTower (L := L) f) q).obj
        M).obj E).V),
      ((EtaleCanonicalDeckTower.levelCohomologyι R (galoisTower (L := L) f) q E).app
        M).hom.hom y = x :=
  EtaleCanonicalDeckTower.levelCohomologyι_exists_rep R (galoisTower f) q M x

/-- Every colimit global section comes from the base change to some finite Galois
subextension. -/
theorem galoisSections_exists_level (M : EtaleDerivedSections.ModuleSheaf X R)
    (x : ((EtaleCanonicalDeckTower.colimitSectionsFunctor R (galoisTower (L := L) f)).obj M).V) :
    ∃ (E : FiniteGaloisIntermediateField K L)
      (y : (((EtaleCanonicalDeckTower.sectionsFunctor R (galoisTower (L := L) f)).obj
        M).obj E).V),
      ((EtaleCanonicalDeckTower.levelSectionsι R (galoisTower (L := L) f) E).app
        M).hom.hom y = x :=
  EtaleCanonicalDeckTower.levelSectionsι_exists_rep R (galoisTower f) M x

end Cohomology

end Langlands.Geometry.EtaleGaloisTower
