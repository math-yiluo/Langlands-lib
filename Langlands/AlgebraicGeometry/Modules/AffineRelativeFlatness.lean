import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Flat.Localization
import Langlands.AlgebraicGeometry.Modules.AffineRelativeFlatnessStatement
import Langlands.AlgebraicGeometry.Modules.RestrictionStalkLinearEquiv
import Langlands.AlgebraicGeometry.Modules.AffineCartesianSectionsBaseChange
import Langlands.Algebra.LocalApproximationFlatnessPropagation

/-! # Relative flatness and flat sections on affine schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- A relatively flat associated sheaf has stalks flat over the affine base ring. -/
lemma flat_stalk_tilde_of_isFlatOver (N : ModuleCat.{u} B)
    (hN : IsFlatOver (Spec.map φ) (tilde N)) (x : PrimeSpectrum B) :
    letI := Module.compHom (stalk (tilde N) x) φ.hom
    Module.Flat A (stalk (tilde N) x) := by
  let : Algebra A ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (Algebra A
      ((structurePresheafInCommRingCat A).stalk (PrimeSpectrum.comap φ.hom x)))
  let : IsLocalization (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (IsLocalization (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk (PrimeSpectrum.comap φ.hom x)))
  let : Module A (stalk (tilde N) x) := Module.compHom _ φ.hom
  let := relativeStalkModule (Spec.map φ) (tilde N) x
  have : IsScalarTower A ((Spec A).presheaf.stalk ((Spec.map φ) x))
      (stalk (tilde N) x) := .of_algebraMap_smul (fun a m => by
    change (Spec.map φ).stalkMap x (StructureSheaf.toStalk A _ a) • m =
      (show (Spec B).presheaf.stalk x from StructureSheaf.toStalk B x (φ a)) • m
    exact congrArg (fun t : (Spec B).presheaf.stalk x => t • m)
      (stalkMap_toStalk_apply φ x a))
  have : Module.Flat A ((Spec A).presheaf.stalk ((Spec.map φ) x)) :=
    IsLocalization.flat _ (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
  have : Module.Flat ((Spec A).presheaf.stalk ((Spec.map φ) x))
      (stalk (tilde N) x) := hN x
  exact Module.Flat.trans A ((Spec A).presheaf.stalk ((Spec.map φ) x)) _

/-- Relative stalk flatness of an associated sheaf implies flatness of its defining
module over the actual affine base ring. -/
lemma flat_of_isFlatOver_tilde (N : ModuleCat.{u} B)
    (hN : IsFlatOver (Spec.map φ) (tilde N)) :
    letI := Module.compHom N φ.hom
    Module.Flat A N := by
  let := φ.hom.toAlgebra
  let : Module A N := Module.compHom N φ.hom
  have : IsScalarTower A B N := .of_algebraMap_smul (fun _ _ => rfl)
  let Np (P : Ideal B) [P.IsMaximal] : Type u :=
    stalk (tilde N) (⟨P, inferInstance⟩ : PrimeSpectrum B)
  let mA : ∀ (P : Ideal B) [P.IsMaximal], Module A (Np P) :=
    fun P _ => Module.compHom (Np P) φ.hom
  have hloc (x : PrimeSpectrum B) :
      IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk N x).hom := inferInstance
  exact @Module.flat_of_isLocalized_maximal A B _ _ _ N _ _ _ _ Np
    (fun _ _ => inferInstance)
    mA
    (fun _ _ => inferInstance)
    (fun P _ => by
      let := mA P
      exact .of_algebraMap_smul (fun _ _ => rfl))
    (fun P _ => (tilde.toStalk N ⟨P, inferInstance⟩).hom)
    (fun P _ => hloc ⟨P, inferInstance⟩)
    (fun P _ => flat_stalk_tilde_of_isFlatOver φ N hN ⟨P, inferInstance⟩)

/-- The actual affine section module of a relatively flat quasi-coherent sheaf is
flat over the base ring via the given ring map. -/
lemma flat_moduleSpecΓFunctor_of_isFlatOver (M : (Spec B).Modules)
    [M.IsQuasicoherent] (hM : IsFlatOver (Spec.map φ) M) :
    letI := Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
    Module.Flat A (moduleSpecΓFunctor.obj M) := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact flat_of_isFlatOver_tilde φ (moduleSpecΓFunctor.obj M)
    ((isFlatOver_iff_of_iso (Spec.map φ) (asIso M.fromTildeΓ)).mpr hM)

/-- Modules on the target ring which are flat over the source of the actual ring map. -/
def affineFlatModules : ObjectProperty (ModuleCat.{u} B) := fun N =>
  letI := Module.compHom N φ.hom
  Module.Flat A N

/-- Ordinary affine sections, restricted to relatively flat quasi-coherent sheaves
and with their proved base flatness retained. -/
def flatAffineSectionsFunctor :
    (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf ⊓
      isFlatOver (Spec.map φ)).FullSubcategory ⥤
        (affineFlatModules φ).FullSubcategory :=
  (affineFlatModules φ).lift
    ((SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf ⊓
      isFlatOver (Spec.map φ)).ι ⋙ moduleSpecΓFunctor)
    (fun M => by
      let : M.obj.IsQuasicoherent := M.property.1
      exact flat_moduleSpecΓFunctor_of_isFlatOver φ M.obj M.property.2)

end Langlands.AlgebraicGeometry.Modules

open CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules

variable {R B : CommRingCat.{u}}

/-- The affine relative flatness comparison for one ring map and module. -/
lemma isFlatOver_tilde_iff (φ : R ⟶ B) (M : ModuleCat.{u} B) :
    let := φ.hom.toAlgebra
    let : Module R M := Module.compHom M φ.hom
    IsFlatOver (Spec.map φ) (tilde M) ↔ Module.Flat R M := by
  let := φ.hom.toAlgebra
  let : Module R M := Module.compHom M φ.hom
  have : IsScalarTower R B M := .of_algebraMap_smul (fun _ _ => rfl)
  let (x : Spec B) : Algebra B ((Spec B).presheaf.stalk x) :=
    inferInstanceAs (Algebra B ((structurePresheafInCommRingCat B).stalk x))
  let (x : Spec B) : Module R (stalk (tilde M) x) :=
    Module.compHom _ φ.hom
  have (x : Spec B) : IsScalarTower B ((Spec B).presheaf.stalk x) (stalk (tilde M) x) :=
    inferInstanceAs (IsScalarTower B ((structurePresheafInCommRingCat B).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf B M).presheaf x))
  have (x : Spec B) : IsScalarTower R B (stalk (tilde M) x) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let (x : Spec B) : Algebra R ((Spec R).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (Algebra R
      ((structurePresheafInCommRingCat R).stalk (PrimeSpectrum.comap φ.hom x)))
  let (x : Spec B) : Module ((Spec R).presheaf.stalk ((Spec.map φ) x))
      (stalk (tilde M) x) := relativeStalkModule (Spec.map φ) (tilde M) x
  have (x : Spec B) : IsScalarTower R
      ((Spec R).presheaf.stalk ((Spec.map φ) x)) (stalk (tilde M) x) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change ((Spec.map φ).stalkMap x) (StructureSheaf.toStalk R _ r) • m = (φ r) • m
    have h := congrArg (fun k => k r) (stalkMap_toStalk φ x)
    change (Spec.map φ).stalkMap x (StructureSheaf.toStalk R _ r) =
      StructureSheaf.toStalk B x (φ r) at h
    rw [h]
    exact IsScalarTower.algebraMap_smul ((Spec B).presheaf.stalk x) (φ r) m
  let (x : Spec B) : IsLocalization
      (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((Spec R).presheaf.stalk ((Spec.map φ) x)) :=
    inferInstanceAs (IsLocalization (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl
      ((structurePresheafInCommRingCat R).stalk (PrimeSpectrum.comap φ.hom x)))
  have hlocal (x : Spec B) : IsLocalizedModule x.asIdeal.primeCompl
      (tilde.toStalk M x).hom := inferInstance
  constructor
  · intro h
    have hlocall : ∀ (P : Ideal B) [P.IsMaximal], IsLocalizedModule.AtPrime P
        (tilde.toStalk M (⟨P, inferInstance⟩ : Spec B)).hom := fun P _ => hlocal ⟨P, inferInstance⟩
    exact @Module.flat_of_isLocalized_maximal R B _ _ _ M _ _ _ _
      (fun P => stalk (tilde M) (⟨P, inferInstance⟩ : Spec B)) _ _ _ _
      (fun P => (tilde.toStalk M (⟨P, inferInstance⟩ : Spec B)).hom) hlocall
      (fun P => (Module.flat_iff_of_isLocalization
        ((Spec R).presheaf.stalk ((Spec.map φ) (⟨P, inferInstance⟩ : Spec B)))
        (PrimeSpectrum.comap φ.hom (⟨P, inferInstance⟩ : Spec B)).asIdeal.primeCompl
        _).mp (h _))
  · intro h x
    have := h
    have := Langlands.Algebra.flat_of_isLocalizedModule_of_flat (R := R)
      x.asIdeal.primeCompl (tilde.toStalk M x).hom
    exact (Module.flat_iff_of_isLocalization
      ((Spec R).presheaf.stalk ((Spec.map φ) x))
      (PrimeSpectrum.comap φ.hom x).asIdeal.primeCompl _).mpr this

/-- Relative flatness of a quasicoherent module on an affine scheme can be tested on its
module of global sections. -/
lemma isFlatOver_iff_flat_sections (φ : R ⟶ B) (M : (Spec B).Modules) [M.IsQuasicoherent] :
    let := φ.hom.toAlgebra
    let : Module R (moduleSpecΓFunctor.obj M) :=
      Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
    IsFlatOver (Spec.map φ) M ↔ Module.Flat R (moduleSpecΓFunctor.obj M) := by
  rw [← isFlatOver_iff_of_iso (Spec.map φ) (asIso M.fromTildeΓ)]
  exact isFlatOver_tilde_iff φ _

/-- The same affine section criterion for a morphism between spectra given in scheme form. -/
lemma isFlatOver_spec_iff_flat_sections (f : Spec B ⟶ Spec R) (M : (Spec B).Modules)
    [M.IsQuasicoherent] :
    let φ : R ⟶ B := (Scheme.Spec.preimage f).unop
    let := φ.hom.toAlgebra
    let : Module R (moduleSpecΓFunctor.obj M) :=
      Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
    IsFlatOver f M ↔ Module.Flat R (moduleSpecΓFunctor.obj M) := by
  let φ : R ⟶ B := (Scheme.Spec.preimage f).unop
  let := φ.hom.toAlgebra
  let : Module R (moduleSpecΓFunctor.obj M) :=
    Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
  change IsFlatOver f M ↔ Module.Flat R (moduleSpecΓFunctor.obj M)
  have hf : Spec.map φ = f := Scheme.Spec.map_preimage f
  rw [← hf]
  exact isFlatOver_iff_flat_sections φ M

/-- An open restriction has the same actual stalk, linearly over the base local ring. -/
def relativeRestrictStalkLinearEquiv {X Y S : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] (f : Y ⟶ S) (M : Y.Modules) (x : X) :
    letI : Module (S.presheaf.stalk (f (g x))) (stalk (M.restrict g) x) :=
      relativeStalkModule (g ≫ f) (M.restrict g) x
    letI : Module (S.presheaf.stalk (f (g x))) (stalk M (g x)) :=
      relativeStalkModule f M (g x)
    stalk (M.restrict g) x ≃ₗ[S.presheaf.stalk (f (g x))] stalk M (g x) := by
  let R := S.presheaf.stalk (f (g x))
  let A := Y.presheaf.stalk (g x)
  let : Algebra R A := (f.stalkMap (g x)).hom.toAlgebra
  let : Module A (stalk (M.restrict g) x) := relativeStalkModule g (M.restrict g) x
  let : Module R (stalk (M.restrict g) x) := relativeStalkModule (g ≫ f) (M.restrict g) x
  let : Module R (stalk M (g x)) := relativeStalkModule f M (g x)
  have : IsScalarTower R A (stalk (M.restrict g) x) :=
    .of_algebraMap_smul (fun r m => by
      change g.stalkMap x (f.stalkMap (g x) r) • m = (g ≫ f).stalkMap x r • m
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  have : IsScalarTower R A (stalk M (g x)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact (restrictStalkLinearEquiv g M x).restrictScalars R

/-- Relative flatness is local on the source for a jointly surjective family of open charts. -/
lemma isFlatOver_iff_openCover {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules)
    {ι : Type*} (X : ι → Scheme.{u}) (g : ∀ i, X i ⟶ Y)
    [∀ i, IsOpenImmersion (g i)] (hcover : ∀ y : Y, ∃ i, ∃ x : X i, g i x = y) :
    IsFlatOver f M ↔ ∀ i, IsFlatOver (g i ≫ f) (M.restrict (g i)) := by
  constructor
  · intro h i x
    let : Module (S.presheaf.stalk (f (g i x))) (stalk (M.restrict (g i)) x) :=
      relativeStalkModule (g i ≫ f) (M.restrict (g i)) x
    let : Module (S.presheaf.stalk (f (g i x))) (stalk M (g i x)) :=
      relativeStalkModule f M (g i x)
    exact (Module.Flat.equiv_iff (relativeRestrictStalkLinearEquiv (g i) f M x)).mpr (h _)
  · intro h y
    obtain ⟨i, x, rfl⟩ := hcover y
    let : Module (S.presheaf.stalk (f (g i x))) (stalk (M.restrict (g i)) x) :=
      relativeStalkModule (g i ≫ f) (M.restrict (g i)) x
    let : Module (S.presheaf.stalk (f (g i x))) (stalk M (g i x)) :=
      relativeStalkModule f M (g i x)
    exact (Module.Flat.equiv_iff (relativeRestrictStalkLinearEquiv (g i) f M x)).mp (h i x)

/-- Relative flatness on a spectrum is flatness of relative global sections. -/
lemma isFlatOver_iff_flat_relativeGlobalSections_spec
    (f : Spec B ⟶ Spec R) (M : (Spec B).Modules) [M.IsQuasicoherent] :
    IsFlatOver f M ↔ Module.Flat R ((DerivedSections.relativeGlobalSections f).obj M) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage f⟩
  let := φ.hom.toAlgebra
  let : Module R (moduleSpecΓFunctor.obj M) :=
    Module.compHom (moduleSpecΓFunctor.obj M) φ.hom
  let e : (DerivedSections.relativeGlobalSections (Spec.map φ)).obj M ≃ₗ[R]
      (moduleSpecΓFunctor.obj M) :=
    ((Langlands.Scheme.Modules.pushforwardΓIso φ).app M).toLinearEquiv
  exact (isFlatOver_iff_flat_sections φ M).trans (Module.Flat.equiv_iff e).symm

/-- Relative flatness is unchanged by a surjective open restriction of the source. -/
lemma isFlatOver_iff_restrict_of_surjective {X Y S : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] [Surjective g] (f : Y ⟶ S) (M : Y.Modules) :
    IsFlatOver f M ↔ IsFlatOver (g ≫ f) (M.restrict g) := by
  have h := isFlatOver_iff_openCover f M (fun _ : Unit => X) (fun _ => g)
    (fun y => by obtain ⟨x, hx⟩ := g.surjective y; exact ⟨(), x, hx⟩)
  exact h.trans ⟨fun h => h (), fun h _ => h⟩

/-- On any affine source, relative flatness is flatness of the actual relative section module. -/
lemma isFlatOver_iff_flat_relativeGlobalSections {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent] :
    IsFlatOver f M ↔ Module.Flat R ((DerivedSections.relativeGlobalSections f).obj M) := by
  let p := X.isoSpec.inv
  have hw : p ≫ f = (p ≫ f) ≫ Spec.map (𝟙 R) := by simp
  have hp := DerivedSections.isIso_scalarSectionsBaseChangeMap_of_isIso
    (𝟙 R) f (p ≫ f) p hw M
  let e : (DerivedSections.relativeGlobalSections f).obj M ≅
      (DerivedSections.relativeGlobalSections (p ≫ f)).obj (M.restrict p) :=
    (ModuleCat.extendScalarsId R).symm.app _ ≪≫
      asIso (DerivedSections.scalarSectionsBaseChangeMap (𝟙 R) f (p ≫ f) p hw M) ≪≫
      (DerivedSections.relativeGlobalSections (p ≫ f)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback p).app M).symm
  exact (isFlatOver_iff_restrict_of_surjective p f M).trans
    ((isFlatOver_iff_flat_relativeGlobalSections_spec (p ≫ f) (M.restrict p)).trans
      (Module.Flat.equiv_iff e.toLinearEquiv).symm)

/-- Relative flatness of associated sheaves is algebraic flatness over the base ring. -/
theorem affineRelativeFlatness : AffineRelativeFlatnessStatement.{u} :=
  fun _ _ φ M => isFlatOver_tilde_iff φ M

end Langlands.AlgebraicGeometry.Modules
