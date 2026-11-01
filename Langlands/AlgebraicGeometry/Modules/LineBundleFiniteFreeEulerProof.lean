import Langlands.AlgebraicGeometry.Modules.LineBundleFiniteFreeEulerStatement
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AlgebraicGeometry.Picard.LocallyFreeTensorInvertibleProof
import Langlands.CategoryTheory.Picard.TensorEquivalenceProof
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite free factors in actual line-bundle cohomology -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules

/-- Sections of the actual finite free sheaf are finite tuples of functions. -/
def finiteFreeSectionsIso (X : Scheme.{u}) (r : ℕ) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (.op U)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      ModuleCat.of Γ(X, U) (Fin r → Γ(X, U)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (.op U)
  let : E.Additive := inferInstanceAs
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (.op U)).Additive)
  exact E.mapIso (Sigma.reindex Equiv.ulift (fun _ : Fin r => structureSheaf X)) ≪≫
    PreservesCoproduct.iso E (fun _ : Fin r => structureSheaf X) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin r => E.obj (structureSheaf X))).symm ≪≫
    ModuleCat.biproductIsoPi _

/-- Every open, in particular every affine open, has finite free-sheaf sections. -/
lemma finiteFreeSections_finite (X : Scheme.{u}) (r : ℕ) (U : X.Opens) :
    Module.Finite Γ(X, U)
      Γ(SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)), U) := by
  exact Module.Finite.equiv (finiteFreeSectionsIso X r U).symm.toLinearEquiv

/-- Restriction to an open subscheme preserves the actual free sheaf. -/
def restrictFiniteFreeIso {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    (r : ℕ) :
    (Scheme.Modules.restrictFunctor h).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) :=
by
  let : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor h) := inferInstance
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.restrictFunctor h) (ULift.{u} (Fin r))
    (Scheme.Modules.restrictUnitIso h).symm).symm

/-- Tensoring a line bundle with the actual finite free sheaf gives a
finite coproduct of copies of that line bundle. -/
def lineBundleFiniteFreeTensorIso {X : Scheme.{u}} (L : Picard.LineBundle X) (r : ℕ) :
    Langlands.Scheme.Modules.tensorObj L.obj
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) ≅
      ∐ (fun _ : Fin r => L.obj) := by
  let : (tensorLeft L.obj).IsEquivalence :=
    (Langlands.CategoryTheory.Picard.tensorInvertibilityEquivalence X.Modules L.obj).mp
      (Picard.locallyFreeRankOneTensorInvertible X L.obj L.property)
  exact (localizedTensorIso X _ _).symm ≪≫
    (tensorLeft L.obj).mapIso
      (Sigma.reindex Equiv.ulift (fun _ : Fin r => structureSheaf X)) ≪≫
    PreservesCoproduct.iso (tensorLeft L.obj) (fun _ : Fin r => structureSheaf X) ≪≫
    Sigma.mapIso (fun _ : Fin r => ρ_ L.obj)

/-- Additivity identifies the cohomology of a finite coproduct with the
ordinary finite product of its cohomology vector spaces. -/
def finiteCoproductCohomologyIso {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (r n : ℕ) :
    (relativeCohomology s n).obj (∐ (fun _ : Fin r => M)) ≅
      ModuleCat.of K (Fin r → (relativeCohomology s n).obj M) := by
  let : (relativeGlobalSections s).Additive :=
    (inferInstance : ∀ {R : CommRingCat.{u}} (g : X ⟶ Spec R),
      (relativeGlobalSections g).Additive) s
  let : (relativeCohomology s n).Additive := by
    change ((relativeGlobalSections s).rightDerived n).Additive
    constructor
    intro A B f g
    let I := injectiveResolution A
    let J := injectiveResolution B
    have hw : I.ι ≫ (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I) =
        (CochainComplex.single₀ X.Modules).map (f + g) ≫ J.ι := by
      simp only [Preadditive.comp_add, InjectiveResolution.desc_commutes,
        Functor.map_add, Preadditive.add_comp]
    rw [(relativeGlobalSections s).rightDerived_map_eq n (f + g) _ hw,
      (relativeGlobalSections s).rightDerived_map_eq n f _
        (InjectiveResolution.desc_commutes f J I),
      (relativeGlobalSections s).rightDerived_map_eq n g _
        (InjectiveResolution.desc_commutes g J I)]
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  exact PreservesCoproduct.iso (relativeCohomology s n) (fun _ : Fin r => M) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin r => (relativeCohomology s n).obj M)).symm ≪≫
    ModuleCat.biproductIsoPi _

/-- The cohomology comparison for the actual tensor with a finite free sheaf. -/
def lineBundleFiniteFreeCohomologyIso {K : Type u} [Field K] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of K)) (L : Picard.LineBundle X) (r n : ℕ) :
    (relativeCohomology s n).obj
        (Langlands.Scheme.Modules.tensorObj L.obj
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) ≅
      ModuleCat.of K (Fin r → (relativeCohomology s n).obj L.obj) :=
  (relativeCohomology s n).mapIso (lineBundleFiniteFreeTensorIso L r) ≪≫
    finiteCoproductCohomologyIso s L.obj r n

/-- The finite free tensor has finite cohomology and the expected Euler value,
including when its rank is zero. -/
theorem lineBundleFiniteFreeEuler : LineBundleFiniteFreeEulerStatement.{u} := by
  intro K _ X s L r hL
  let M := Langlands.Scheme.Modules.tensorObj L.obj
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
  let E (n : ℕ) := lineBundleFiniteFreeCohomologyIso s L r n
  have hM : HasFiniteCohomology s M := by
    constructor
    · intro n
      let : Module.Finite K ((relativeCohomology s n).obj L.obj) := hL.1 n
      exact Module.Finite.equiv (E n).symm.toLinearEquiv
    · obtain ⟨b, hb⟩ := hL.2
      refine ⟨b, fun n hn => ?_⟩
      let : Subsingleton ((relativeCohomology s n).obj L.obj) :=
        ModuleCat.subsingleton_of_isZero (hb n hn)
      exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of K (Fin r → (relativeCohomology s n).obj L.obj))) (E n)
  refine ⟨hM, ?_⟩
  intro hM'
  have hrank (n : ℕ) :
      Module.finrank K ((relativeCohomology s n).obj M) =
        r * Module.finrank K ((relativeCohomology s n).obj L.obj) := by
    let : Module.Finite K ((relativeCohomology s n).obj L.obj) := hL.1 n
    rw [(E n).toLinearEquiv.finrank_eq]
    simp [Module.finrank_pi_fintype]
  unfold eulerCharacteristic
  rw [mul_finsum]
  apply finsum_congr
  intro n
  rw [hrank]
  push_cast
  ring

end Langlands.AlgebraicGeometry.Modules.DerivedSections
