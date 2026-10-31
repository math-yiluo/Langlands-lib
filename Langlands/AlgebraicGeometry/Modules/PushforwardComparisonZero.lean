import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange

/-! # Degree-zero compatibility of the pushforward comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry

namespace Langlands.Cohomology.AcyclicResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] {H : C ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H)

/-- The degree-zero composite comparison agrees with the canonical maps
from the original functors to their zeroth right derived functors. -/
@[reassoc]
theorem toRightDerivedZero_compComparison (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    H.toRightDerivedZero.app A ≫ compComparison G e A hA 0 =
      e.inv.app A ≫ G.toRightDerivedZero.app (F.obj A) := by
  let I := injectiveResolution A
  let ε := mapAugmentation F I
  let ψ := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app
    I.cocomplex
  have := quasiIso_mapAugmentation F I hA
  have hcycles :
      I.toRightDerivedZero' H ≫ HomologicalComplex.cyclesMap ψ 0 =
        e.inv.app A ≫ toCyclesZero G ε := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
    simp only [Category.assoc]
    change I.toRightDerivedZero' H ≫ HomologicalComplex.cyclesMap ψ 0 ≫
        ((G.mapHomologicalComplex _).obj
          ((F.mapHomologicalComplex _).obj I.cocomplex)).iCycles 0 =
      e.inv.app A ≫ toCyclesZero G ε ≫
        ((G.mapHomologicalComplex _).obj
          ((F.mapHomologicalComplex _).obj I.cocomplex)).iCycles 0
    erw [HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc,
      toCyclesZero_iCycles]
    have hε : ε.f 0 = F.map (I.ι.f 0) := by
      dsimp only [ε]
      rw [mapAugmentation_f_zero]
      change F.map (𝟙 _ ≫ I.ι.f 0) = _
      rw [Category.id_comp]
    rw [hε]
    exact e.inv.naturality (I.ι.f 0)
  have hG :
      G.toRightDerivedZero.app (F.obj A) =
        toCyclesZero G ε ≫
          ((G.mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj
            I.cocomplex)).homologyπ 0 ≫ resolutionComparison G ε 0 :=
    toRightDerivedZero_eq_comparison G ε (injectiveResolution (F.obj A))
      (lift ε (𝟙 (F.obj A)) (injectiveResolution (F.obj A)).ι)
      (comp_lift_id ε (injectiveResolution (F.obj A)))
  change H.toRightDerivedZero.app A ≫
      (I.isoRightDerivedObj H 0).hom ≫
        (HomologicalComplex.homologyFunctor E _ 0).map ψ ≫
          resolutionComparison G ε 0 = _
  rw [I.toRightDerivedZero_eq H]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change I.toRightDerivedZero' H ≫
      ((H.mapHomologicalComplex _).obj I.cocomplex).homologyπ 0 ≫
        HomologicalComplex.homologyMap ψ 0 ≫
          resolutionComparison G ε 0 = _
  rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc,
    hcycles, Category.assoc, hG]
  rfl

/-- For left exact functors, the degree-zero composite comparison is
the ordinary functor comparison through the canonical zeroth-derived
identifications. -/
theorem compComparison_zero [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    compComparison G e A hA 0 =
      H.rightDerivedZeroIsoSelf.hom.app A ≫ e.inv.app A ≫
        G.rightDerivedZeroIsoSelf.inv.app (F.obj A) := by
  apply (cancel_epi (H.rightDerivedZeroIsoSelf.inv.app A)).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.rightDerivedZeroIsoSelf_inv, NatTrans.comp_app,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc] using
    toRightDerivedZero_compComparison G e A hA

instance isIso_compComparison_zero [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    IsIso (compComparison G e A hA 0) := by
  rw [compComparison_zero]
  infer_instance

/-- The degree-zero composite comparison is an isomorphism for left exact
functors, without any hypothesis about images of injective objects. -/
def compComparisonZeroIso [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    (H.rightDerived 0).obj A ≅ (G.rightDerived 0).obj (F.obj A) :=
  asIso (compComparison G e A hA 0)

@[simp]
lemma compComparisonZeroIso_hom [PreservesFiniteLimits G] [PreservesFiniteLimits H]
    (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    (compComparisonZeroIso G e A hA).hom = compComparison G e A hA 0 := rfl

end Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Cohomology.AcyclicResolution

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {R : CommRingCat.{u}}
  (g : Y ⟶ Spec R)

/-- In degree zero the published pushforward comparison is the
ordinary composition isomorphism on relative global sections. -/
theorem pushforwardComparison_zero (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) :
    pushforwardComparison h g M hM 0 =
      (relativeCohomologyZeroIso (h ≫ g)).hom.app M ≫
        (relativeGlobalSectionsCompIso h g).inv.app M ≫
        (relativeCohomologyZeroIso g).inv.app
          ((Scheme.Modules.pushforward h).obj M) :=
  compComparison_zero _ _ M hM

end Langlands.AlgebraicGeometry.Modules.DerivedSections
