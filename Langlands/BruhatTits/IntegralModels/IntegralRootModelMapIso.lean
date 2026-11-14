import Langlands.BruhatTits.IntegralModels.IntegralRootModelMap
import Langlands.BruhatTits.IntegralModels.RootModelPresentationIso

/-! # Actual root-map isomorphisms at equal zero-fixer depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

private theorem modelIso_comp
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
    {C : KPApartmentData i ω} {x : C.Apartment} {a : relativeRoots i} {r s : ℝ}
    (U : RootFiltrationModelData R K C x a r)
    (V : RootFiltrationModelData R K C x a s)
    (e : U.model.Iso V.model (U.genericIso V))
    {N N' : IntegralModel R K G}
    (j : U.model.Hom N U.inclusion) (k : V.model.Hom N' V.inclusion)
    (ψ : N.Hom N' (𝟙 G)) :
    e.iso.hom ≫ k.hom = j.hom ≫ ψ.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono N'.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc, k.generic_comm,
    ψ.generic_comm, Category.comp_id]
  rw [← Category.assoc, e.generic_comm, Category.assoc,
    U.genericIso_hom_comp V, ← j.generic_comm]

end Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hb' : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))

private instance sourceNeutral_smooth : Smooth source.neutral.group.X.hom :=
  source.neutral_smooth

private instance targetNeutral_smooth : Smooth target.neutral.group.X.hom :=
  target.neutral_smooth

include hsource htarget hne hne' hb hb'

/-- Equality of actual root-fixer depths makes the canonical integral root
map an isomorphism. The ambient model map need not be smooth. -/
theorem integralRootMap_isIso_of_rootFixerDepth_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    IsIso (φ.integralRootMap T hT a a.2.1) := by
  let A := T.toIntegralSplitTorusData hT
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let U := A.unramifiedZeroRootFiltrationModelData C E Ω' hsource hne' hb' x a
  let V := B.unramifiedZeroRootFiltrationModelData C E Ω htarget hne hb x a
  let e := U.unramifiedModelIsoOfFiltrationEq V (by rw [hdepth])
  have he :
      e.iso.hom ≫ (B.rootModelMap a a.2.1).hom =
        (A.rootModelMap a a.2.1).hom ≫ φ.neutral.hom := by
    exact U.modelIso_comp V e (A.rootModelMap a a.2.1)
      (B.rootModelMap a a.2.1) φ.neutral
  have hmap : φ.integralRootMap T hT a a.2.1 = e.iso.hom := by
    apply (B.rootModelMap_isRepresentedBy a a.2.1).hom_ext
    have hcomp :
        φ.integralRootMap T hT a a.2.1 ≫ (B.rootModelMap a a.2.1).hom =
          (A.rootModelMap a a.2.1).hom ≫ φ.neutral.hom :=
      φ.integralRootMap_comp T hT a a.2.1
    exact hcomp.trans he.symm
  rw [hmap]
  infer_instance

/-- The actual residue base change of the equal-depth root map is an
isomorphism on all scheme tests. -/
theorem residueRootMap_isIso_of_rootFixerDepth_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    IsIso (φ.residueRootMap T hT a a.2.1) := by
  let : IsIso (φ.integralRootMap T hT a a.2.1) :=
    φ.integralRootMap_isIso_of_rootFixerDepth_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth
  exact (GroupScheme.baseChange (IntegralModel.residueBaseMap
    (fixedFieldIntegers F))).map_isIso _

/-- The equal-depth isomorphism whose forward map is the canonical actual
integral root map. -/
def integralRootIsoOfRootFixerDepthEq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    ((T.toIntegralSplitTorusData hT).rootModel a a.2.1).group ≅
      (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModel a a.2.1).group := by
  let : IsIso (φ.integralRootMap T hT a a.2.1) :=
    φ.integralRootMap_isIso_of_rootFixerDepth_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth
  exact asIso (φ.integralRootMap T hT a a.2.1)

@[simp] theorem integralRootIsoOfRootFixerDepthEq_hom
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    (φ.integralRootIsoOfRootFixerDepthEq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth).hom =
        φ.integralRootMap T hT a a.2.1 := rfl

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
