import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleSupport
import Langlands.Sheaf.PointProductSetSections

/-! # Ordinary-open fibers and coordinates of actual analytic point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL wI w

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)

/-- An ordinary-open domain is subterminal in the actual analytic étale site. -/
instance openEtaleToSelf_mono (U : Opens (localizedSpaceFunctor.obj X)) :
    Mono (openEtaleToSelf X U) where
  right_cancellation _ _ _ := Subsingleton.elim _ _

/-- Each actual analytic point has at most one lift to an ordinary-open domain. -/
theorem subsingleton_openEtale_fiber
    (x : (localizedFieldPointFunctor L).obj X)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    Subsingleton ((etalePoints L h x).fiber.obj (openEtaleObject X U)) := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  let hself : IsTerminal (etaleSelf X) := IsTerminal.ofUniqueHom
    (fun V => MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun V f => MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))
  exact (etalePoints L h x).subsingleton_fiber_obj (openEtaleToSelf X U) hself

/-- A field-point lift to an ordinary domain projects into its defining open. -/
theorem projection_mem_of_openEtale_fiber
    (x : (localizedFieldPointFunctor L).obj X)
    (U : Opens (localizedSpaceFunctor.obj X))
    (p : (etalePoints L h x).fiber.obj (openEtaleObject X U)) :
    pointProjection L X x ∈ U := by
  let D := (presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen
  have hp : localizedSpaceFunctor.map (domainι X D)
      (pointProjection L (openEtaleObject X U).left p.down.1) = pointProjection L X x :=
    (pointProjection_map L (domainι X D) p.down.1).symm.trans
      (congrArg (pointProjection L X) p.down.2)
  have hv := domainι_apply D
    (pointProjection L (openEtaleObject X U).left p.down.1)
  exact (hv.symm.trans hp) ▸
    (pointProjection L (openEtaleObject X U).left p.down.1).property

variable [T2Space (localizedSpaceFunctor.obj X)]

/-- The actual étale point fiber over an ordinary open is the standard
ordinary-topology point fiber, in the independent coefficient universe. -/
def openEtaleFiberEquiv
    (x : (localizedFieldPointFunctor L).obj X)
    (U : Opens (localizedSpaceFunctor.obj X)) :
    (etalePoints L h x).fiber.obj (openEtaleObject X U) ≃
      (underlyingTopologyPoint.{u, v, uL} X (pointProjection L X x)).fiber.obj U where
  toFun p := ⟨⟨projection_mem_of_openEtale_fiber L h x U p⟩⟩
  invFun p := by
    have hp : pointProjection L X x ∈
        Set.range (localizedSpaceFunctor.map (openEtaleObject X U).hom) :=
      ⟨⟨pointProjection L X x, p.down.down⟩, domainι_apply _ _⟩
    exact ULift.up ((etalePointLifting_of_hausdorff L h x (openEtaleObject X U) hp).some)
  left_inv p := (subsingleton_openEtale_fiber L h x U).allEq _ _
  right_inv p := by
    apply ULift.ext
    exact Subsingleton.elim _ _

/-- The ordinary fiber identification respects every ordinary restriction. -/
theorem openEtaleFiberEquiv_map
    (x : (localizedFieldPointFunctor L).obj X)
    {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V)
    (p : (etalePoints L h x).fiber.obj (openEtaleObject X U)) :
    openEtaleFiberEquiv L h x V ((etalePoints L h x).fiber.map (openEtaleMap X f) p) =
      (underlyingTopologyPoint.{u, v, uL} X (pointProjection L X x)).fiber.map f
        (openEtaleFiberEquiv L h x U p) := by
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- The ordinary point family indexed by the original field-valued points,
with each point placed at its actual projection. -/
def ordinaryFieldPointFamily (x : (localizedFieldPointFunctor L).obj X) :
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)).Point.{max u (v + 1) uL} :=
  underlyingTopologyPoint.{u, v, uL} X (pointProjection L X x)

variable {R : Type (max u (v + 1) uL)} [CommRing R]

private local instance {S : Type w} [CommRing S] :
    HasProducts.{wI} (ModuleCat.{max wI w} S) := by
  let := hasLimitsOfSizeShrink.{wI, wI, w, w} (ModuleCat.{max wI w} S)
  infer_instance

variable (M : (localizedFieldPointFunctor L).obj X → ModuleCat.{max u (v + 1) uL} R)

/-- Actual point-product sections over an ordinary open have the ordinary
point-product coordinates, through the proved equivalence of their fibers. -/
def openPointProductCoordinates (U : Opens (localizedSpaceFunctor.obj X)) :
    (productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M).obj.obj (op (openEtaleObject X U)) ≃ₗ[R]
      (productSheaf (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) (ModuleCat.{max u (v + 1) uL} R) M).obj.obj (op U) :=
  (sectionCoordinates.{max u v uL, max u (v + 1) uL} (etalePoints L h) M (openEtaleObject X U)).trans
    ((LinearEquiv.piCongrRight fun x =>
      LinearEquiv.funCongrLeft R (M x) (openEtaleFiberEquiv L h x U).symm).trans
        (sectionCoordinates.{max u v uL, max u (v + 1) uL} (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) M U).symm)

/-- The ordinary coordinate is the original analytic coordinate at the
unique lift represented by that ordinary point. -/
theorem openPointProductCoordinates_apply
    (U : Opens (localizedSpaceFunctor.obj X))
    (s : (productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M).obj.obj (op (openEtaleObject X U)))
    (x : (localizedFieldPointFunctor L).obj X)
    (p : (ordinaryFieldPointFamily.{u, v, uL} L (X := X) x).fiber.obj U) :
    sectionCoordinates.{max u v uL, max u (v + 1) uL} (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) M U
        (openPointProductCoordinates L h M U s) x p =
      sectionCoordinates.{max u v uL, max u (v + 1) uL} (etalePoints L h) M (openEtaleObject X U) s x
        ((openEtaleFiberEquiv L h x U).symm p) := by
  change (sectionCoordinates.{max u v uL, max u (v + 1) uL} (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) M U
    ((sectionCoordinates.{max u v uL, max u (v + 1) uL} (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) M U).symm _)) x p = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The point-product coordinate identification commutes with actual
restrictions to smaller ordinary opens. -/
theorem openPointProductCoordinates_restrict
    {U V : Opens (localizedSpaceFunctor.obj X)} (f : U ⟶ V)
    (s : (productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M).obj.obj (op (openEtaleObject X V))) :
    openPointProductCoordinates L h M U
        ((productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M).obj.map (openEtaleMap X f).op s) =
      (productSheaf (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) (ModuleCat.{max u (v + 1) uL} R) M).obj.map f.op
        (openPointProductCoordinates L h M V s) := by
  apply (sectionCoordinates.{max u v uL, max u (v + 1) uL} (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) M U).injective
  funext x p
  rw [openPointProductCoordinates_apply, sectionCoordinates_restrict.{max u v uL, max u (v + 1) uL},
    sectionCoordinates_restrict.{max u v uL, max u (v + 1) uL}, openPointProductCoordinates_apply]
  apply congrArg (fun q =>
    sectionCoordinates.{max u v uL, max u (v + 1) uL} (etalePoints L h) M (openEtaleObject X V) s x q)
  apply (openEtaleFiberEquiv L h x V).injective
  rw [openEtaleFiberEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The actual raw étale point product on ordinary opens is the ordinary
product of skyscrapers at the projected points. -/
def openPointProductPresheafIso :
    ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
      (productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M)).obj ≅
        (productSheaf (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) (ModuleCat.{max u (v + 1) uL} R) M).obj :=
  NatIso.ofComponents (fun U => (openPointProductCoordinates L h M U.unop).toModuleIso) (by
    intro U V f
    ext s
    exact openPointProductCoordinates_restrict L h M f.unop s)

/-- The ordinary-open point-product comparison is an isomorphism of actual sheaves. -/
def openPointProductSheafIso :
    (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
      (productSheaf (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R) M) ≅
        productSheaf (ordinaryFieldPointFamily.{u, v, uL} L (X := X)) (ModuleCat.{max u (v + 1) uL} R) M :=
  ObjectProperty.isoMk _ (openPointProductPresheafIso L h M)

end Langlands.Sheaf.Equivariant.Analytic
