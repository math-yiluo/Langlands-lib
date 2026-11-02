import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestrictionSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartAlgebraSheaf

/-! # Actions on the actual algebra sheaf and its whole-chart sections -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Opposite DomainAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A) (H : OpenSubgroup G)

/-- Each bounded section operator is a morphism of the actual restricted sheaf. -/
def spectralInvariantSheafOperator (g : H) :
    (spectralInvariantSheafInclusion ρ H (CommAlgCat K)).obj (algebraSheaf K A) ⟶
      (spectralInvariantSheafInclusion ρ H (CommAlgCat K)).obj (algebraSheaf K A) where
  hom := {
    app d := CommAlgCat.ofHom
      ((spectralInvariantSectionAction ρ H d.unop).obj.ρ g).toAlgHom
    naturality d e f := by
      ext a
      exact congrArg
        (fun h : BoundedAlgHom K d.unop.obj.algebra e.unop.obj.algebra => h a)
        (spectralInvariantSectionAction_restriction ρ H f.unop g).symm }

/-- The original section operators act on the whole ordinary algebra sheaf. -/
def spectralInvariantSheafAction :
    Action (Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H) (CommAlgCat K)) H where
  V := (spectralInvariantSheafInclusion ρ H (CommAlgCat K)).obj (algebraSheaf K A)
  ρ := {
    toFun := spectralInvariantSheafOperator ρ H
    map_one' := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext d
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg
        (fun h : BoundedAlgHom K d.unop.obj.algebra d.unop.obj.algebra => h a)
        (spectralInvariantSectionAction ρ H d.unop).obj.ρ.map_one
    map_mul' g h := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext d
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg
        (fun f : BoundedAlgHom K d.unop.obj.algebra d.unop.obj.algebra => f a)
        ((spectralInvariantSectionAction ρ H d.unop).obj.ρ.map_mul g h) }

/-- The sheaf action retains the entire original restricted algebra presheaf. -/
@[simp]
theorem spectralInvariantSheafAction_presheaf :
    (spectralInvariantSheafAction ρ H).V.obj =
      (spectralInvariantChartInclusion ρ H).op ⋙ algebraPresheaf K A := rfl

@[simp]
theorem spectralInvariantSheafAction_apply
    (g : H) (d : SpectralInvariantChart ρ H) (a : d.obj.algebra) :
    (((spectralInvariantSheafAction ρ H).ρ g).hom.app (op d)).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom a := rfl

/-- The group action gives actual sheaf automorphisms, including their inverses. -/
def spectralInvariantSheafAutomorphisms :
    H →* Aut (spectralInvariantSheafAction ρ H).V :=
  (spectralInvariantSheafAction ρ H).ρAut

@[simp]
theorem spectralInvariantSheafAutomorphisms_hom_apply
    (g : H) (d : SpectralInvariantChart ρ H) (a : d.obj.algebra) :
    (((spectralInvariantSheafAutomorphisms ρ H g).hom).hom.app (op d)).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom a := rfl

@[simp]
theorem spectralInvariantSheafAutomorphisms_inv_apply
    (g : H) (d : SpectralInvariantChart ρ H) (a : d.obj.algebra) :
    (((spectralInvariantSheafAutomorphisms ρ H g).inv).hom.app (op d)).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g⁻¹).toAlgHom a := rfl

/-- Evaluation of the sheaf action gives the action on each original quotient. -/
def spectralInvariantSheafSectionAction (d : SpectralInvariantChart ρ H) :
    Action (CommAlgCat K) H :=
  (((sheafSections (SpectralInvariantChart.finiteRationalTopology ρ H)
      (CommAlgCat K)).obj (op d)).mapAction H).obj (spectralInvariantSheafAction ρ H)

@[simp]
theorem spectralInvariantSheafSectionAction_algebra (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSheafSectionAction ρ H d).V = CommAlgCat.of K d.obj.algebra := rfl

@[simp]
theorem spectralInvariantSheafSectionAction_apply
    (d : SpectralInvariantChart ρ H) (g : H) (a : d.obj.algebra) :
    ((spectralInvariantSheafSectionAction ρ H d).ρ g).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom a := rfl

/-- Naturality of the actual sheaf operators makes every restriction equivariant. -/
def spectralInvariantSheafSectionRestriction {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) :
    spectralInvariantSheafSectionAction ρ H e ⟶ spectralInvariantSheafSectionAction ρ H d where
  hom := (spectralInvariantSheafAction ρ H).V.obj.map f.op
  comm g := (((spectralInvariantSheafAction ρ H).ρ g).hom.naturality f.op).symm

@[simp]
theorem spectralInvariantSheafSectionRestriction_apply
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) (a : e.obj.algebra) :
    (spectralInvariantSheafSectionRestriction ρ H f).hom a = f.hom.restriction a := rfl

/-- Forget the bounds of the ambient action restricted to the same subgroup. -/
def spectralInvariantBaseAlgebraAction : Action (CommAlgCat K) H where
  V := CommAlgCat.of K A
  ρ := {
    toFun g := CommAlgCat.ofHom ((spectralInvariantBaseAction ρ H).obj.ρ g).toAlgHom
    map_one' := by
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg (fun f : BoundedAlgHom K A A => f a)
        (spectralInvariantBaseAction ρ H).obj.ρ.map_one
    map_mul' g h := by
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg (fun f : BoundedAlgHom K A A => f a)
        ((spectralInvariantBaseAction ρ H).obj.ρ.map_mul g h) }

@[simp]
theorem spectralInvariantBaseAlgebraAction_apply (g : H) (a : A) :
    ((spectralInvariantBaseAlgebraAction ρ H).ρ g).hom a =
      (ρ.toMonoidHom (g : G)).hom.toAlgHom a := rfl

/-- The constructed whole-section identification intertwines the original action. -/
def spectralInvariantWholeSectionIso :
    spectralInvariantBaseAlgebraAction ρ H ≅
      spectralInvariantSheafSectionAction ρ H (SpectralInvariantChart.whole ρ H) :=
  Action.mkIso (wholeSectionIso K A) (fun g => by
    ext a
    exact (spectralInvariantSectionAction_baseMap ρ H
      (SpectralInvariantChart.whole ρ H) g a).symm)

@[simp]
theorem spectralInvariantWholeSectionIso_hom_apply (a : A) :
    (spectralInvariantWholeSectionIso ρ H).hom.hom a = (whole K A).baseMap a := rfl

@[simp]
theorem spectralInvariantWholeSectionIso_inv_apply (a : (whole K A).algebra) :
    (spectralInvariantWholeSectionIso ρ H).inv.hom a = wholeRetraction K A a := rfl

/-- The original structural map is whole-section identification followed by restriction. -/
def spectralInvariantSheafBaseMap (d : SpectralInvariantChart ρ H) :
    spectralInvariantBaseAlgebraAction ρ H ⟶ spectralInvariantSheafSectionAction ρ H d :=
  (spectralInvariantWholeSectionIso ρ H).hom ≫
    spectralInvariantSheafSectionRestriction ρ H (SpectralInvariantChart.toWhole ρ H d)

@[simp]
theorem spectralInvariantSheafBaseMap_apply (d : SpectralInvariantChart ρ H) (a : A) :
    (spectralInvariantSheafBaseMap ρ H d).hom a = d.obj.baseMap a :=
  wholeSectionIso_restrict K A d.obj a

/-- Equality of full algebra homomorphisms retains the original structural map. -/
@[simp]
theorem spectralInvariantSheafBaseMap_hom (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSheafBaseMap ρ H d).hom = CommAlgCat.ofHom d.obj.baseMap.toAlgHom := by
  apply CommAlgCat.hom_ext
  ext a
  exact spectralInvariantSheafBaseMap_apply ρ H d a

/-- Structural maps commute with every original invariant-chart restriction. -/
theorem spectralInvariantSheafBaseMap_naturality
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) :
    spectralInvariantSheafBaseMap ρ H e ≫ spectralInvariantSheafSectionRestriction ρ H f =
      spectralInvariantSheafBaseMap ρ H d := by
  apply Action.Hom.ext
  apply CommAlgCat.hom_ext
  ext a
  exact (congrArg f.hom.restriction
    (spectralInvariantSheafBaseMap_apply ρ H e a)).trans
    ((congrArg (fun h : BoundedAlgHom K A d.obj.algebra => h a)
      f.hom.comp_baseMap).trans
      (spectralInvariantSheafBaseMap_apply ρ H d a).symm)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
