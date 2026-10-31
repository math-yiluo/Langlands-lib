import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverGluingTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinementTransport
import Mathlib.CategoryTheory.Types.Basic

/-! # Compatible continuous families as natural descent data -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A B : PresentedAffinoidAlgebra K} {V : Domain K A}
variable {Y : Type v} [TopologicalSpace Y]

namespace Refinement

variable {c d : FiniteCover V}

/-- Assembly on the finer actual spectra is assembly on the coarser spectra
precomposed with the actual refinement spectrum map. -/
theorem spectrumFamilyMap_pullbackFamily (r : Refinement d c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.spectrumFamilyMap (r.pullbackFamily g) =
      (c.spectrumFamilyMap g).comp r.spectrumMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (g (r.index x.1))
    ((r.map x.1).spectrumToLocus_naturality x.2).symm

/-- Transport and actual refinement restriction commute for every family,
before imposing overlap agreement. -/
theorem transportBaseFamily_pullbackFamily (r : Refinement d c)
    (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.transportBaseFamily e (r.pullbackFamily g) =
      (r.transportBase e).pullbackFamily (c.transportBaseFamily e g) := by
  funext j
  apply ContinuousMap.ext
  intro x
  exact congrArg (g (r.index j))
    (Domain.transportBaseLocusHomeomorph_naturality e (r.map j) x).symm

/-- The constructed compatible-family equivalences commute with refinement
pullback, with every chosen component index retained. -/
theorem transportBaseFamilyEquiv_pullback (r : Refinement d c)
    (e : BoundedAlgEquiv K A B) (g : CompatibleFamily c Y) :
    d.transportBaseFamilyEquiv e (r.pullback g) =
      (r.transportBase e).pullback (c.transportBaseFamilyEquiv e g) := by
  apply Subtype.ext
  exact r.transportBaseFamily_pullbackFamily e g.val

/-- The entire square commutes as an equality of constructed equivalences. -/
theorem pullbackEquiv_trans_transportBaseFamilyEquiv (r : Refinement d c)
    (e : BoundedAlgEquiv K A B) :
    (r.pullbackEquiv (Y := Y)).trans (d.transportBaseFamilyEquiv e) =
      (c.transportBaseFamilyEquiv e).trans
        ((r.transportBase e).pullbackEquiv (Y := Y)) := by
  apply Equiv.ext
  intro g
  exact r.transportBaseFamilyEquiv_pullback e g

/-- Descent from the finer family and subsequent base transport agree with
base transport followed by descent through the transported refinement. -/
theorem transportBaseFamilyEquiv_pullbackEquiv_symm (r : Refinement d c)
    (e : BoundedAlgEquiv K A B) (g : CompatibleFamily d Y) :
    c.transportBaseFamilyEquiv e ((r.pullbackEquiv (Y := Y)).symm g) =
      ((r.transportBase e).pullbackEquiv (Y := Y)).symm
        (d.transportBaseFamilyEquiv e g) := by
  apply ((r.transportBase e).pullbackEquiv (Y := Y)).injective
  change (r.transportBase e).pullback
      (c.transportBaseFamilyEquiv e ((r.pullbackEquiv (Y := Y)).symm g)) =
    (r.transportBase e).pullbackEquiv
      (((r.transportBase e).pullbackEquiv (Y := Y)).symm
        (d.transportBaseFamilyEquiv e g))
  rw [← r.transportBaseFamilyEquiv_pullback]
  change d.transportBaseFamilyEquiv e
      ((r.pullbackEquiv (Y := Y)) ((r.pullbackEquiv (Y := Y)).symm g)) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The commuting refinement/transport square also agrees on the retained
disjoint unions of actual quotient spectra. -/
theorem transportBase_spectrumFamilyMap_pullbackFamily (r : Refinement d c)
    (e : BoundedAlgEquiv K A B)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (d.transportBase e).spectrumFamilyMap
        ((r.transportBase e).pullbackFamily (c.transportBaseFamily e g)) =
      (c.spectrumFamilyMap g).comp r.spectrumMap := by
  rw [← r.transportBaseFamily_pullbackFamily,
    d.transportBaseFamily_spectrumFamilyMap, r.spectrumFamilyMap_pullbackFamily]

end Refinement

/-- Compatible continuous families form a presheaf on the actual chosen-index
finite full-domain cover category. -/
def compatibleFamilyPresheaf (V : Domain K A) (Y : Type v) [TopologicalSpace Y] :
    (FiniteCover V)ᵒᵖ ⥤ Type (max u v) where
  obj c := CompatibleFamily c.unop Y
  map r := TypeCat.ofHom (Refinement.pullback r.unop)
  map_id c := by
    apply ConcreteCategory.hom_ext
    intro g
    exact Refinement.pullback_id g
  map_comp r s := by
    apply ConcreteCategory.hom_ext
    intro g
    exact Refinement.pullback_comp s.unop r.unop g

/-- The actual quotient-lift gluing equivalences are natural in all
chosen cover refinements. -/
def gluingNatIso (V : Domain K A) (Y : Type v) [TopologicalSpace Y] :
    (Functor.const (FiniteCover V)ᵒᵖ).obj C(V.locus, Y) ≅
      compatibleFamilyPresheaf V Y :=
  NatIso.ofComponents (fun c => (c.unop.gluingEquiv (Y := Y)).toIso)
    (by
      intro c d r
      ext f
      exact (r.unop.pullback_gluingEquiv f).symm)

/-- Bounded ambient equivalences induce a natural isomorphism of compatible
continuous family presheaves, along the actual cover transport functor. -/
def transportBaseFamilyNatIso (e : BoundedAlgEquiv K A B) (V : Domain K A)
    (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf V Y ≅
      (transportBaseFunctor e).op ⋙
        compatibleFamilyPresheaf (Domain.transportBase e V) Y :=
  NatIso.ofComponents (fun c => (c.unop.transportBaseFamilyEquiv e).toIso)
    (by
      intro c d r
      ext g
      exact r.unop.transportBaseFamilyEquiv_pullback e g)

@[simp] theorem transportBaseFamilyNatIso_hom_app
    (e : BoundedAlgEquiv K A B) (c : FiniteCover V) (g : CompatibleFamily c Y) :
    (transportBaseFamilyNatIso e V Y).hom.app (Opposite.op c) g =
      c.transportBaseFamilyEquiv e g := rfl

@[simp] theorem transportBaseFamilyNatIso_inv_app
    (e : BoundedAlgEquiv K A B) (c : FiniteCover V)
    (g : CompatibleFamily (c.transportBase e) Y) :
    (transportBaseFamilyNatIso e V Y).inv.app (Opposite.op c) g =
      (c.transportBaseFamilyEquiv e).symm g := rfl

/-- The categorical transport component commutes with the actual restriction
and quotient-gluing identification of global continuous maps. -/
theorem transportBaseFamilyNatIso_gluing
    (e : BoundedAlgEquiv K A B) (c : FiniteCover V) (f : C(V.locus, Y)) :
    (transportBaseFamilyNatIso e V Y).hom.app (Opposite.op c)
        ((gluingNatIso V Y).hom.app (Opposite.op c) f) =
      (gluingNatIso (Domain.transportBase e V) Y).hom.app
        (Opposite.op (c.transportBase e))
        (f.comp (Domain.transportBaseLocusHomeomorph e V :
          C((Domain.transportBase e V).locus, V.locus))) :=
  c.transportBaseFamilyEquiv_gluingEquiv e f

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
