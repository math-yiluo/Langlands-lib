import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantRestrictionSite
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartAlgebraSheaf
import Mathlib.CategoryTheory.Action.Limits

/-! # Actual algebra sheaves with actions on the finite invariant rational site -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Opposite DomainAutomorphism

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A) (H : OpenSubgroup G)

/-- Restrict the actual, proved rational algebra sheaf to the invariant site. -/
def spectralInvariantAlgebraSheaf :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H) (CommAlgCat K) :=
  (spectralInvariantSheafInclusion ρ H (CommAlgCat K)).obj (algebraSheaf K A)

/-- Restriction retains the complete presheaf of original quotient algebras. -/
@[simp]
theorem spectralInvariantAlgebraSheaf_presheaf :
    (spectralInvariantAlgebraSheaf ρ H).obj =
      (spectralInvariantChartInclusion ρ H).op ⋙ algebraPresheaf K A := rfl

/-- The bounded section operators act on the original commutative K-algebra. -/
def spectralInvariantAlgebraAction (d : SpectralInvariantChart ρ H) :
    Action (CommAlgCat K) H where
  V := CommAlgCat.of K d.obj.algebra
  ρ := {
    toFun g := CommAlgCat.ofHom ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom
    map_one' := by
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg (fun f : BoundedAlgHom K d.obj.algebra d.obj.algebra => f a)
        (spectralInvariantSectionAction ρ H d).obj.ρ.map_one
    map_mul' g h := by
      apply CommAlgCat.hom_ext
      ext a
      exact congrArg (fun f : BoundedAlgHom K d.obj.algebra d.obj.algebra => f a)
        ((spectralInvariantSectionAction ρ H d).obj.ρ.map_mul g h) }

@[simp]
theorem spectralInvariantAlgebraAction_apply (d : SpectralInvariantChart ρ H)
    (g : H) (a : d.obj.algebra) :
    ((spectralInvariantAlgebraAction ρ H d).ρ g).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom a := rfl

/-- All original rational restrictions are equivariant algebra homomorphisms. -/
def spectralInvariantAlgebraPresheaf :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ Action (CommAlgCat K) H where
  obj d := spectralInvariantAlgebraAction ρ H d.unop
  map {d e} f := {
    hom := CommAlgCat.ofHom f.unop.hom.restriction.toAlgHom
    comm g := by
      ext a
      exact congrArg
        (fun h : BoundedAlgHom K d.unop.obj.algebra e.unop.obj.algebra => h a)
        (spectralInvariantSectionAction_restriction ρ H f.unop g) }
  map_id _ := by
    apply Action.Hom.ext
    rfl
  map_comp _ _ := by
    apply Action.Hom.ext
    rfl

/-- Forgetting the action retains the entire actual algebra presheaf. -/
@[simp]
theorem spectralInvariantAlgebraPresheaf_forget :
    spectralInvariantAlgebraPresheaf ρ H ⋙ Action.forget (CommAlgCat K) H =
      (spectralInvariantAlgebraSheaf ρ H).obj := rfl

/-- Sheafness lifts along reflection of limits; no new descent premise is used. -/
theorem spectralInvariantAlgebraPresheaf_isSheaf :
    Presheaf.IsSheaf (SpectralInvariantChart.finiteRationalTopology ρ H)
      (spectralInvariantAlgebraPresheaf ρ H) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (Action.forget (CommAlgCat K) H)
  exact (spectralInvariantAlgebraSheaf ρ H).property

/-- The actual quotient-algebra sheaf with the constructed common-subgroup action. -/
def spectralInvariantEquivariantAlgebraSheaf :
    Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H) (Action (CommAlgCat K) H) :=
  ⟨spectralInvariantAlgebraPresheaf ρ H, spectralInvariantAlgebraPresheaf_isSheaf ρ H⟩

/-- The whole forgotten presheaf is the restricted ordinary algebra sheaf. -/
@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_forget :
    (spectralInvariantEquivariantAlgebraSheaf ρ H).obj ⋙ Action.forget (CommAlgCat K) H =
      (spectralInvariantAlgebraSheaf ρ H).obj := rfl

@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_obj (d : SpectralInvariantChart ρ H) :
    ((spectralInvariantEquivariantAlgebraSheaf ρ H).obj.obj (op d)).V =
      CommAlgCat.of K d.obj.algebra := rfl

@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_action_apply
    (d : SpectralInvariantChart ρ H) (g : H) (a : d.obj.algebra) :
    (((spectralInvariantEquivariantAlgebraSheaf ρ H).obj.obj (op d)).ρ g).hom a =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom a := rfl

@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_map_apply
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) (a : e.obj.algebra) :
    ((spectralInvariantEquivariantAlgebraSheaf ρ H).obj.map f.op).hom a =
      f.hom.restriction a := rfl

/-- The original bounded structural map intertwines the ambient and section actions. -/
@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_baseMap
    (d : SpectralInvariantChart ρ H) (g : H) (a : A) :
    (((spectralInvariantEquivariantAlgebraSheaf ρ H).obj.obj (op d)).ρ g).hom
        (d.obj.baseMap a) =
      d.obj.baseMap ((ρ.toMonoidHom (g : G)).hom.toAlgHom a) :=
  spectralInvariantSectionAction_baseMap ρ H d g a

/-- The stored restriction preserves every original structural section. -/
@[simp]
theorem spectralInvariantEquivariantAlgebraSheaf_restrict_baseMap
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) (a : A) :
    ((spectralInvariantEquivariantAlgebraSheaf ρ H).obj.map f.op).hom (e.obj.baseMap a) =
      d.obj.baseMap a :=
  congrArg (fun h : BoundedAlgHom K A d.obj.algebra => h a) f.hom.comp_baseMap

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
