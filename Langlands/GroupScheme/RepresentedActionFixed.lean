import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Fixed subgroups of represented invariant subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

section Equivariant

variable {S : Scheme.{u}} {H G C K Z : GroupScheme S}
    (a : AutomorphicAction H G) (b : AutomorphicAction H C)
    (i : C ⟶ G) [Mono i.hom.hom]
    (hab : ∀ (T : Over S) (h : T ⟶ H.X) (c : T ⟶ C.X),
      b.act h c ≫ i.hom.hom = a.act h (c ≫ i.hom.hom))

include hab

/-- An equivariant monomorphism reflects and preserves all-refinement fixedness. -/
theorem isFixed_iff_of_equivariant_mono {T : Over S} (c : T ⟶ C.X) :
    b.IsFixed c ↔ a.IsFixed (c ≫ i.hom.hom) := by
  constructor
  · intro hc V q h
    have e := congrArg (fun f : V ⟶ C.X => f ≫ i.hom.hom) (hc V q h)
    simpa only [hab, Category.assoc] using e
  · intro hc V q h
    apply (cancel_mono i.hom.hom).1
    rw [hab, Category.assoc, hc V q h]

/-- The all-test fixed functor of an equivariantly included subgroup is a preimage. -/
theorem fixedSubgroup_eq_comap_of_equivariant_mono :
    b.fixedSubgroup = a.fixedSubgroup.comap i := by
  ext T c
  exact isFixed_iff_of_equivariant_mono a b i hab c

end Equivariant

variable {S : Scheme.{u}} {H G C K Z : GroupScheme S}
    (a : AutomorphicAction H G) (i : C ⟶ G)
    {F : SubgroupFunctor G} (hi : F.IsRepresentedBy i) (hF : a.IsStable F)

/-- Fixed points of the action on a represented stable subgroup are exactly the
points whose images are fixed in the ambient group. -/
theorem onRepresentedSubgroup_fixedSubgroup_eq_comap :
    (a.onRepresentedSubgroup i hi hF).fixedSubgroup = a.fixedSubgroup.comap i := by
  let : Mono i.hom.hom := hi.1
  exact fixedSubgroup_eq_comap_of_equivariant_mono a
    (a.onRepresentedSubgroup i hi hF) i
    (fun _ h c => a.onRepresentedSubgroup_act_comp i hi hF h c)

/-- The same comparison holds after restricting the acting group along any
homomorphism. -/
theorem onRepresentedSubgroup_restrict_fixedSubgroup_eq_comap (j : K ⟶ H) :
    ((a.onRepresentedSubgroup i hi hF).restrict j).fixedSubgroup =
      (a.restrict j).fixedSubgroup.comap i := by
  let : Mono i.hom.hom := hi.1
  apply fixedSubgroup_eq_comap_of_equivariant_mono
  intro T h c
  simp only [restrict_act, onRepresentedSubgroup_act_comp]

/-- A restriction preserving the ambient fixed functor also preserves the fixed
functor on every represented invariant subgroup. -/
theorem onRepresentedSubgroup_restrict_fixedSubgroup_eq (j : K ⟶ H)
    (hj : (a.restrict j).fixedSubgroup = a.fixedSubgroup) :
    ((a.onRepresentedSubgroup i hi hF).restrict j).fixedSubgroup =
      (a.onRepresentedSubgroup i hi hF).fixedSubgroup := by
  rw [onRepresentedSubgroup_restrict_fixedSubgroup_eq_comap,
    onRepresentedSubgroup_fixedSubgroup_eq_comap, hj]

variable (hcontains : a.fixedSubgroup ≤ F)
    (z : Z ⟶ G) (hz : a.fixedSubgroup.IsRepresentedBy z)

/-- Factor an ambient fixed representative into a stable represented subgroup
containing all fixed points. -/
def representedFixedFactor : Z ⟶ C :=
  hi.factorHom z (by rw [hz.2]; exact hcontains)

theorem representedFixedFactor_comp :
    a.representedFixedFactor i hi hcontains z hz ≫ i = z :=
  hi.factorHom_comp z _

/-- The factor of any ambient fixed representative represents the fixed functor
of the action on the stable subgroup. -/
theorem onRepresentedSubgroup_isRepresentedBy_fixedFactor :
    (a.onRepresentedSubgroup i hi hF).fixedSubgroup.IsRepresentedBy
      (a.representedFixedFactor i hi hcontains z hz) := by
  let f := a.representedFixedFactor i hi hcontains z hz
  have hcomp : f.hom.hom ≫ i.hom.hom = z.hom.hom :=
    congrArg (fun q => q.hom.hom)
      (a.representedFixedFactor_comp i hi hcontains z hz)
  let : Mono z.hom.hom := hz.1
  let : Mono i.hom.hom := hi.1
  rw [onRepresentedSubgroup_fixedSubgroup_eq_comap]
  refine ⟨mono_of_mono_fac hcomp, ?_⟩
  ext T c
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, ← hz.2,
    SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Category.assoc, hcomp]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (cancel_mono i.hom.hom).1
    rw [Category.assoc, hcomp]
    exact hx

/-- Closed ambient fixed representatives give closed representatives inside the
stable subgroup. -/
theorem isClosedSubgroup_representedFixedFactor
    (hic : IsClosedSubgroup i) (hzc : IsClosedSubgroup z) :
    IsClosedSubgroup (a.representedFixedFactor i hi hcontains z hz) :=
  IsClosedSubgroup.of_comp hic (by
    rw [representedFixedFactor_comp]
    exact hzc)

end Langlands.GroupScheme.AutomorphicAction
