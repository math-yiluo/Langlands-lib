import Langlands.GroupScheme.RelativeLevi.DynamicStatement
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport

/-! # Transport and construction of relative unipotent radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {P P' U V : GroupScheme S} {r : U ⟶ P}

/-- Replacing the source of a relative radical by an isomorphic group scheme
preserves the relative radical predicate. -/
theorem IsRelativeUnipotentRadical.precomp_iso
    (hr : IsRelativeUnipotentRadical r) (e : V ≅ U) :
    IsRelativeUnipotentRadical (e.hom ≫ r) := by
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  let : Smooth U.X.hom := hr.smooth
  refine ⟨(IsClosedSubgroup.of_iso e).comp hr.isClosedSubgroup, ?_, ?_, ?_⟩
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · rw [SubgroupFunctor.range_iso_comp]
    exact hr.isNormal
  · intro s
    change IsUnipotentRadical
      ((GroupScheme.baseChange (geometricPoint S s)).map (e.hom ≫ r))
    rw [Functor.map_comp]
    exact (hr.geometricFiber s).precomp_iso
      ((GroupScheme.baseChange (geometricPoint S s)).mapIso e)

/-- Relative radicals transport through isomorphisms of the ambient group. -/
theorem IsRelativeUnipotentRadical.comp_iso
    (hr : IsRelativeUnipotentRadical r) (e : P ≅ P') :
    IsRelativeUnipotentRadical (r ≫ e.hom) := by
  refine ⟨hr.isClosedSubgroup.comp_iso e, hr.smooth, ?_, ?_⟩
  · rw [SubgroupFunctor.range_comp_iso]
    exact hr.isNormal.comap e.inv
  · intro s
    change IsUnipotentRadical
      ((GroupScheme.baseChange (geometricPoint S s)).map (r ≫ e.hom))
    rw [Functor.map_comp]
    exact (hr.geometricFiber s).comp_iso
      ((GroupScheme.baseChange (geometricPoint S s)).mapIso e)

/-- A closed representative of the same all-test subgroup as a relative
radical inherits the whole relative radical predicate. -/
theorem IsRelativeUnipotentRadical.of_range_eq
    (hr : IsRelativeUnipotentRadical r) {r' : V ⟶ P}
    (hr' : IsClosedSubgroup r')
    (heq : SubgroupFunctor.range r' = SubgroupFunctor.range r) :
    IsRelativeUnipotentRadical r' := by
  let e := hr'.sourceIsoOfRangeEq hr.isClosedSubgroup heq
  have he : e.hom ≫ r = r' :=
    hr'.sourceIsoOfRangeEq_hom_comp hr.isClosedSubgroup heq
  rw [← he]
  exact hr.precomp_iso e

namespace RelativeLevi

/-- Given the dynamic relative Levi theorem, construct an actual relative
unipotent radical of any represented dynamic parabolic. -/
def dynamicUnipotentRadical
    (hdynamic : DynamicRelativeLeviStatement.{u})
    (G P : GroupScheme S) (χ : (Gm S).toGrp ⟶ G) (iP : P ⟶ G)
    (hG : IsReductive G) (hP : (Dynamic.parabolic χ).IsRepresentedBy iP) :
    Σ U : GroupScheme S, {r : U ⟶ P // IsRelativeUnipotentRadical r} := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hex := dynamicBaseRepresentability S G χ
  choose U iU hUc hUlfp hUr using hex.2.1
  choose Z iZ hZc hZlfp hZr using hex.2.2
  have hle : SubgroupFunctor.range iU ≤ Dynamic.parabolic χ := by
    rw [hUr.2]
    exact Dynamic.unipotent_le_parabolic χ
  let r : U ⟶ P := hP.factorHom iU hle
  have hfac : r ≫ iP = iU := hP.factorHom_comp iU hle
  exact ⟨U, r, (hdynamic S G P U Z χ iP iU iZ hG hP hUr hZr).2.1 r hfac⟩

end RelativeLevi

end Langlands.GroupScheme
