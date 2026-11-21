import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Factorization of a restricted conjugate subgroup family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S W : Scheme.{u}} {T M : Over S}
variable {G D Q L : GroupScheme S} {K : GroupScheme M.left}

/-- An identification of a restricted family source with the corresponding pullback
of `D`, and a lift of its inclusion through the iterated base change of `m`. -/
structure RestrictedFamilyFactorization (D : GroupScheme S) (m : Q ⟶ L)
    (j : K ⟶ (baseChange M.hom).obj L) (b : T ⟶ M) (s : W ⟶ T.left) where
  sourceIso : (baseChange s).obj ((baseChange b.left).obj K) ≅
    (baseChange s).obj ((baseChange T.hom).obj D)
  factor : (baseChange s).obj ((baseChange b.left).obj K) ⟶
    (baseChange s).obj ((baseChange T.hom).obj Q)
  fac : factor ≫ (baseChange s).map ((baseChange T.hom).map m) =
    (baseChange s).map (familyHom j b)

/-- A family that is conjugate by the image of a point after restriction factors
there through the intermediate group. The returned source iso compares the actual
iterated pullbacks, and the factor is the corresponding conjugated inclusion. -/
def restrictedFamilyFactorization (q : G ⟶ Q) (d : D ⟶ Q) (m : Q ⟶ L)
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hd : IsClosedSubgroup (d ≫ m)) (f : G.X ⟶ M)
    (hf : evaluate j f = range (conjugateFamily (d ≫ m) (q ≫ m).hom.hom))
    (b : T ⟶ M) (s : W ⟶ T.left) (g : Over.mk (s ≫ T.hom) ⟶ G.X)
    (hg : g ≫ f = (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T) ≫ b) :
    RestrictedFamilyFactorization D m j b s := by
  let r := s ≫ T.hom
  let a : Over.mk r ⟶ T := Over.homMk s rfl
  let e := conjugateFamily (d ≫ m) (g ≫ (q ≫ m).hom.hom)
  have hEq : evaluate j (a ≫ b) = range e := by
    rw [← hg, ← evaluate_comp j f g]
    exact (evaluate_eq_of_range_eq (familyHom j f) _ hf g).trans
      (evaluate_conjugateFamily (d ≫ m) (q ≫ m).hom.hom g)
  have hclosed₁ : IsClosedImmersion (familyHom j (a ≫ b)).hom.hom.left :=
    isClosedSubgroup_familyHom j hj _
  have hclosed₂ : IsClosedImmersion e.hom.hom.left :=
    isClosedSubgroup_conjugatePullback _ (d ≫ m) hd _
  let : Mono (familyHom j (a ≫ b)).hom.hom.left :=
    ((IsClosedImmersion.iff_isFinite_and_mono (f := _)).mp hclosed₁).2
  let : Mono e.hom.hom.left := ((IsClosedImmersion.iff_isFinite_and_mono (f := _)).mp hclosed₂).2
  let h₁ : (range e).IsRepresentedBy (familyHom j (a ≫ b)) :=
    ⟨Over.mono_of_mono_left _, hEq⟩
  let h₂ : (range e).IsRepresentedBy e := ⟨Over.mono_of_mono_left _, rfl⟩
  let σ := h₁.isoOfIsRepresentedBy h₂
  have hσ : σ.hom ≫ e = familyHom j (a ≫ b) := h₁.isoOfIsRepresentedBy_hom_comp h₂
  let x := (baseChangeBasePointsEquiv r Q).symm (g ≫ q.hom.hom)
  let c := (baseChange r).map d ≫ (((baseChange r).obj Q).innerIso x).hom
  have hx : x ≫ ((baseChange r).map m).hom.hom =
      (baseChangeBasePointsEquiv r L).symm (g ≫ (q ≫ m).hom.hom) := by
    apply (baseChangeBasePointsEquiv r L).injective
    rw [baseChangeBasePointsEquiv_comp, MulEquiv.apply_symm_apply]
    dsimp only [x]
    rw [MulEquiv.apply_symm_apply, Grp.comp_hom_hom, Category.assoc]
  have hc : c ≫ (baseChange r).map m = e := by
    dsimp only [c, e, conjugateFamily, conjugatePullback]
    rw [Category.assoc, innerIso_hom_comp, hx, ← Category.assoc, ← Functor.map_comp]
    rfl
  let uB := familySourceComparison K b a
  let uD := Descent.pullbackComparison T.hom s r rfl D
  let uQ := Descent.pullbackComparison T.hom s r rfl Q
  let uL := Descent.pullbackComparison T.hom s r rfl L
  refine ⟨uB ≪≫ σ ≪≫ uD.symm, uB.hom ≫ σ.hom ≫ c ≫ uQ.inv, ?_⟩
  have hn : (baseChange s).map ((baseChange T.hom).map m) ≫ uL.hom =
      uQ.hom ≫ (baseChange r).map m :=
    Descent.pullbackComparison_naturality T.hom s r rfl m
  apply (cancel_mono uL.hom).mp
  simp only [Category.assoc, hn, Iso.inv_hom_id_assoc, hc, hσ]
  exact (familyHom_evaluate_comp j b a).symm

end Langlands.GroupScheme.TorusSubgroupModuli
