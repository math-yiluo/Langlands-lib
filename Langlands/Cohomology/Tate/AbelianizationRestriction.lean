import Langlands.Cohomology.Tate.AbelianizationCorestriction
import Langlands.Cohomology.Tate.NegativeTransferComparison
import Langlands.Cohomology.Tate.SchreierTransfer

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G J : Type u} [CommRing R] [Group G] [Group J]

/-- The actual degree-one chain comparison on a generator. -/
lemma chainsIsoOne_inv_single (A : Rep.{u} R G) (g : G) (a : A) :
    (groupHomology.chainsIso₁ A).inv (Finsupp.single g a) =
      Finsupp.single (fun _ : Fin 1 => g) a := by
  classical
  change Finsupp.domLCongr (Equiv.funUnique (Fin 1) G).symm (Finsupp.single g a) = _
  rw [Finsupp.domLCongr_single]
  rfl

/-- A proved chain map acts on the actual first-homology class of a representative. -/
lemma groupHomology_chainMap_H1π
    {A : Rep.{u} R G} {B : Rep.{u} R J} [A.IsTrivial] [B.IsTrivial]
    (F : groupHomology.inhomogeneousChains A ⟶ groupHomology.inhomogeneousChains B)
    (x : G →₀ A) (y : J →₀ B)
    (hxy : F.f 1 ((groupHomology.chainsIso₁ A).inv x) =
      (groupHomology.chainsIso₁ B).inv y) :
    HomologicalComplex.homologyMap F 1
        (groupHomology.H1π A ((groupHomology.cycles₁IsoOfIsTrivial A).inv x)) =
      groupHomology.H1π B ((groupHomology.cycles₁IsoOfIsTrivial B).inv y) := by
  let z := (groupHomology.isoCycles₁ A).inv
    ((groupHomology.cycles₁IsoOfIsTrivial A).inv x)
  let w := (groupHomology.isoCycles₁ B).inv
    ((groupHomology.cycles₁IsoOfIsTrivial B).inv y)
  have hz : (groupHomology.inhomogeneousChains A).iCycles 1 z =
      (groupHomology.chainsIso₁ A).inv x :=
    groupHomology.isoCycles₁_inv_comp_iCycles_apply A
      ((groupHomology.cycles₁IsoOfIsTrivial A).inv x)
  have hw : (groupHomology.inhomogeneousChains B).iCycles 1 w =
      (groupHomology.chainsIso₁ B).inv y :=
    groupHomology.isoCycles₁_inv_comp_iCycles_apply B
      ((groupHomology.cycles₁IsoOfIsTrivial B).inv y)
  have hc : HomologicalComplex.cyclesMap F 1 z = w := by
    apply (ModuleCat.mono_iff_injective
      ((groupHomology.inhomogeneousChains B).iCycles 1)).mp inferInstance
    exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i F 1) z).trans
      ((congrArg (F.f 1) hz).trans (hxy.trans hw.symm))
  exact (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality F 1) z).trans
    (congrArg ((groupHomology.inhomogeneousChains B).homologyπ 1) hc)

variable [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

omit [Fintype G] [Fintype H] in
/-- Ordinary homological transfer on first-homology generators with trivial coefficients. -/
lemma ordinaryHomologyTransfer_single (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    ordinaryHomologyTransfer H A 1
        (groupHomology.H1π A
          ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))) =
      ∑ q : G ⧸ H, groupHomology.H1π (Rep.res H.subtype A)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.res H.subtype A)).inv
          (Finsupp.single (schreierElement H g q) a)) := by
  classical
  have hchain : (ordinaryTransferChainMap H A).f 1
        ((groupHomology.chainsIso₁ A).inv (Finsupp.single g a)) =
      (groupHomology.chainsIso₁ (Rep.res H.subtype A)).inv
        (∑ q : G ⧸ H, Finsupp.single (schreierElement H g q) a) := by
    rw [chainsIsoOne_inv_single, ordinaryTransferChainMap_single, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [transferTuple_one, Representation.isTrivial_apply, chainsIsoOne_inv_single]
  refine (groupHomology_chainMap_H1π (ordinaryTransferChainMap H A)
    (Finsupp.single g a) (∑ q : G ⧸ H, Finsupp.single (schreierElement H g q) a) hchain).trans ?_
  rw [map_sum, map_sum]

/-- Tate restriction on a single degree-minus-two class is the sum of Schreier classes. -/
theorem restriction_minusTwoClass (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    restriction H A (-2) (minusTwoClass A g a) =
      ∑ q : G ⧸ H, minusTwoClass (Rep.res H.subtype A) (schreierElement H g q) a := by
  have hh := ConcreteCategory.congr_hom (restriction_groupHomology H A 1)
    (minusTwoClass A g a)
  change restriction H A (-2) (minusTwoClass A g a) =
    ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app
      (Rep.res H.subtype A)).inv
      (ordinaryHomologyTransfer H A 1
        (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).hom
          (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
            (groupHomology.H1π A
              ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))))) at hh
  rw [Iso.inv_hom_id_apply, ordinaryHomologyTransfer_single, map_sum] at hh
  exact hh

/-- Integral Tate restriction in degree minus two is Mathlib's actual abelianization transfer. -/
theorem integralMinusTwoEquiv_restriction
    (x : tateCohomology (integralTrivial G) (-2)) :
    integralMinusTwoEquiv H (restriction H (integralTrivial G) (-2) x) =
      abelianizationTransfer H (integralMinusTwoEquiv G x) := by
  classical
  obtain ⟨g, rfl⟩ := integralMinusTwoClass_surjective x
  rw [restriction_minusTwoClass, map_sum, integralMinusTwoEquiv_class,
    abelianizationTransfer_schreier]
  exact Finset.sum_congr rfl (fun q _ => integralMinusTwoEquiv_class (schreierElement H g q))

end Langlands.Tate
