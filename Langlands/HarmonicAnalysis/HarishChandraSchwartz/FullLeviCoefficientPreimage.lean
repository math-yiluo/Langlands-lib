import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviOrbitMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviProductCoefficients

/-! # Product-induced preimages of ordinary ambient coefficients at the full root -/

noncomputable section

universe u uV uP

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Transport

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
  (M : Subgroup Γ) (hM : M = ⊤) (e : M ≃ₜ* Γ)
  (he : ∀ g, e (fullLeviGroupEquiv M hM g) = g)

private def fullLeviAmbientPullbackEquiv (A : SmoothRep.{0, u, uV} ℂ Γ) :
    (fullLeviAmbientSmoothRep M hM (SmoothRep.pullback e A)).representation.Equiv
      A.representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => by
    ext v
    change A.representation (e (fullLeviGroupEquiv M hM g)) v = A.representation g v
    rw [he]

private theorem exists_coefficient_preimage_of_equiv
    [IsTopologicalGroup Γ] {P : Type uP} [AddCommGroup P] [Module ℂ P]
    {A B : SmoothRep.{0, u, uV} ℂ Γ}
    (e : A.representation.Equiv B.representation)
    (E : P ≃ₗ[ℂ] CoefficientTensor A) (c : P →ₗ[ℂ] LocallyConstant Γ ℂ)
    (hc : ∀ w, coefficientTensorMap A (E w) = c w)
    (t : CoefficientTensor B) :
    ∃ w, c w = coefficientTensorMap B t := by
  let F := E.trans (coefficientTensorCongr e)
  let w := F.symm t
  refine ⟨w, (hc w).symm.trans ((coefficientTensorMap_congr e (E w)).symm.trans ?_)⟩
  exact congrArg (coefficientTensorMap B) (F.apply_symm_apply t)

end Transport

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "hM" => RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν
set_option hygiene false in
local notation "πM" => IrreducibleAdmissibleRep.pullback eG π

/-- Pull back to the full literal Levi and then to the ambient group. The
result is equivariantly identified with the original representation. -/
def rationalFullLeviAmbientInducingEquiv :
    (fullLeviAmbientSmoothRep 𝐌 hM (πM).obj).representation.Equiv π.obj.representation :=
  fullLeviAmbientPullbackEquiv 𝐌 hM eG (fun g =>
    (rationalFullLeviLiteralPointEquiv_apply hG hi hν (fullLeviGroupEquiv 𝐌 hM g)).trans
      (coe_fullLeviGroupEquiv 𝐌 hM g)) π.obj

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "Π" => productInducedCoefficientObject
  (isSemidirectDecomposition_standard hG hi hν
    (RationalPointFamily.rootSet_subset i ν Finset.univ))
  (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)) (πM).obj

set_option maxHeartbeats 350000 in
/-- At the full-group endpoint, every ordinary ambient tensor coefficient
is the actual coefficient of a product-induced value at the inducing
representation obtained by pullback. -/
theorem exists_rationalFullLeviProductCoefficient_of_ambient
    (t : CoefficientTensor π.obj) :
    ∃ Φ : Π,
      rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK (πM).obj (πM).property.2 Φ =
        coefficientTensorMap π.obj t := by
  let E := rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK (πM).obj (πM).property.2
  let c := rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK (πM).obj (πM).property.2
  have hc (w : Π) : coefficientTensorMap (fullLeviAmbientSmoothRep 𝐌 hM (πM).obj) (E w) =
      c w := by
    have h := coefficientTensorMap_rationalFullLeviProductCoefficientTensorEquiv
      hG hi hν hKc hPK (πM).obj (πM).property.2 w
    refine (DFunLike.congr ?_ ?_).trans (h.trans (DFunLike.congr ?_ ?_))
    · rfl
    · refine DFunLike.congr ?_ ?_ <;> rfl
    · rfl
    · rfl
  have h := exists_coefficient_preimage_of_equiv
    (rationalFullLeviAmbientInducingEquiv hG hi hν π) E c hc t
  with_reducible_and_instances exact h

end Langlands.HarishChandraSchwartz
