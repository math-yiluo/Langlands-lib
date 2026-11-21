import Langlands.TraceFormula.GeneralLinearWeilTwistedGeometry
import Langlands.Global.AdelicWeilNormOneComparisonProof
import Langlands.Global.AdelicGLDeterminantNormOne

/-! # Norm-one points in the Weil adelic matrix coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance weilNormOneGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilNormOneGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

private theorem mem_normOne_map_iso_iff {F : Type u} [Field F] [NumberField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))} (e : G ≅ H) (x : AdelicGroupPoints F G) :
    map F G H e.hom x ∈ normOneSubgroup F H ↔ x ∈ normOneSubgroup F G := by
  constructor
  · intro hx
    have hy := map_normOneSubgroup_le F H G e.inv ⟨map F G H e.hom x, hx, rfl⟩
    change map F H G e.inv (map F G H e.hom x) ∈ normOneSubgroup F G at hy
    rwa [map_comp_apply, e.hom_inv_id, map_id_apply] at hy
  · intro hx
    exact map_normOneSubgroup_le F G H e.hom ⟨x, hx, rfl⟩

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (n : ℕ)

set_option maxHeartbeats 900000 in
set_option maxRecDepth 2000 in
/-- In the original adelic matrix coordinates, the Weil norm-one subgroup
is the determinant-norm kernel over the upper field. -/
theorem generalLinearWeilAdelicMap_mem_normOne_iff (x : AdelicGroupPoints K Wₙ) :
    cyclicWeilAdelicMap K L n x ∈ AdelicGL.determinantNormOne L n ↔
      x ∈ normOneSubgroup K Wₙ := by
  let H := AffineWeil.unitBaseChange K L GLₙ
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L)
  let j : H ≅ G := GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)
  let e := AdelicWeilRestriction.adelicPointsEquiv K L H
  change GeneralLinearGroupPoints.adelicHomeomorph L n (map L H G j.hom (e x)) ∈ _ ↔ _
  rw [← GeneralLinearGroupPoints.mem_normOneSubgroup_iff_determinantNorm,
    mem_normOne_map_iso_iff]
  have h : (normOneSubgroup K Wₙ).map e.toMonoidHom = normOneSubgroup L H :=
    (AdelicWeilRestriction.normOneComparison K L H).2.2
  rw [← h, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, he⟩ => e.injective he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
/-- The matrix coordinate equivalence restricts to a topological group
isomorphism of the two norm-one subgroups. -/
def generalLinearWeilNormOneHomeomorph
    (e : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGL L n)
    (he : ⇑e = cyclicWeilAdelicMap K L n) :
    normOneSubgroup K Wₙ ≃ₜ* AdelicGL.determinantNormOne L n :=
  Langlands.QuotientIntegration.subgroupContinuousMulEquiv e _ _ fun x => by
    rw [congrFun he x]
    exact generalLinearWeilAdelicMap_mem_normOne_iff K L n x

@[simp]
theorem generalLinearWeilNormOneHomeomorph_val
    (e : AdelicGroupPoints K Wₙ ≃ₜ* AdelicGL L n)
    (he : ⇑e = cyclicWeilAdelicMap K L n) (x : normOneSubgroup K Wₙ) :
    (generalLinearWeilNormOneHomeomorph K L n e he x).val = e x.val := rfl

end Langlands.TraceFormula
