import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.Group.GL.RankReindex
import Langlands.LocalField.PadicBridge
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.CuspidalSupport.UnitaryProductSupport

/-! # Supercuspidal support of a σ-orbit product -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear PadicField.TopologicalData

universe u v z

variable {F : Type u} [Field F] [TopologicalSpace F]
  {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p}
  (T : E.TopologicalData) [Algebra F E.Carrier]

/-- The supercuspidal support of the seed is a submultiset of the support
of any smooth realization of its positive-length normalized orbit product. -/
def SigmaOrbitProductSupportStatement : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ [IsModuleTopology F E.Carrier] (σ : E.Carrier ≃ₐ[F] E.Carrier)
    {t m n : ℕ}, 0 < t → ∀ (hm : 0 < m) (hrank : t * m = n)
    (Q : SmoothRep.{0,v,z} ℂ (GeneralLinear m E.Carrier))
    (P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)),
    Q.IsIrreducible → IsUnitarizable Q.representation →
    Nonempty (P.representation.Equiv ((sigmaOrbitProduct σ t hm Q.representation).comp
      (reindex (R := E.Carrier) (finCongr hrank)).symm.toMonoidHom)) →
    ∀ s : Multiset (CuspidalDatum.{max v z,v} T),
      T.IsSupercuspidalSupport Q.universeLift.{v} s →
      ∃ s', s ≤ s' ∧ T.IsSupercuspidalSupport P.universeLift.{v} s'

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
/-- Support inclusion follows from the support sum for normalized unitary products. -/
theorem sigmaOrbitProductSupport : SigmaOrbitProductSupportStatement.{u,v,z} (F := F) T := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ σ t m n ht hm hrank Q P hQi hQu hOrbit s hs
  subst n
  obtain ⟨eOrbit⟩ := hOrbit
  rw [reindex_finCongr_rfl] at eOrbit
  change P.representation.Equiv
    ((sigmaOrbitProduct σ t hm Q.representation).comp (MonoidHom.id _)) at eOrbit
  rw [MonoidHom.comp_id] at eOrbit
  let B := BlockShape.uniform t m hm
  let θ (i : Fin B.length) : GeneralLinear m E.Carrier ≃ₜ* GeneralLinear m E.Carrier :=
    { entrywiseAut (σ ^ i.val) m with
      continuous_toFun := continuous_entrywiseAut (σ ^ i.val) m
      continuous_invFun := continuous_entrywiseAut_symm (σ ^ i.val) m }
  let A (i : Fin B.length) := SmoothRep.pullback (θ i) Q.universeLift.{v}
  have hA (i : Fin B.length) :
      (A i).IsIrreducible ∧ IsUnitarizable (A i).representation :=
    ⟨(CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ (θ i).toMulEquiv).mpr
        (Q.isIrreducible_universeLift_iff.mpr hQi),
      ((isUnitarizable_iff_of_equiv Q.universeLiftEquiv.{v}).mp hQu).comp
        (θ i).toMonoidHom⟩
  have hsupports (i : Fin B.length) :
      ∃ sᵢ : Multiset (CuspidalDatum.{max v z,v} T),
        T.IsSupercuspidalSupport (A i) sᵢ := by
    obtain ⟨k, ρ, hρ⟩ :=
      glSupercuspidalEmbedding.{max v z,v} p E T m hm (A i) (hA i).1
    exact ⟨↑(List.ofFn ρ), k, ρ, rfl, hρ.isCuspidalConstituent⟩
  choose S hS using hsupports
  let j : Fin B.length := ⟨0, ht⟩
  have hθ : (θ j).toMulEquiv = MulEquiv.refl _ := by
    change entrywiseAut (σ ^ (0 : ℕ)) m = _
    rw [pow_zero]
    apply MulEquiv.ext
    intro g
    exact entrywiseAut_one_apply (F := F) g
  have ej : Q.universeLift.{v} ≅ A j := SmoothRep.mkIso (by
    change Q.universeLift.{v}.representation.Equiv
      (Q.universeLift.{v}.representation.comp (θ j).toMulEquiv.toMonoidHom)
    rw [hθ]
    exact Representation.Equiv.refl _)
  have hj : s = S j :=
    glSupercuspidalSupportUniqueness.{max v z,v} p E T m hm
      (A j) (hA j).1 s (S j) (hs.of_iso ej) (hS j)
  have hsum := T.normalizedUnitaryProduct_hasSupercuspidalSupport.{v,max v z}
    (t * m) (Nat.mul_pos ht hm) B A hA S hS
  let eBlocks := T.normalizedProductInducedEquiv B
    (fun i => BinaryTensor.compEquiv Q.universeLiftEquiv.{v} (θ i).toMonoidHom)
  let eProd := (T.normalizedProductInductionObjEquiv B A).trans
    (eBlocks.symm.trans (eOrbit.symm.trans P.universeLiftEquiv.{v}))
  exact ⟨∑ i, S i, hj ▸ Finset.single_le_sum_of_canonicallyOrdered
    (Finset.mem_univ j), hsum.of_iso (SmoothRep.mkIso eProd)⟩

end Langlands.BaseChange
