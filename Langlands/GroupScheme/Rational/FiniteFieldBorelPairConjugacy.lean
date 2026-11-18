import Langlands.GroupScheme.Rational.FiniteFieldBorelConjugacy
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.FiniteFieldBorelPairStatement

/-! # Rational conjugacy of Borel pairs over finite fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FiniteFieldBorelPair

variable (k : Type u) [Field k] [Fintype k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Lang's equation expressed using the coefficient-conjugation action on the
actual algebraic-closure pullback. -/
theorem exists_eq_inv_mul_rationalConjugate
    (a : rationalPoints (baseChanged k (AlgebraicClosure k) G)) :
    ∃ x : rationalPoints (baseChanged k (AlgebraicClosure k) G),
      a = x⁻¹ * rationalConjugate k (AlgebraicClosure k) G
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) x := by
  let e := baseChangeCoeffEquiv k (AlgebraicClosure k) G
  obtain ⟨y, hy⟩ := FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius
    G (AlgebraicClosure k) (e a)
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [baseChangeCoeffEquiv_rationalConjugate, MulEquiv.apply_symm_apply]
  exact hy

/-- Two ground-field geometric Borels are conjugate by a ground-field point.
The geometric conjugator is corrected using Lang's theorem in the source Borel. -/
theorem geometricBorel_rationalConjugate
    (B B' : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (b' : B' ⟶ G)
    (hb : IsGeometricBorelSubgroup b) (hb' : IsGeometricBorelSubgroup b') :
    ∃ q : rationalPoints G,
      SubgroupFunctor.range (b ≫ (G.innerIso q).hom) = SubgroupFunctor.range b' := by
  let K := AlgebraicClosure k
  let F := GroupScheme.baseChange (baseMap k K)
  let GK := baseChanged k K G
  let bK := F.map b
  let bK' := F.map b'
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  let θ := rationalConjugate k K G σ
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom (baseMap k K))
    infer_instance
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (baseMap k K))
    infer_instance
  have : ConnectedSpace GK.X.left :=
    G.connectedSpace_baseChange_of_smooth_affine (baseMap k K)
  have hbK : IsBorelSubgroup bK := hb.2
  have hbK' : IsBorelSubgroup bK' := hb'.2
  obtain ⟨g, e, he⟩ := (borelConjugacy K GK).2 _ _ bK bK' hbK hbK'
  have hg : g • SubgroupFunctor.range bK = SubgroupFunctor.range bK' := by
    rw [SubgroupFunctor.basePoint_smul_range, he, SubgroupFunctor.range_iso_comp]
  have hθg : θ g • SubgroupFunctor.range bK = SubgroupFunctor.range bK' := by
    rw [SubgroupFunctor.basePoint_smul_range]
    have h := congrArg (SubgroupFunctor.galoisTransport k K G σ)
      (show SubgroupFunctor.range (F.map b ≫ (GK.innerIso g).hom) =
        SubgroupFunctor.range (F.map b') from by
          rw [he, SubgroupFunctor.range_iso_comp])
    rw [galoisTransport_conjugate_range, galoisTransport_range] at h
    exact h
  have hd : g⁻¹ * θ g ∈
      (SubgroupFunctor.range bK).normalizer.carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    rw [← SubgroupFunctor.stabilizer_basePointConjugation, MulAction.mem_stabilizer_iff]
    rw [mul_smul, hθg, ← hg, ← mul_smul, inv_mul_cancel, one_smul]
  have hd' := SubgroupFunctor.normalizer_carrier_base_le (SubgroupFunctor.range bK) hd
  rw [borelNormalizer K GK _ bK hbK] at hd'
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hd'
  have : Smooth B.X.hom := hb.1.smooth
  have : ConnectedSpace B.X.left := hb.1.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb.1.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨x, hx⟩ := exists_eq_inv_mul_rationalConjugate k B a
  let m := rationalPoints.map bK
  have hm : m (rationalConjugate k K B σ x) = θ (m x) :=
    (GaloisPointComparison.rationalConjugate_naturality k K b σ x).symm
  have hmx : g⁻¹ * θ g = (m x)⁻¹ * θ (m x) := by
    calc
      g⁻¹ * θ g = m a := ha.symm
      _ = m (x⁻¹ * rationalConjugate k K B σ x) := congrArg m hx
      _ = (m x)⁻¹ * θ (m x) := by rw [map_mul, map_inv, hm]
  let z := g * (m x)⁻¹
  have hz : θ z = z := by
    change θ (g * (m x)⁻¹) = g * (m x)⁻¹
    rw [map_mul, map_inv]
    have hθ : θ g = g * ((m x)⁻¹ * θ (m x)) := by
      rw [← hmx]
      group
    rw [hθ]
    group
  have hzrange : SubgroupFunctor.range (bK ≫ (GK.innerIso z).hom) =
      SubgroupFunctor.range bK' := by
    rw [← SubgroupFunctor.basePoint_smul_range]
    change (g * (m x)⁻¹) • SubgroupFunctor.range bK = _
    rw [mul_smul]
    have hmxrange : (m x)⁻¹ • SubgroupFunctor.range bK = SubgroupFunctor.range bK := by
      rw [SubgroupFunctor.basePoint_smul_range]
      change SubgroupFunctor.range (bK ≫ (GK.innerIso ((m x)⁻¹)).hom) = _
      rw [← map_inv]
      exact range_comp_innerIso_of_mem bK x⁻¹
    rw [hmxrange, hg]
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨q, hq⟩ := exists_rationalPoint_of_frobenius_fixed k K G z hz
  have hfpqc := fieldExtension_fpqc k K
  let : Surjective (baseMap k K) := hfpqc.1
  let : Flat (baseMap k K) := hfpqc.2.1
  let : QuasiCompact (baseMap k K) := hfpqc.2.2
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion b'.hom.hom.left := hb'.1.isClosedSubgroup
  have : Mono b'.hom.hom := Over.mono_of_mono_left _
  have : Mono (b ≫ (G.innerIso q).hom).hom.hom := by
    change Mono (b.hom.hom ≫ (G.innerIso q).hom.hom.hom)
    infer_instance
  refine ⟨q, SubgroupFunctor.range_eq_of_baseChange_eq (baseMap k K)
    (b ≫ (G.innerIso q).hom) b' ?_⟩
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    Functor.map_comp, baseChange_innerIso_hom, hq]
  exact hzrange

end Langlands.GroupScheme.FiniteFieldBorelPair
