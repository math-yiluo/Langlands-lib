import Langlands.Global.AdelicIwasawaReduction
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.Global.InfinitePlaceIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.InfiniteAdelicMaximalCompactConjugacy

/-! # Adelic parabolic Iwasawa decomposition with prescribed infinite compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme InfiniteAdelicGroupPoints CompactIwasawa

/-- A prescribed maximal compact subgroup of the actual infinite point group extends
to a maximal compact adelic Iwasawa subgroup for a given rational parabolic. -/
def IwasawaWithInfiniteCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
    IsConnectedReductive G → IsParabolicSubgroup p →
    ∀ (H : Subgroup (InfiniteAdelicGroupPoints F G)), IsMaximalCompact H →
      ∃ K : Subgroup (AdelicGroupPoints F G), IsParabolicIwasawaCompact F G P p K ∧
        K.comap (ofInfinite F G).toMonoidHom = H

set_option maxHeartbeats 650000 in
/-- Start with an unrestricted Iwasawa subgroup. The conjugating infinite point has a
parabolic times compact factorization, so its effect on the compact can be realized by
an infinite point of the parabolic. -/
theorem iwasawaWithInfiniteCompact : IwasawaWithInfiniteCompactStatement.{u} := by
  intro F _ _ G _ P p hG hp H hH
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  obtain ⟨K, hK⟩ := parabolicIwasawaStatement_of_archimedean_finite_integral
    InfinitePlaceGroupPoints.parabolicIwasawaStatement FinitePlaceGroupPoints.parabolicIwasawaStatement
    IntegralIwasawaFamily.existenceStatement F G hG P p hp
  let H₀ := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨t, ht⟩ := infiniteAdelicMaximalCompactConjugacy F G H₀ H hG
    hK.isMaximalCompact_comap_ofInfinite hH
  obtain ⟨q, k, hk, he⟩ := hK.isIwasawaCompact.exists_eq (ofInfinite F G t)
  let a := infinite F G (map F P G p q)
  let c := infinite F G k
  have hc : c ∈ H₀ := (hK.1.mem_iff k).mp hk |>.1
  have hac : a * c = t := by
    have h := congrArg (infinite F G) he
    simpa only [map_mul, infinite_ofInfinite, a, c] using h
  let q₀ := ofInfinite F P (infinite F P q)
  let b := ofInfinite F G a
  have hb : map F P G p q₀ = b := by
    have hi : infinite F G (map F P G p q) =
        P.affinePointsTarget p (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F P q) :=
      DFunLike.congr_fun (P.affinePointsTarget_naturality p (CommAlgCat.ofHom
        (AlgHom.fst F (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))) q
    rw [show q₀ = ofInfinite F P (infinite F P q) from rfl, map_ofInfinite]
    exact congrArg (ofInfinite F G) hi.symm
  let e : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G :=
    { toMulEquiv := MulAut.conj b
      continuous_toFun := IsTopologicalGroup.continuous_conj b
      continuous_invFun := by
        change Continuous (fun x : AdelicGroupPoints F G => b⁻¹ * x * b)
        exact (continuous_const.mul continuous_id).mul continuous_const }
  let L := K.map e.toMonoidHom
  have hL : IsMaximalCompactSubgroup F G L := CompactIwasawa.IsMaximalCompact.map hK.1 e
  refine ⟨L, ⟨hL, Set.eq_univ_of_forall fun g => ?_⟩, ?_⟩
  · obtain ⟨q', k', hk', hq'⟩ := hK.isIwasawaCompact.exists_eq (g * b)
    refine ⟨map F P G p (q' * q₀⁻¹), ⟨q' * q₀⁻¹, rfl⟩, e k', ⟨k', hk', rfl⟩, ?_⟩
    change map F P G p (q' * q₀⁻¹) * (b * k' * b⁻¹) = g
    rw [map_mul, map_inv, hb]
    calc
      _ = (map F P G p q' * k') * b⁻¹ := by group
      _ = g := by rw [hq', mul_inv_cancel_right]
  · ext x
    rw [← ht, Subgroup.mem_comap, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    change b⁻¹ * ofInfinite F G x * b ∈ K ↔ t⁻¹ * x * t ∈ H₀
    rw [show b⁻¹ * ofInfinite F G x * b = ofInfinite F G (a⁻¹ * x * a) by
      simp only [b, map_mul, map_inv], ← hac]
    change a⁻¹ * x * a ∈ H₀ ↔ (a * c)⁻¹ * x * (a * c) ∈ H₀
    have heq : (a * c)⁻¹ * x * (a * c) = c⁻¹ * (a⁻¹ * x * a) * c := by group
    rw [heq]
    constructor
    · intro h
      exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hc) h) hc
    · intro h
      have h' := H₀.mul_mem (H₀.mul_mem hc h) (H₀.inv_mem hc)
      rwa [show c * (c⁻¹ * (a⁻¹ * x * a) * c) * c⁻¹ = a⁻¹ * x * a by group] at h'

end Langlands.Global.AdelicGroupPoints
