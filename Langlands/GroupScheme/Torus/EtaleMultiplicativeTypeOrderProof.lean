import Langlands.GroupScheme.Torus.EtaleMultiplicativeTypeOrderForward
import Langlands.GroupScheme.Torus.EtaleMultiplicativeTypeOrderReverse

/-! # Étale groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace EtaleMultiplicativeTypeOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

/-- Rational points after extension are the original coefficient points. -/
def extensionPointsEquiv (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X) ≃*
      G.affinePoints (CommAlgCat.of k K) := by
  let b := algebraBaseMap k K
  let e : (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≅
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k K)) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ algebraBaseMap k K = algebraBaseMap k K
      exact Category.id_comp _)
  exact (baseChangePointsEquiv b G _).trans
    (G.points.mapIso e.op).groupIsoToMulEquiv

/-- An affine étale commutative group of prime-to-characteristic geometric
order is of multiplicative type. -/
theorem reverse (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Etale G.X.hom]
    [IsAffineHom G.X.hom]
    (hcomm : IsCommMonObj G.X)
    (hcard : Nat.Coprime (Nat.card (G.affinePoints (CommAlgCat.of k Ks))) p) :
    IsMultiplicativeType G := by
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  have : ExpChar Ks p := expChar_of_injective_algebraMap (algebraMap k Ks).injective p
  let H : CommGroupScheme (Spec (CommRingCat.of k)) := { G with comm := hcomm }
  let GK := (CommGroupScheme.baseChange (algebraBaseMap k Ks)).obj H
  have : Etale GK.X.hom := by
    change Etale (pullback.snd G.X.hom (algebraBaseMap k Ks))
    infer_instance
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k Ks))
    infer_instance
  have : IsAffine GK.X.left := isAffine_of_isAffineHom GK.X.hom
  have : IsFinite GK.X.hom := isFinite_of_affine_etale Ks GK.X
  have hcard' : Nat.Coprime
      (Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of Ks))) ⟶ GK.X)) p := by
    change Nat.Coprime
      (Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of Ks))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G).X)) p
    rw [Nat.card_congr (extensionPointsEquiv k Ks G).toEquiv]
    exact hcard
  obtain ⟨Λ, hΛ, hfg, ⟨d⟩⟩ := exists_diagonalizableIso_of_coprime_order Ks p GK hcard'
  exact ⟨Ks, inferInstance, inferInstance, Λ, hΛ, hfg, ⟨d⟩⟩

end EtaleMultiplicativeTypeOrder

/-- An affine étale group is of multiplicative type exactly when it is
commutative and its geometric order is prime to the characteristic exponent. -/
theorem etaleMultiplicativeTypeOrderStatement :
    EtaleMultiplicativeTypeOrderStatement.{u} := by
  intro k _ p _ Ks _ _ _ G _ _
  exact ⟨EtaleMultiplicativeTypeOrder.forward k p Ks G,
    fun h => EtaleMultiplicativeTypeOrder.reverse k p Ks G h.1 h.2⟩

end Langlands.GroupScheme
