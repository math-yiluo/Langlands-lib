import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# Geometric averaging bridge for actual block stable images

This proposition states stable-image membership after nested compact averaging
and preservation of a Jacquet class fixed by the larger compact Levi subgroup.
It requires smoothness only and does not assert uniqueness of canonical lifts.
-/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Averaging a smaller-subgroup stable-image vector over the larger compact
subgroup lies in its stable image. Its Jacquet class is preserved whenever that
class is fixed by the larger subgroup's Levi intersection. -/
def BlockStableImageAverageBridgeStatement : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
    (K1 K0 : OpenSubgroup (GeneralLinear n F.Carrier))
    (hK1 : IsCompact (K1 : Set (GeneralLinear n F.Carrier)))
    (hK0 : IsCompact (K0 : Set (GeneralLinear n F.Carrier))),
    K1 ≤ K0 →
    B.HasBlockIwahoriFactorization T K1 →
    B.HasBlockIwahoriFactorization T K0 →
    ∀ a : Fin B.length → F.Carrierˣ,
      B.IsStrictlyContracting T a →
      ∀ w : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a),
        let v := stableImageToRepresentation ρ hρ K1 hK1
          (B.blockScalar F.Carrier a) w
        let e0 := Compact.averageMap ρ hρ K0 hK0
        let N := B.unipotentSubgroup F.Carrier
        let M := B.leviSubgroup F.Carrier
        let hMN := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
        (⟨e0 v, Compact.averageMap_mem_fixedVectors ρ hρ K0 hK0 v⟩ :
            fixedVectors ρ K0.toSubgroup) ∈
            stableImage ρ hρ K0 hK0 (B.blockScalar F.Carrier a) ∧
          (Jacquet.mk ρ N v ∈
              fixedVectors (Jacquet.action ρ N M hMN)
                (K0.toSubgroup.comap M.subtype) →
            Jacquet.mk ρ N (e0 v) = Jacquet.mk ρ N v)

end Langlands.Jacquet
