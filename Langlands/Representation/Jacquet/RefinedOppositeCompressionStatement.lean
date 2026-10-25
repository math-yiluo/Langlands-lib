import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.CuspidalSupport.DualAveraging
import Langlands.Representation.Parabolic.OppositeRefinementDefinitions

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uF uV

/-- Multiplication and actual quotient compatibility for normalized opposite
compression in an arbitrary smooth representation of a product Levi. -/
def RefinedOppositeCompressionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
        let KP := CuspidalSupport.leviPiOpenSubgroup T B K
        let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
        let g := fun (a : ∀ i, Fin (S i).length → F.Carrierˣ) =>
          (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹ : B.Levi F.Carrier)
        (∀ a b : ∀ i, Fin (S i).length → F.Carrierˣ,
          (∀ i, (S i).IsWeaklyContracting T (a i)) →
          (∀ i, (S i).IsWeaklyContracting T (b i)) →
            compressedAction ρ hρ KP hKP (g (a * b)) =
              compressedAction ρ hρ KP hKP (g a) *
                compressedAction ρ hρ KP hKP (g b)) ∧
        (∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
          (∀ i, (S i).IsWeaklyContracting T (a i)) →
          ∀ v : fixedVectors ρ KP.toSubgroup,
            mk ρ (refinedOppositeUnipotent F.Carrier B S)
                (compressedAction ρ hρ KP hKP (g a) v : V) =
              mk ρ (refinedOppositeUnipotent F.Carrier B S) (ρ (g a) (v : V)))

end Langlands.Jacquet
