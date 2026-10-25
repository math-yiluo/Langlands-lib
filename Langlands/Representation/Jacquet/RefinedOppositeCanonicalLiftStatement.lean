import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.CuspidalSupport.DualAveraging
import Langlands.Representation.Parabolic.OppositeRefinementDefinitions

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Generalized compression kernel for the actual product opposite radical. -/
def RefinedOppositePowerKernelJacquetClause : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        let KP := CuspidalSupport.leviPiOpenSubgroup T B K
        let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
        let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
        powerKernelSup ρ hρ KP hKP g =
          LinearMap.ker (fixedJacquetMap ρ
            (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
            (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
            KP.toSubgroup)

/-- The actual product opposite quotient is bijective on the all-power stable image. -/
def RefinedOppositeStableImageJacquetBijectiveClause : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        let KP := CuspidalSupport.leviPiOpenSubgroup T B K
        let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
        let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
        Function.Bijective (stableImageJacquetMap ρ hρ KP hKP g
          (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
          (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property))

/-- The closed product-Levi opposite canonical-lift family, with independent universes. -/
def RefinedOppositeCanonicalLiftStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V],
    RefinedOppositePowerKernelJacquetClause F T B S V ∧
      RefinedOppositeStableImageJacquetBijectiveClause F T B S V

end Langlands.Jacquet
