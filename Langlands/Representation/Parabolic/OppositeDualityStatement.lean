import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Jacquet.Normalized
import Langlands.Representation.Smooth.Contragredient.Definitions

namespace Langlands.Parabolic

open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The asymptotic formula on actual block-scalar elements. The bound may
depend on the vector and smooth functional; no contracting cone is assumed. -/
def CanonicalPairingAsymptotics :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
      (Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ) → Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  fun ρ b =>
    let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
    let J := Jacquet.normalizedActionOfModulus ρ
      (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
      (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) δ
    ∀ (v : V) (ℓ : SmoothDual ρ),
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ a : Fin B.length → F.Carrierˣ,
          (∀ i j : Fin B.length, i < j →
            (((T.normalizedAbsUnits (a i * (a j)⁻¹)) : ℝ≥0) : ℝ) < ε) →
          let aM : B.Levi F.Carrier :=
            fun i => GeneralLinear.scalar (n := B.size i) (a i)
          ℓ.1 (ρ (B.leviEmbedding F.Carrier aM) v) =
            (T.leviHalfModulus B aM : ℂ) *
              b (Jacquet.mk (smoothContragredient ρ)
                  (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
                (J (B.leviEquiv F.Carrier aM)
                  (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v))

/-- Unique bilinear canonical pairing between the upper Jacquet quotient
and the opposite Jacquet quotient of the actual smooth dual. -/
def CanonicalPairingClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
    IsAdmissible ρ →
    ∃! b : Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ,
      CanonicalPairingAsymptotics F T B V ρ b

/-- Every pairing with the canonical asymptotics induces the actual smooth
contragredient equivalence. Opposite normalization uses the inverse full
modulus, so its inverse half is the positive upper-parabolic half. -/
def OppositeJacquetDualityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
    IsAdmissible ρ →
    ∀ b : Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ,
      CanonicalPairingAsymptotics F T B V ρ b →
      let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
      let J := Jacquet.normalizedActionOfModulus ρ
        (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) δ
      let JopDual := Jacquet.normalizedActionOfModulus (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) δ⁻¹
      ∃ E : Representation.Equiv JopDual (smoothContragredient J),
        ∀ (ℓ : SmoothDual ρ) (v : V),
          (E (Jacquet.mk (smoothContragredient ρ)
            (B.oppositeUnipotentSubgroup F.Carrier) ℓ)).1
              (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v) =
          b (Jacquet.mk (smoothContragredient ρ)
            (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
              (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v)

/-- Casselman's canonical pairing and opposite-parabolic Jacquet duality
on actual finite-p-adic GL block groups. -/
def OppositeDualityStatement : Prop :=
  CanonicalPairingClause F T B V ∧ OppositeJacquetDualityClause F T B V

end Langlands.Parabolic
