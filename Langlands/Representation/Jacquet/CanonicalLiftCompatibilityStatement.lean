import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# Compatibility statements for actual stable-image canonical Jacquet lifts

These proposition definitions state independence of the strictly contracting
tuple and compatibility with normalized averaging under nested compact open
subgroups for representatives of the same Jacquet class.
-/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Any two strictly contracting tuples give the same actual all-power
stable-image submodule of the fixed-vector module for a factorizing subgroup. -/
def BlockStableImageTupleIndependenceClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a b : Fin B.length → F.Carrierˣ,
        B.IsStrictlyContracting T a → B.IsStrictlyContracting T b →
        stableImage ρ hρ K hK (B.blockScalar F.Carrier a) =
          stableImage ρ hρ K hK (B.blockScalar F.Carrier b)

/-- For nested factorizing compact open subgroups, averaging a smaller-subgroup
stable lift over the larger subgroup gives its larger-subgroup stable lift
whenever the two ambient representatives have the same Jacquet class. -/
def BlockStableImageNestedAverageClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K1 K0 : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK1 : IsCompact (K1 : Set (GeneralLinear n F.Carrier)))
      (hK0 : IsCompact (K0 : Set (GeneralLinear n F.Carrier))),
      K1 ≤ K0 →
      B.HasBlockIwahoriFactorization T K1 →
      B.HasBlockIwahoriFactorization T K0 →
      ∀ a1 a0 : Fin B.length → F.Carrierˣ,
        B.IsStrictlyContracting T a1 → B.IsStrictlyContracting T a0 →
        ∀ (w1 : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a1))
          (w0 : stableImage ρ hρ K0 hK0 (B.blockScalar F.Carrier a0)),
          let v1 := stableImageToRepresentation ρ hρ K1 hK1
            (B.blockScalar F.Carrier a1) w1
          let v0 := stableImageToRepresentation ρ hρ K0 hK0
            (B.blockScalar F.Carrier a0) w0
          Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v1 =
              Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v0 →
            Compact.averageMap ρ hρ K0 hK0 v1 = v0

/-- Tuple independence and nested-subgroup averaging compatibility of the
existing stable-image carriers, without assuming any canonical-lift object. -/
def BlockCanonicalLiftCompatibilityStatement : Prop :=
  BlockStableImageTupleIndependenceClause F T B V ∧
  BlockStableImageNestedAverageClause F T B V

end Langlands.Jacquet
