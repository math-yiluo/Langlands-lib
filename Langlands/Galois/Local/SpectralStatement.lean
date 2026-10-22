import Langlands.Galois.Local.SpectralDefinitions
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas

open IsLocalRing

namespace Langlands.LocalGalois

universe u v

/-- Exactness and topology of the constructed spectral residue action. -/
def SpectralResidueExactness : Prop :=
  ∀ (K : Type u) (L : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [IsGalois K L]
    [Finite (ResidueField (baseIntegers K))],
    (∀ x : L, IsIntegral (baseIntegers K) x ↔ x ∈ extensionIntegers K L) ∧
    (∀ [IsAlgClosed L], IsAlgClosure (ResidueField (baseIntegers K))
      (ResidueField (extensionIntegers K L))) ∧
    (∀ (σ : Gal(L/K)) (x : extensionIntegers K L),
      residueHom K L σ (residue _ x) = residue _ (integerAut K L σ x)) ∧
    Continuous (residueHom K L) ∧
    Function.Surjective (residueHom K L) ∧
    IsOpenMap (residueHom K L) ∧
    (∀ σ : Gal(L/K), σ ∈ inertia K L ↔
      ∀ x : extensionIntegers K L, residue _ (integerAut K L σ x) = residue _ x) ∧
    inertia K L = ((extensionIntegers K L).inertiaSubgroup K).comap
      (decompositionHom K L) ∧
    (inertia K L).Normal ∧
    IsClosed (inertia K L : Set Gal(L/K)) ∧
    CompactSpace (inertia K L) ∧
    TotallyDisconnectedSpace (inertia K L) ∧
    ∃ e : (Gal(L/K) ⧸ inertia K L) ≃ₜ*
        Gal(ResidueField (extensionIntegers K L)/ResidueField (baseIntegers K)),
      ∀ σ : Gal(L/K), e (QuotientGroup.mk σ) = residueHom K L σ

end Langlands.LocalGalois
