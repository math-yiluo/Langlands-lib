import Langlands.Representation.Families.RationalTwistLocalSeparation
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Local twist separation in the actual rational Levi topology -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v w

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {P M : GroupScheme (Spec (CommRingCat.of k))}
variable (l : M ⟶ P) (hl : GroupScheme.IsRationalLeviSubgroup l)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The Levi's own point topology is the canonical evaluation topology used by
the published rational twist-stabilizer theorem. -/
theorem leviPointTopology_eq_canonical :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    leviPointTopology l hl = rationalPointTopology k M.X :=
  rfl

/-- Mixed actual Levi twist-isomorphism locus, using the exact smooth-twist
expression of the irreducible-induced-twist existence target. -/
def leviUnramifiedTwistIsoLocus :
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
    ∀ [NonarchimedeanGroup (GroupScheme.rationalPoints M)],
      SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M) →
        SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M) →
          Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)) :=
  letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
  fun A B => {ψ | Nonempty (A.twist ψ.val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ ψ) ≅ B)}

/-- There is no topology transport or change of twist in the Levi
specialization: both isomorphism loci are definitionally equal. -/
theorem leviUnramifiedTwistIsoLocus_eq_canonical :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
    ∀ [NonarchimedeanGroup (GroupScheme.rationalPoints M)]
      (A B : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M)),
      leviUnramifiedTwistIsoLocus l hl A B =
        CuspidalSupport.rationalUnramifiedTwistIsoLocus M A B :=
  fun _ _ => rfl

/-- The mixed twist-isomorphism locus of an irreducible actual Levi object is
finite, with the exact Levi topology and smooth-twist expression. -/
theorem leviUnramifiedTwistIsoLocus_finite :
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
    ∀ [NonarchimedeanGroup (GroupScheme.rationalPoints M)]
      (A B : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M)),
      A.IsIrreducible → (leviUnramifiedTwistIsoLocus l hl A B).Finite := by
  let : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
  intro _ A B hA
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  exact CuspidalSupport.rationalUnramifiedTwistIsoLocus_finite
    M hl.isConnectedReductive A B hA

/-- Local isolation of mixed twists for actual rational Levi data. -/
theorem exists_isOpen_leviUnramifiedTwistIso_separation :
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
    ∀ [NonarchimedeanGroup (GroupScheme.rationalPoints M)]
      (A B : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M)),
      A.IsIrreducible →
      ∃ V : Set (unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)),
        IsOpen V ∧ 1 ∈ V ∧ ∀ ψ ∈ V,
          Nonempty (A.twist ψ.val.toMonoidHom
            (unramifiedCharacter_isOpen_ker _ ψ) ≅ B) ↔
              ψ = 1 ∧ Nonempty (A ≅ B) := by
  let : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
  intro _ A B hA
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  exact CuspidalSupport.exists_isOpen_rationalUnramifiedTwistIso_separation
    M hl.isConnectedReductive A B hA

/-- Two actual Levi twist families based at the identity have no nearby
isomorphisms except equality of their characters and isomorphism of their bases. -/
theorem eventually_leviUnramifiedTwistsIso_separation :
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
    ∀ [NonarchimedeanGroup (GroupScheme.rationalPoints M)]
      (A B : SmoothRep.{0, u, v} ℂ (GroupScheme.rationalPoints M)),
      A.IsIrreducible →
      ∀ {T : Type w} [TopologicalSpace T] (t₀ : T)
        (f g : T → unramifiedCharacters (fun chi => (rationalNormCharacters M chi).toMul)),
        ContinuousAt f t₀ → ContinuousAt g t₀ → f t₀ = 1 → g t₀ = 1 →
        ∀ᶠ t in 𝓝 t₀,
          Nonempty (A.twist (f t).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker _ (f t)) ≅
              B.twist (g t).val.toMonoidHom
                (unramifiedCharacter_isOpen_ker _ (g t))) ↔
                  f t = g t ∧ Nonempty (A ≅ B) := by
  let : TopologicalSpace (GroupScheme.rationalPoints M) := leviPointTopology l hl
  intro _ A B hA T _ t₀ f g hf hg hf₀ hg₀
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  exact CuspidalSupport.eventually_rationalUnramifiedTwistsIso_separation
    M hl.isConnectedReductive A B hA t₀ f g hf hg hf₀ hg₀

end Langlands.Aubert.General.RepresentedParabolic
