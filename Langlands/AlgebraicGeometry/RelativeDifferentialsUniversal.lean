import Langlands.AlgebraicGeometry.RelativeDifferentialsStatement
import Langlands.AlgebraicGeometry.PresheafRelativeDifferentialsUniversalProof

/-!
# Universal property of the constructed relative differential sheaf
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/-- Morphisms from the relative differential sheaf are relative derivations.
The universal property of the concrete presheaf is proved, not assumed. -/
def relativeDifferentialsHomEquiv (M : X.Modules) :
    (relativeDifferentials f ⟶ M) ≃ RelativeDerivation f M :=
  sheafifyRelativeDerivationHomEquiv (Langlands.PresheafDifferentials.derivation f.c)
    (Langlands.PresheafDifferentials.derivationUniversal f.c) M

lemma relativeDifferentialsHomEquiv_apply (M : X.Modules)
    (α : relativeDifferentials f ⟶ M) :
    relativeDifferentialsHomEquiv f M α =
      RelativeDerivation.postcomp (relativeDifferentialsDerivation f) α :=
  sheafifyRelativeDerivationHomEquiv_apply _ _ M α

lemma relativeDifferentialsHomEquiv_naturality {M N : X.Modules}
    (α : relativeDifferentials f ⟶ M) (β : M ⟶ N) :
    relativeDifferentialsHomEquiv f N (α ≫ β) =
      RelativeDerivation.postcomp (relativeDifferentialsHomEquiv f M α) β :=
  sheafifyRelativeDerivationHomEquiv_naturality _ _ α β

/-- The natural universal equivalence for the relative derivation functor. -/
def relativeDifferentialsCorepresentable :
    (relativeDerivationFunctor f).CorepresentableBy (relativeDifferentials f) :=
  sheafifyRelativeDerivationCorepresentable
    (Langlands.PresheafDifferentials.derivation f.c)
    (Langlands.PresheafDifferentials.derivationUniversal f.c)

theorem relativeDifferentialsUniversal : RelativeDifferentialsUniversalStatement f := by
  intro M
  have h : (fun (α : relativeDifferentials f ⟶ M) =>
      RelativeDerivation.postcomp (relativeDifferentialsDerivation f) α) =
        relativeDifferentialsHomEquiv f M :=
    funext fun α => (relativeDifferentialsHomEquiv_apply f M α).symm
  rw [h]
  exact (relativeDifferentialsHomEquiv f M).bijective

/-- Descend a relative derivation to a morphism from the differential sheaf. -/
def relativeDifferentialsDesc {M : X.Modules} (d : RelativeDerivation f M) :
    relativeDifferentials f ⟶ M :=
  (relativeDifferentialsHomEquiv f M).symm d

@[simp]
lemma relativeDifferentialsDesc_fac {M : X.Modules} (d : RelativeDerivation f M) :
    RelativeDerivation.postcomp (relativeDifferentialsDerivation f)
      (relativeDifferentialsDesc f d) = d := by
  rw [← relativeDifferentialsHomEquiv_apply]
  exact (relativeDifferentialsHomEquiv f M).apply_symm_apply d

lemma relativeDifferentials_hom_ext {M : X.Modules}
    (α β : relativeDifferentials f ⟶ M)
    (h : RelativeDerivation.postcomp (relativeDifferentialsDerivation f) α =
      RelativeDerivation.postcomp (relativeDifferentialsDerivation f) β) : α = β := by
  apply (relativeDifferentialsHomEquiv f M).injective
  simpa only [relativeDifferentialsHomEquiv_apply] using h

@[simp]
lemma relativeDifferentialsDesc_postcomp {M N : X.Modules}
    (d : RelativeDerivation f M) (α : M ⟶ N) :
    relativeDifferentialsDesc f (RelativeDerivation.postcomp d α) =
      relativeDifferentialsDesc f d ≫ α := by
  apply relativeDifferentials_hom_ext f
  simp only [relativeDifferentialsDesc_fac, RelativeDerivation.postcomp_comp]

end Langlands.Scheme
