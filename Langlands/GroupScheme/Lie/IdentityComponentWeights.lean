import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Actual adjoint weights in the identity component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section SmoothMono

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
  (f : H ⟶ G) [Mono f.hom.hom] (hf : Smooth f.hom.hom.left)
  (i : T.toGrp ⟶ H) (α : characterLattice T)

/-- A smooth monomorphic group map identifies every actual adjoint weight
through its actual differential, over any commutative ring. -/
def smoothMonoWeightEquiv : weightSpace i α ≃ₗ[R] weightSpace (i ≫ f) α :=
  LinearEquiv.ofBijective
    ((Lie.targetMapLinear f R).comp (weightSpace i α).subtype |>.codRestrict
      (weightSpace (i ≫ f) α) (fun X =>
        lieKernelHomLinear_mem_weightSpace f i α X.property))
    ⟨by
      intro X Y h
      apply Subtype.ext
      exact Lie.targetMapLinear_injective f R (congrArg Subtype.val h),
    by
      intro Y
      obtain ⟨X, hX⟩ := Lie.targetMapLinear_surjective_of_smooth f R hf Y.val
      have hm : X ∈ weightSpace i α :=
        (lieKernelHomLinear_mem_weightSpace_iff f i α X).mp (hX.symm ▸ Y.property)
      exact ⟨⟨X, hm⟩, Subtype.ext hX⟩⟩

@[simp] theorem smoothMonoWeightEquiv_coe (X : weightSpace i α) :
    (smoothMonoWeightEquiv f hf i α X : Additive (lieKernel G R)) =
      Lie.targetMapLinear f R X := rfl

end SmoothMono

namespace IdentityComponent

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)

/-- The canonical factor of an actual split-torus map through the actual
identity component, retaining the supplied torus as its source. -/
def torusHom : T.toGrp ⟶ identityComponent G :=
  haveI := hT.connectedSpace
  factor G i

@[reassoc (attr := simp)] theorem torusHom_comp :
    torusHom i hT ≫ identityComponentι G = i := by
  let := hT.connectedSpace
  exact factor_identityComponentι G i

theorem isClosedSubgroup_torusHom (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (torusHom i hT) :=
  IsClosedSubgroup.of_comp (isClosedSubgroup_identityComponentι G) (by
    rwa [torusHom_comp])

/-- Passing to the actual identity component preserves every actual adjoint
character weight via the differential of its open-and-closed inclusion. -/
def weightEquiv (α : characterLattice T) :
    weightSpace (torusHom i hT) α ≃ₗ[k] weightSpace i α :=
  (smoothMonoWeightEquiv (identityComponentι G) inferInstance (torusHom i hT) α).trans
    (LinearEquiv.ofEq _ _ (by rw [torusHom_comp]))

@[simp] theorem weightEquiv_coe (α : characterLattice T)
    (X : weightSpace (torusHom i hT) α) :
    (weightEquiv i hT α X : Additive (lieKernel G k)) =
      Lie.targetMapLinear (identityComponentι G) k X := rfl

theorem finrank_weightSpace (α : characterLattice T) :
    Module.finrank k (weightSpace (torusHom i hT) α) =
      Module.finrank k (weightSpace i α) :=
  (weightEquiv i hT α).finrank_eq

theorem weightSpace_eq_bot_iff (α : characterLattice T) :
    weightSpace (torusHom i hT) α = ⊥ ↔ weightSpace i α = ⊥ := by
  simpa only [Submodule.subsingleton_iff_eq_bot] using
    (weightEquiv i hT α).toEquiv.subsingleton_congr

/-- The nonzero adjoint characters are exactly unchanged. -/
theorem roots_torusHom : roots (torusHom i hT) = roots i := by
  ext α
  exact and_congr Iff.rfl (not_congr (weightSpace_eq_bot_iff i hT α))

end IdentityComponent

end Langlands.GroupScheme
