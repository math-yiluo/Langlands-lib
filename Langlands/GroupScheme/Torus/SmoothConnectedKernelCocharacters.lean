import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.PositiveMultipleLift
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Mathlib.Algebra.Module.Projective

/-! # Integral cocharacters of split-torus quotients with smooth connected kernel -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Diagonalizable

/-- Smoothness and connectedness eliminate all torsion in a finitely generated
character group of an actual diagonalizable group. -/
theorem free_of_smooth_connected (k : Type u) [Field k]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    [Smooth (groupScheme (CommRingCat.of k) Λ).X.hom]
    [ConnectedSpace (groupScheme (CommRingCat.of k) Λ).X.left] :
    Module.Free ℤ Λ := by
  classical
  have : Algebra.FiniteType (CommRingCat.of k)
      (AddMonoidAlgebra (CommRingCat.of k) Λ) := inferInstance
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing (AddMonoidAlgebra (CommRingCat.of k) Λ) :=
    Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) _
  have : IsLocallyNoetherian (groupScheme (CommRingCat.of k) Λ).X.left := by
    change IsLocallyNoetherian
      (Spec (CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k) Λ)))
    infer_instance
  have : IsIntegral (groupScheme (CommRingCat.of k) Λ).X.left :=
    CharacterLatticeProof.isIntegral_of_smooth k
      (groupScheme (CommRingCat.of k) Λ).X.hom
  have : IsDomain (AddMonoidAlgebra (CommRingCat.of k) Λ) :=
    (affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra (CommRingCat.of k) Λ))).mp
      (inferInstanceAs (IsIntegral (groupScheme (CommRingCat.of k) Λ).X.left))
  let A := AddMonoidAlgebra (CommRingCat.of k) Λ
  let F := FractionRing A
  let w : Multiplicative Λ →* F :=
    (algebraMap A F).toMonoidHom.comp ((Units.coeHom A).comp
      (monomialUnits (CommRingCat.of k) Λ))
  have hw : LinearIndependent (CommRingCat.of k) (CharacterLattice.wa w) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom (CommRingCat.of k) A F) :=
      IsFractionRing.injective A F
    exact (AddMonoidAlgebra.basis Λ (CommRingCat.of k)).linearIndependent.map'
      (IsScalarTower.toAlgHom (CommRingCat.of k) A F).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
  have : IsAddTorsionFree Λ := CharacterLattice.isAddTorsionFree w hw
  infer_instance

/-- A split-torus homomorphism with smooth connected full kernel has a free
full quotient of character groups. -/
theorem homKernelLattice_free {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T.toGrp ⟶ Q.toGrp) (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    [Smooth (kernel f).X.hom] [ConnectedSpace (kernel f).X.left] :
    Module.Free ℤ (homKernelLattice f) := by
  let Λ := homKernelLattice f
  have : AddGroup.FG Λ := homKernelLattice_fg f hT
  let e := homKernelDiagonalizableIso f hT hQ
  have : IsIso e.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  have : Smooth (groupScheme (CommRingCat.of k) Λ).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  have : ConnectedSpace (groupScheme (CommRingCat.of k) Λ).X.left :=
    (Scheme.homeoOfIso ((Grp.forget _ ⋙ Over.forget _).mapIso e)).connectedSpace_iff.mp
      (by change ConnectedSpace (kernel f).X.left; infer_instance)
  exact free_of_smooth_connected k Λ

end Diagonalizable

private theorem leftInverse_of_free_quotient
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f)
    [Module.Free ℤ (B ⧸ f.range)] :
    ∃ r : B →+ A, ∀ a, r (f a) = a := by
  let q := (QuotientAddGroup.mk' f.range).toIntLinearMap
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (QuotientAddGroup.mk'_surjective f.range))
  let e := AddMonoidHom.ofInjective hf
  let r₀ : B →+ f.range :=
    { toFun := fun b => ⟨b - s (q b), by
        apply (QuotientAddGroup.eq_zero_iff _).mp
        change q (b - s (q b)) = 0
        rw [map_sub, show q (s (q b)) = q b from LinearMap.congr_fun hs (q b), sub_self]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun b c => by
        apply Subtype.ext
        change (b + c) - s (q (b + c)) = (b - s (q b)) + (c - s (q c))
        simp only [map_add]
        abel }
  refine ⟨e.symm.toAddMonoidHom.comp r₀, fun a => ?_⟩
  have hqa : q (f a) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩
  change e.symm (r₀ (f a)) = a
  apply e.symm_apply_eq.mpr
  apply Subtype.ext
  change f a - s (q (f a)) = f a
  rw [hqa, map_zero, sub_zero]

/-- An epimorphism of split tori with smooth connected actual kernel is
surjective on integral cocharacters. -/
theorem IsSplitTorus.cocharacter_surjective_of_smooth_connected_kernel
    {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q)
    [Epi (CommGroupScheme.groupHom f)]
    [Smooth (kernel (CommGroupScheme.groupHom f)).X.hom]
    [ConnectedSpace (kernel (CommGroupScheme.groupHom f)).X.left] :
    Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f) := by
  let c := characterLattice.comapHom (CommGroupScheme.groupHom f)
  have hc : Function.Injective c := characterRestrict_injective_of_epi
    (CommGroupScheme.groupHom f)
  have : Module.Free ℤ (characterLattice T ⧸ c.range) :=
    Diagonalizable.homKernelLattice_free (CommGroupScheme.groupHom f) hT hQ
  obtain ⟨r, hr⟩ := leftInverse_of_free_quotient c hc
  have : (latticePairing T).IsPerfPair := CocharacterUniformizer.latticePairing_isPerfPair k T hT
  intro ν'
  let F : characterLattice T →ₗ[ℤ] ℤ := ((latticePairing Q).flip ν').comp r.toIntLinearMap
  obtain ⟨ν, hν⟩ := (LinearMap.IsPerfPair.bijective_right (latticePairing T)).surjective F
  refine ⟨ν, ?_⟩
  apply sub_eq_zero.mp
  apply hQ.cocharacter_eq_zero
  intro α
  rw [map_sub, sub_eq_zero]
  have h := LinearMap.congr_fun hν (c α)
  change latticePairing T (c α) ν = latticePairing Q (r (c α)) ν' at h
  rw [hr α] at h
  exact h

/-- A chosen integral lift of a target cocharacter through a split-torus
epimorphism with smooth connected actual kernel. -/
def IsSplitTorus.cocharacterLiftOfSmoothConnectedKernel
    {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q)
    [Epi (CommGroupScheme.groupHom f)]
    [Smooth (kernel (CommGroupScheme.groupHom f)).X.hom]
    [ConnectedSpace (kernel (CommGroupScheme.groupHom f)).X.left]
    (ν' : cocharacterLattice Q) : cocharacterLattice T :=
  Classical.choose (hT.cocharacter_surjective_of_smooth_connected_kernel hQ f ν')

/-- The chosen integral lift maps to the specified target cocharacter. -/
@[simp]
theorem IsSplitTorus.cocharacterLiftOfSmoothConnectedKernel_comp
    {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp) (f : T ⟶ Q)
    [Epi (CommGroupScheme.groupHom f)]
    [Smooth (kernel (CommGroupScheme.groupHom f)).X.hom]
    [ConnectedSpace (kernel (CommGroupScheme.groupHom f)).X.left]
    (ν' : cocharacterLattice Q) :
    hT.cocharacterLiftOfSmoothConnectedKernel hQ f ν' ≫ f = ν' :=
  Classical.choose_spec (hT.cocharacter_surjective_of_smooth_connected_kernel hQ f ν')

end Langlands.GroupScheme
