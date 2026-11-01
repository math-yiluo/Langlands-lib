import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Classification.FiniteLengthProof

/-! Exact finite-length K0 under continuous equivalences of acting groups. -/

noncomputable section

namespace Langlands.SmoothRep

universe uG uH uJ uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {J : Type uJ} [Group J] [TopologicalSpace J]

/-- Pullback along a group equivalence preserves finite group-algebra length. -/
theorem pullbackFunctor_preservesFiniteLength (e : H ≃ₜ* G) :
    PreservesFiniteLength (pullbackFunctor.{uG, uH, uV} e) := by
  intro A hA
  exact (FiniteLengthAssembly.finiteLength_comp_surjective_iff
    A.representation e.toMonoidHom e.surjective).mp hA

/-- Pullback retains the linear maps, hence every actual short exact sequence. -/
theorem pullbackFunctor_preservesShortExact (e : H ≃ₜ* G) :
    PreservesFiniteLengthShortExact (pullbackFunctor.{uG, uH, uV} e) := by
  intro A B C f g _ _ _ h
  exact h

namespace FiniteLengthGrothendieckGroup

/-- Contravariant change of acting group on the full exact finite-length K0. -/
def pullback (e : H ≃ₜ* G) :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uH, uV} ℂ H :=
  map (pullbackFunctor e) (pullbackFunctor_preservesFiniteLength e)
    (pullbackFunctor_preservesShortExact e)

/-- The image is the class of the literal smooth pullback, for any length proof. -/
theorem pullback_ofRepresentation (e : H ≃ₜ* G)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength)
    (hOut : (SmoothRep.pullback e A).HasFiniteLength) :
    pullback e (ofRepresentation A hA) =
      ofRepresentation (SmoothRep.pullback e A) hOut :=
  map_ofRepresentation _ _ _ A hA

/-- Identity pullback is the identity on every virtual class. -/
theorem pullback_refl :
    pullback (ContinuousMulEquiv.refl G) =
      LinearMap.id (R := ℤ) (M := FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G) := by
  apply hom_ext_object ℂ G
  intro A
  change pullback _ (ofRepresentation A.val A.property) = ofRepresentation A.val A.property
  rw [pullback_ofRepresentation _ _ _ (pullbackFunctor_preservesFiniteLength _ _ A.property)]
  exact ofRepresentation_eq_of_equiv _ _
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A.val) (fun _ => rfl))

/-- Composing group equivalences reverses the order of their K0 pullbacks. -/
theorem pullback_trans (e : H ≃ₜ* G) (f : J ≃ₜ* H) :
    pullback (f.trans e) = (pullback.{uH, uJ, uV} f).comp (pullback e) := by
  apply hom_ext_object ℂ G
  intro A
  change pullback _ (ofRepresentation A.val A.property) =
    pullback f (pullback e (ofRepresentation A.val A.property))
  have hE : (SmoothRep.pullback e A.val).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e A.val A.property
  have hF : (SmoothRep.pullback f (SmoothRep.pullback e A.val)).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength f (SmoothRep.pullback e A.val) hE
  have hComp : (SmoothRep.pullback (f.trans e) A.val).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength (f.trans e) A.val A.property
  rw [pullback_ofRepresentation (f.trans e) A.val A.property hComp,
    pullback_ofRepresentation e A.val A.property hE,
    pullback_ofRepresentation f (SmoothRep.pullback e A.val) hE hF]
  exact ofRepresentation_eq_of_equiv _ _
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A.val) (fun _ => rfl))

/-- Pullback by the inverse group equivalence undoes pullback on all classes. -/
theorem pullback_symm_comp (e : H ≃ₜ* G) :
    (pullback.{uH, uG, uV} e.symm).comp (pullback e) =
      LinearMap.id (R := ℤ) (M := FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G) := by
  apply hom_ext_object ℂ G
  intro A
  change pullback e.symm (pullback e (ofRepresentation A.val A.property)) =
    ofRepresentation A.val A.property
  have hE : (SmoothRep.pullback e A.val).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e A.val A.property
  have hInv : (SmoothRep.pullback e.symm (SmoothRep.pullback e A.val)).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e.symm (SmoothRep.pullback e A.val) hE
  rw [pullback_ofRepresentation e A.val A.property hE,
    pullback_ofRepresentation e.symm (SmoothRep.pullback e A.val) hE hInv]
  exact ofRepresentation_eq_of_equiv _ _
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A.val) (fun g => by
      ext v
      change A.val.representation (e (e.symm g)) v = A.val.representation g v
      rw [e.apply_symm_apply]))

/-- Continuous group equivalences induce integer-linear equivalences of exact K0. -/
def pullbackEquiv (e : H ≃ₜ* G) :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G ≃ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uH, uV} ℂ H where
  toLinearMap := pullback e
  invFun := pullback e.symm
  left_inv x := LinearMap.congr_fun (pullback_symm_comp e) x
  right_inv x := LinearMap.congr_fun (pullback_symm_comp e.symm) x

@[simp]
theorem pullbackEquiv_toLinearMap (e : H ≃ₜ* G) :
    (pullbackEquiv.{uG, uH, uV} e).toLinearMap = pullback e := rfl

@[simp]
theorem pullbackEquiv_symm (e : H ≃ₜ* G) :
    (pullbackEquiv.{uG, uH, uV} e).symm = pullbackEquiv e.symm := rfl

end FiniteLengthGrothendieckGroup
end Langlands.SmoothRep
