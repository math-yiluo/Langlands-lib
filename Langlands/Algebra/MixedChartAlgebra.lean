import Langlands.Algebra.HopfPointTwist
import Langlands.Algebra.HopfPointKernel
import Langlands.Algebra.HopfPointWindowExtension
import Langlands.Algebra.InvariantPrincipalOpen

/-! # The universal Hopf point of a finite diagonalizable group and its twisting action -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.MixedChartAlgebra

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (L : Type u) [AddCommGroup L] [Fintype L]

/-- The representing algebra of homomorphisms `D(L) → Spec A`, for a finite abelian
group `L`. -/
abbrev W : Type u := HomAlgebra R A (AddMonoidAlgebra R L)

/-- The universal Hopf point `A → W[L]`. -/
def univ : A →ₐ[R] AddMonoidAlgebra (W R A L) L :=
  toGroupAlgebra (universalPoint R A (AddMonoidAlgebra R L))

theorem isHopfPoint_univ : IsHopfPoint (univ R A L) :=
  (isHopfPoint_iff _).mp (isHopfPoint_universalPoint R A _)

/-- The Hopf point classified by an algebra map out of `W`. -/
theorem univ_point {C : Type u} [CommRing C] [Algebra R C] (g : W R A L →ₐ[R] C) :
    toGroupAlgebra (homEquiv R A (AddMonoidAlgebra R L) C g).1 =
      (AddMonoidAlgebra.mapAlgHom L g).comp (univ R A L) := by
  rw [homEquiv_apply, toGroupAlgebra_pushPoint]
  rfl

/-- Twisting the universal point. -/
theorem mapAlgHom_twistHom_comp_univ (γ : L →+ L) :
    (AddMonoidAlgebra.mapAlgHom L (twistHom γ : W R A L →ₐ[R] W R A L)).comp (univ R A L) =
      (AddMonoidAlgebra.mapDomainAlgHom R (W R A L) γ).comp (univ R A L) := by
  rw [univ, ← toGroupAlgebra_pushPoint, pushPoint_twistHom, toGroupAlgebra_twistPoint]

/-- The Hopf point of a `C`-point `g` of `W`, in group-algebra form. -/
def pointOf {C : Type*} [CommRing C] [Algebra R C] (g : W R A L →ₐ[R] C) :
    A →ₐ[R] AddMonoidAlgebra C L :=
  (AddMonoidAlgebra.mapAlgHom L g).comp (univ R A L)

theorem isHopfPoint_pointOf {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A L →ₐ[R] C) : IsHopfPoint (pointOf R A L g) :=
  HopfPointWindowExtension.IsHopfPoint.mapAlgHom g (isHopfPoint_univ R A L)

/-- Precomposing a point with the twist by `γ` twists its Hopf point by `γ`. -/
theorem pointOf_comp_twistHom {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A L →ₐ[R] C) (γ : L →+ L) :
    pointOf R A L (g.comp (twistHom γ)) =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ).comp (pointOf R A L g) := by
  have h1 : AddMonoidAlgebra.mapAlgHom L (g.comp (twistHom γ)) =
      (AddMonoidAlgebra.mapAlgHom L g).comp
        (AddMonoidAlgebra.mapAlgHom L (twistHom γ : W R A L →ₐ[R] W R A L)) := by
    apply AlgHom.ext
    intro x
    apply AddMonoidAlgebra.coeff_injective
    ext b
    simp [AddMonoidAlgebra.coeff_mapAlgHom]
  rw [pointOf, pointOf, h1, AlgHom.comp_assoc, mapAlgHom_twistHom_comp_univ,
    ← AlgHom.comp_assoc, HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]

/-- Freeness of the twisting action at closed-immersion points over a nonzero ring. -/
theorem twist_injective_of_surjective {C : Type*} [CommRing C] [Algebra R C] [Nontrivial C]
    (g : W R A L →ₐ[R] C)
    (hsurj : Function.Surjective (HopfPointClosedLocus.scalarExt (pointOf R A L g)))
    (γ δ : L ≃+ L)
    (h : pointOf R A L (g.comp (twistHom γ.toAddMonoidHom)) =
      pointOf R A L (g.comp (twistHom δ.toAddMonoidHom))) : γ = δ := by
  rw [pointOf_comp_twistHom, pointOf_comp_twistHom] at h
  have hid : δ.symm.toAddMonoidHom.comp δ.toAddMonoidHom = AddMonoidHom.id _ := by
    ext x; simp
  have h2 : (AddMonoidAlgebra.mapDomainAlgHom R C (γ.trans δ.symm).toAddMonoidHom).comp
      (pointOf R A L g) = pointOf R A L g := by
    have he : (γ.trans δ.symm).toAddMonoidHom = δ.symm.toAddMonoidHom.comp γ.toAddMonoidHom :=
      rfl
    rw [he, AddMonoidAlgebra.mapDomainAlgHom_comp, AlgHom.comp_assoc, h, ← AlgHom.comp_assoc,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp, hid, AddMonoidAlgebra.mapDomainAlgHom_id,
      AlgHom.id_comp]
  have hε := HopfPointKernel.eq_refl_of_mapDomain_comp_eq hsurj (γ.trans δ.symm) h2
  refine AddEquiv.ext fun x => ?_
  have hx := congrArg (fun e => δ (e x)) hε
  simpa using hx

end Langlands.Algebra.MixedChartAlgebra
