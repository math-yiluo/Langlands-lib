import Langlands.Algebra.HopfPointTwist
import Langlands.Algebra.HopfPointKernel
import Langlands.Algebra.HopfPointWindowExtension
import Langlands.Algebra.InvariantPrincipalOpen

/-! # The universal Hopf point of `μ_m^r` and its twisting action -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.TorusChartAlgebra

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (r : Type u) [Fintype r] (m : ℕ) [NeZero m]

/-- The representing algebra of homomorphisms `μ_m^r → Spec A`. -/
abbrev W : Type u := HomAlgebra R A (AddMonoidAlgebra R (r → ZMod m))

/-- The universal Hopf point `A → W[(ℤ/m)^r]`. -/
def univ : A →ₐ[R] AddMonoidAlgebra (W R A r m) (r → ZMod m) :=
  toGroupAlgebra (universalPoint R A (AddMonoidAlgebra R (r → ZMod m)))

theorem isHopfPoint_univ : IsHopfPoint (univ R A r m) :=
  (isHopfPoint_iff _).mp (isHopfPoint_universalPoint R A _)

/-- The Hopf point classified by an algebra map out of `W`. -/
theorem univ_point {C : Type u} [CommRing C] [Algebra R C] (g : W R A r m →ₐ[R] C) :
    toGroupAlgebra (homEquiv R A (AddMonoidAlgebra R (r → ZMod m)) C g).1 =
      (AddMonoidAlgebra.mapAlgHom (r → ZMod m) g).comp (univ R A r m) := by
  rw [homEquiv_apply, toGroupAlgebra_pushPoint]
  rfl

/-- Twisting the universal point. -/
theorem mapAlgHom_twistHom_comp_univ (γ : (r → ZMod m) →+ (r → ZMod m)) :
    (AddMonoidAlgebra.mapAlgHom (r → ZMod m) (twistHom γ : W R A r m →ₐ[R] W R A r m)).comp
        (univ R A r m) =
      (AddMonoidAlgebra.mapDomainAlgHom R (W R A r m) γ).comp (univ R A r m) := by
  rw [univ, ← toGroupAlgebra_pushPoint, pushPoint_twistHom, toGroupAlgebra_twistPoint]

/-- The Hopf point of a `C`-point `g` of `W`, in group-algebra form. -/
def pointOf {C : Type*} [CommRing C] [Algebra R C] (g : W R A r m →ₐ[R] C) :
    A →ₐ[R] AddMonoidAlgebra C (r → ZMod m) :=
  (AddMonoidAlgebra.mapAlgHom (r → ZMod m) g).comp (univ R A r m)

theorem isHopfPoint_pointOf {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A r m →ₐ[R] C) : IsHopfPoint (pointOf R A r m g) :=
  HopfPointWindowExtension.IsHopfPoint.mapAlgHom g (isHopfPoint_univ R A r m)

/-- Precomposing a point with the twist by `γ` twists its Hopf point by `γ`. -/
theorem pointOf_comp_twistHom {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A r m →ₐ[R] C) (γ : (r → ZMod m) →+ (r → ZMod m)) :
    pointOf R A r m (g.comp (twistHom γ)) =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ).comp (pointOf R A r m g) := by
  have h1 : AddMonoidAlgebra.mapAlgHom (r → ZMod m) (g.comp (twistHom γ)) =
      (AddMonoidAlgebra.mapAlgHom (r → ZMod m) g).comp
        (AddMonoidAlgebra.mapAlgHom (r → ZMod m) (twistHom γ : W R A r m →ₐ[R] W R A r m)) := by
    apply AlgHom.ext
    intro x
    apply AddMonoidAlgebra.coeff_injective
    ext b
    simp [AddMonoidAlgebra.coeff_mapAlgHom]
  rw [pointOf, pointOf, h1, AlgHom.comp_assoc, mapAlgHom_twistHom_comp_univ,
    ← AlgHom.comp_assoc, HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]

/-- Freeness of the twisting action at closed-immersion points over a nonzero ring. -/
theorem twist_injective_of_surjective {C : Type*} [CommRing C] [Algebra R C] [Nontrivial C]
    (g : W R A r m →ₐ[R] C)
    (hsurj : Function.Surjective (HopfPointClosedLocus.scalarExt (pointOf R A r m g)))
    (γ δ : (r → ZMod m) ≃+ (r → ZMod m))
    (h : pointOf R A r m (g.comp (twistHom γ.toAddMonoidHom)) =
      pointOf R A r m (g.comp (twistHom δ.toAddMonoidHom))) : γ = δ := by
  rw [pointOf_comp_twistHom, pointOf_comp_twistHom] at h
  have hid : δ.symm.toAddMonoidHom.comp δ.toAddMonoidHom = AddMonoidHom.id _ := by
    ext x; simp
  have h2 : (AddMonoidAlgebra.mapDomainAlgHom R C (γ.trans δ.symm).toAddMonoidHom).comp
      (pointOf R A r m g) = pointOf R A r m g := by
    have he : (γ.trans δ.symm).toAddMonoidHom = δ.symm.toAddMonoidHom.comp γ.toAddMonoidHom :=
      rfl
    rw [he, AddMonoidAlgebra.mapDomainAlgHom_comp, AlgHom.comp_assoc, h, ← AlgHom.comp_assoc,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp, hid, AddMonoidAlgebra.mapDomainAlgHom_id,
      AlgHom.id_comp]
  have hε := HopfPointKernel.eq_refl_of_mapDomain_comp_eq hsurj (γ.trans δ.symm) h2
  refine AddEquiv.ext fun x => ?_
  have hx := congrArg (fun e => δ (e x)) hε
  simpa using hx

end Langlands.Algebra.TorusChartAlgebra
