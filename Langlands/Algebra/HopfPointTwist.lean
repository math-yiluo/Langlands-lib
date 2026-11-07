import Langlands.Algebra.HopfPointBridge
import Mathlib.Algebra.Group.End

/-! # Twisting Hopf points by automorphisms of the character group -/

noncomputable section

universe u v

open TensorProduct

namespace Langlands.Algebra.HopfPointTwist

open HopfPointExtension HopfPointBridge FiniteBialgebraHom

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Bialgebra R A]
  {M : Type u} [AddCommGroup M]

section Points

variable {C : Type v} [CommRing C] [Algebra R C]

/-- Twist a point `A → C ⊗[R] R[M]` by an endomorphism of `M`. -/
def twistPoint (γ : M →+ M) (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M :=
  (Algebra.TensorProduct.map (AlgHom.id R C) (AddMonoidAlgebra.mapDomainAlgHom R R γ)).comp f

theorem scalarMap_comp_map_mapDomain (γ : M →+ M) :
    (scalarMap R C M).comp
        (Algebra.TensorProduct.map (AlgHom.id R C) (AddMonoidAlgebra.mapDomainAlgHom R R γ)) =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ).comp (scalarMap R C M) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
      scalarMap_tmul_single]

theorem toGroupAlgebra_twistPoint (γ : M →+ M) (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    toGroupAlgebra (twistPoint γ f) =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ).comp (toGroupAlgebra f) := by
  rw [toGroupAlgebra, twistPoint, ← AlgHom.comp_assoc, scalarMap_comp_map_mapDomain,
    AlgHom.comp_assoc]

theorem isHopfPoint_twistPoint (γ : M →+ M) {f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M}
    (hf : FiniteBialgebraHom.IsHopfPoint R f) :
    FiniteBialgebraHom.IsHopfPoint R (twistPoint γ f) := by
  rw [isHopfPoint_iff, toGroupAlgebra_twistPoint]
  exact ((isHopfPoint_iff f).mp hf).mapDomain γ

theorem pushPoint_twistPoint {D : Type*} [CommRing D] [Algebra R D] (g : C →ₐ[R] D)
    (γ : M →+ M) (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    pushPoint R g (twistPoint γ f) = twistPoint γ (pushPoint R g f) := by
  simp only [pushPoint, twistPoint, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id, AlgHom.id_comp]

theorem twistPoint_twistPoint (γ δ : M →+ M) (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    twistPoint γ (twistPoint δ f) = twistPoint (γ.comp δ) f := by
  simp only [twistPoint, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id, AddMonoidAlgebra.mapDomainAlgHom_comp]

theorem twistPoint_id (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    twistPoint (AddMonoidHom.id M) f = f := by
  simp only [twistPoint, AddMonoidAlgebra.mapDomainAlgHom_id, Algebra.TensorProduct.map_id,
    AlgHom.id_comp]

end Points

section Action

variable [Module.Finite R (AddMonoidAlgebra R M)] [Module.Free R (AddMonoidAlgebra R M)]
  [Algebra.FinitePresentation R A]

local notation "W" => HomAlgebra R A (AddMonoidAlgebra R M)

/-- The algebra endomorphism of the representing algebra induced by twisting the
universal Hopf point by `γ`. -/
def twistHom (γ : M →+ M) : W →ₐ[R] W :=
  (homEquiv R A (AddMonoidAlgebra R M) W).symm
    ⟨twistPoint γ (universalPoint R A (AddMonoidAlgebra R M)),
      isHopfPoint_twistPoint γ (isHopfPoint_universalPoint R A _)⟩

theorem homEquiv_twistHom (γ : M →+ M) :
    (homEquiv R A (AddMonoidAlgebra R M) W (twistHom γ)).1 =
      twistPoint γ (universalPoint R A (AddMonoidAlgebra R M)) := by
  simp only [twistHom, Equiv.apply_symm_apply]

theorem pushPoint_twistHom (γ : M →+ M) :
    pushPoint R (twistHom γ) (universalPoint R A (AddMonoidAlgebra R M)) =
      twistPoint γ (universalPoint R A (AddMonoidAlgebra R M)) := by
  rw [← homEquiv_apply, homEquiv_twistHom]

/-- On points, `twistHom γ` twists by `γ`. -/
theorem homEquiv_comp_twistHom {C : Type u} [CommRing C] [Algebra R C] (γ : M →+ M)
    (g : W →ₐ[R] C) :
    (homEquiv R A (AddMonoidAlgebra R M) C (g.comp (twistHom γ))).1 =
      twistPoint γ (homEquiv R A (AddMonoidAlgebra R M) C g).1 := by
  rw [homEquiv_apply, homEquiv_apply, ← pushPoint_pushPoint, pushPoint_twistHom,
    pushPoint_twistPoint]

theorem twistHom_comp (γ δ : M →+ M) :
    (twistHom γ).comp (twistHom δ) = (twistHom (δ.comp γ) : W →ₐ[R] W) := by
  apply (homEquiv R A (AddMonoidAlgebra R M) W).injective
  apply Subtype.ext
  rw [homEquiv_comp_twistHom, homEquiv_twistHom, homEquiv_twistHom, twistPoint_twistPoint]

theorem twistHom_id : (twistHom (AddMonoidHom.id M) : W →ₐ[R] W) = AlgHom.id R W := by
  apply (homEquiv R A (AddMonoidAlgebra R M) W).injective
  apply Subtype.ext
  rw [homEquiv_twistHom, twistPoint_id, homEquiv_apply, pushPoint_id]

/-- The algebra automorphism induced by an automorphism of `M`. -/
def twistEquiv (γ : M ≃+ M) : W ≃ₐ[R] W :=
  AlgEquiv.ofAlgHom (twistHom γ.toAddMonoidHom) (twistHom γ.symm.toAddMonoidHom)
    (by rw [twistHom_comp]; convert twistHom_id; ext; simp)
    (by rw [twistHom_comp]; convert twistHom_id; ext; simp)

theorem twistEquiv_apply (γ : M ≃+ M) (w : W) :
    twistEquiv γ w = twistHom γ.toAddMonoidHom w := rfl

/-- The action of the automorphism group of `M` (written multiplicatively) on the
representing algebra; `γ` acts by twisting with `γ⁻¹`, so that this is a group
homomorphism. -/
def twistAction : Multiplicative (AddAut M) →* (W ≃ₐ[R] W) where
  toFun γ := twistEquiv (-(Multiplicative.toAdd γ))
  map_one' := by
    apply AlgEquiv.ext
    intro w
    change twistHom (AddMonoidHom.id M) w = w
    rw [twistHom_id]
    rfl
  map_mul' γ δ := by
    apply AlgEquiv.ext
    intro w
    change twistHom (-(Multiplicative.toAdd (γ * δ)) : AddAut M).toAddMonoidHom w =
      twistHom (-(Multiplicative.toAdd γ) : AddAut M).toAddMonoidHom
        (twistHom (-(Multiplicative.toAdd δ) : AddAut M).toAddMonoidHom w)
    rw [← AlgHom.comp_apply, twistHom_comp]
    congr 2

end Action

end Langlands.Algebra.HopfPointTwist
