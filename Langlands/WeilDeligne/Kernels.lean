import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Invariants

/-!
# Monodromy kernels and their inertia invariants

Covariance implies that the actual kernel of monodromy is stable under the
Weil action. Pair morphisms restrict to this kernel, functorially.
-/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The monodromy kernel, with stability derived from covariance. -/
def kernelSubrepresentation (A : WeilDeligneRepresentation K G ν) :
    Subrepresentation A.representation where
  toSubmodule := A.monodromy.ker
  apply_mem_toSubmodule g {v} hv := by
    change A.monodromy v = 0 at hv
    change A.monodromy (A.representation g v) = 0
    have hi : A.representation g⁻¹ (A.representation g v) = v := by
      change (A.representation g⁻¹ * A.representation g) v = v
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    have h := LinearMap.congr_fun (A.covariance g) (A.representation g v)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
    rw [hi, hv, map_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (Units.ne_zero _)

/-- The actual finite-dimensional representation on the kernel of monodromy. -/
def kernelRepresentation (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    FiniteRepresentation.{uK, uG, uV} K G :=
  FiniteRepresentation.of A.kernelSubrepresentation.toRepresentation

/-- The inclusion of the monodromy kernel into the underlying Weil representation. -/
def kernelInclusion (A : WeilDeligneRepresentation K G ν) :
    A.kernelRepresentation.representation.IntertwiningMap A.representation :=
  ⟨A.monodromy.ker.subtype, fun _ => rfl⟩

/-- A morphism of pairs restricts to an intertwiner of their monodromy kernels. -/
def kernelMap {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    A.kernelRepresentation.representation.IntertwiningMap
      B.kernelRepresentation.representation where
  toLinearMap :=
    (f.intertwiner.toLinearMap.comp A.monodromy.ker.subtype).codRestrict B.monodromy.ker
      fun x => by
        have h := LinearMap.congr_fun f.comm_monodromy x.val
        change f.intertwiner (A.monodromy x.val) = B.monodromy (f.intertwiner x.val) at h
        change B.monodromy (f.intertwiner x.val) = 0
        rw [← h, x.property, map_zero]
  isIntertwining' g := by
    ext x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ f.intertwiner g x.val

/-- Taking the kernel of monodromy is a functor to finite Weil representations. -/
def kernelFunctor : WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
    FiniteRepresentation.{uK, uG, uV} K G where
  obj := kernelRepresentation
  map f := (FiniteRepresentation.homEquiv _ _).symm (kernelMap f)
  map_id A := by
    apply (FiniteRepresentation.homEquiv _ _).injective
    ext x
    rfl
  map_comp f g := by
    apply (FiniteRepresentation.homEquiv _ _).injective
    ext x
    rfl

/-- Pair isomorphisms induce actual equivalences on their monodromy kernels. -/
def kernelEquiv {A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν} (e : Equiv A B) :
    FiniteRepresentation.Equiv A.kernelRepresentation B.kernelRepresentation :=
  FiniteRepresentation.equivOfIso (kernelFunctor.mapIso e.toIso)

/-- Monodromy kernels descend to genuine isomorphism classes. -/
def kernelClass : IsomorphismClasses.{uK, uG, uV} K G ν →
    FiniteRepresentation.IsomorphismClasses.{uK, uG, uV} K G :=
  Quotient.map kernelRepresentation (fun _ _ ⟨e⟩ => ⟨kernelEquiv e⟩)

/-- The finite-dimensional representation on the inertia-fixed monodromy kernel. -/
def inertiaKernelRepresentation (I : Subgroup G) [I.Normal]
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    FiniteRepresentation.{uK, uG, uV} K G :=
  FiniteRepresentation.invariants I A.kernelRepresentation

/-- The full inertia-fixed monodromy-kernel construction is functorial. -/
def inertiaKernelFunctor (I : Subgroup G) [I.Normal] :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
      FiniteRepresentation.{uK, uG, uV} K G :=
  kernelFunctor ⋙ FiniteRepresentation.invariantsFunctor I

/-- Its action on isomorphism classes is well defined. -/
def inertiaKernelClass (I : Subgroup G) [I.Normal] :
    IsomorphismClasses.{uK, uG, uV} K G ν →
      FiniteRepresentation.IsomorphismClasses.{uK, uG, uV} K G :=
  FiniteRepresentation.invariantsClass I ∘ kernelClass

end Langlands.WeilDeligneRepresentation
