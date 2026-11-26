import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension

/-! # The identity extension of a presented affinoid algebra -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private def fromIdentityExtension (A : PresentedAffinoidAlgebra K) :
    BoundedAlgHom K (algebra K K A) A :=
  lift K K A A (BoundedAlgHom.id K A)

private theorem fromIdentityExtension_iota (A : PresentedAffinoidAlgebra K) (a : A) :
    fromIdentityExtension K A (iota K K A a) = a :=
  lift_iota K K A A (BoundedAlgHom.id K A) a

private theorem iota_fromIdentityExtension (A : PresentedAffinoidAlgebra K) (x : algebra K K A) :
    iota K K A (fromIdentityExtension K A x) = x := by
  let F : BoundedAlgHom K (algebra K K A) (algebra K K A) :=
    (iota K K A).comp (fromIdentityExtension K A)
  have h : F = BoundedAlgHom.id K (algebra K K A) := by
    apply hom_ext_coordinate K _ _
    intro (i : Fin A.arity)
    have hi := iota_coordinate K K A i
    change iota K K A (fromIdentityExtension K A (coordinate K (algebra K K A) i)) =
      coordinate K (algebra K K A) i
    refine (congrArg (iota K K A) ?_).trans hi
    exact (congrArg (fromIdentityExtension K A) hi.symm).trans
      (fromIdentityExtension_iota K A (coordinate K A i))
  exact congrArg (fun f : BoundedAlgHom K (algebra K K A) (algebra K K A) => f x) h

/-- The structural map to the identity extension is a bounded algebra equivalence. -/
def unitEquiv (A : PresentedAffinoidAlgebra K) : BoundedAlgEquiv K A (algebra K K A) :=
  BoundedAlgEquiv.ofHomInv (iota K K A) (fromIdentityExtension K A)
    (fromIdentityExtension_iota K A) (iota_fromIdentityExtension K A)

@[simp] theorem unitEquiv_apply (A : PresentedAffinoidAlgebra K) (a : A) :
    unitEquiv K A a = iota K K A a := rfl

/-- The comparison identifies each scalar-extended chart spectrum with its original spectrum. -/
def unitSpectrumHomeomorph (A : PresentedAffinoidAlgebra K) :
    BanachSpectrum (algebra K K A) ≃ₜ BanachSpectrum A :=
  (unitEquiv K A).spectrumHomeomorph

@[simp] theorem unitSpectrumHomeomorph_apply (A : PresentedAffinoidAlgebra K)
    (x : BanachSpectrum (algebra K K A)) :
    unitSpectrumHomeomorph K A x = spectrumProjection K K A x := rfl

/-- The genuine identity extension of presented affinoid algebras is naturally
isomorphic to the identity on every bounded arrow. -/
def unitNatIso : 𝟭 (PresentedAffinoidAlgebra K) ≅ functor (K := K) (L := K) :=
  NatIso.ofComponents (fun A => {
    hom := (unitEquiv K A).toBoundedAlgHom
    inv := (unitEquiv K A).symm.toBoundedAlgHom
    hom_inv_id := BoundedAlgHom.ext (fromIdentityExtension_iota K A)
    inv_hom_id := BoundedAlgHom.ext (iota_fromIdentityExtension K A) }) (fun {_ _} f => by
      apply BoundedAlgHom.ext
      intro x
      exact (map_iota (K := K) (L := K) f x).symm)

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
