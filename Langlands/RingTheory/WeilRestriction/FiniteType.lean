import Langlands.TauCeti.RingTheory.WeilRestriction.Basic

noncomputable section

open Algebra TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Present an algebra by a given generating family and all elements of its kernel. -/
def presentationOfKernel (G : Generators R S ι) : Presentation R S ι G.ker where
  toGenerators := G
  relation := Subtype.val
  span_range_relation_eq_ker := by
    rw [Subtype.range_coe_subtype]
    exact Ideal.span_eq (I := G.ker)

end Algebra.Generators

namespace Langlands.Algebra

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FiniteType B C]

namespace WeilRestrictionFiniteType

/-- The size of a chosen finite generating family for the input algebra. -/
def generatorsCount : ℕ :=
  (FiniteType.iff_exists_generators.mp (inferInstance : FiniteType B C)).choose

/-- A chosen finite generating family, without a finite-relation assumption. -/
def generators : Generators B C (Fin (generatorsCount B C)) :=
  (FiniteType.iff_exists_generators.mp (inferInstance : FiniteType B C)).choose_spec.some

end WeilRestrictionFiniteType

/-- The actual finite-type affine Weil-restriction algebra along a finite projective algebra. -/
def WeilRestrictionFiniteType : Type _ :=
  TauCeti.Algebra.WeilRestriction.OfPresentation A B
    (WeilRestrictionFiniteType.generators B C).presentationOfKernel
deriving CommRing, Algebra A

namespace WeilRestrictionFiniteType

instance : FiniteType A (WeilRestrictionFiniteType A B C) :=
  inferInstanceAs (FiniteType A (TauCeti.Algebra.WeilRestriction.OfPresentation A B
    (generators B C).presentationOfKernel))

/-- The universal tensor-valued point of the finite-type construction. -/
def universalPoint : C →ₐ[B] B ⊗[A] WeilRestrictionFiniteType A B C :=
  TauCeti.Algebra.WeilRestriction.OfPresentation.universalPoint A B _

variable (T : Type*) [CommRing T] [Algebra A T]

/-- The representing bijection for actual tensor-valued points. -/
def homEquiv : (WeilRestrictionFiniteType A B C →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) :=
  TauCeti.Algebra.WeilRestriction.OfPresentation.homEquiv A B _ T

variable {A B C T}

@[simp]
theorem homEquiv_apply (g : WeilRestrictionFiniteType A B C →ₐ[A] T) :
    homEquiv A B C T g =
      (Algebra.TensorProduct.lTensor B g).comp (universalPoint A B C) := rfl

/-- Naturality of the representing bijection in the test algebra. -/
theorem homEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T']
    (g : WeilRestrictionFiniteType A B C →ₐ[A] T) (h : T →ₐ[A] T') :
    homEquiv A B C T' (h.comp g) =
      (Algebra.TensorProduct.lTensor B h).comp (homEquiv A B C T g) := by
  simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc]

/-- Maps out of the representing algebra are determined by the universal point. -/
@[ext]
theorem hom_ext {g₁ g₂ : WeilRestrictionFiniteType A B C →ₐ[A] T}
    (h : (Algebra.TensorProduct.lTensor B g₁).comp (universalPoint A B C) =
      (Algebra.TensorProduct.lTensor B g₂).comp (universalPoint A B C)) : g₁ = g₂ :=
  (homEquiv A B C T).injective <| by simpa using h

variable (A B C)

/-- Agreement with the published finite-presentation Weil restriction on its full domain. -/
def finitePresentationAlgEquiv [FinitePresentation B C] :
    WeilRestrictionFiniteType A B C ≃ₐ[A] TauCeti.Algebra.WeilRestriction A B C :=
  AlgEquiv.ofAlgHom
    ((homEquiv A B C _).symm (TauCeti.Algebra.WeilRestriction.universalPoint A B C))
    ((TauCeti.Algebra.WeilRestriction.homEquiv A B C _).symm (universalPoint A B C))
    (TauCeti.Algebra.WeilRestriction.hom_ext <| by
      simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc, ← homEquiv_apply,
        ← TauCeti.Algebra.WeilRestriction.homEquiv_apply])
    (hom_ext <| by
      simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc, ← homEquiv_apply,
        ← TauCeti.Algebra.WeilRestriction.homEquiv_apply])

/-- The comparison carries the finite-type universal point to the existing universal point. -/
theorem finitePresentationAlgEquiv_universalPoint [FinitePresentation B C] :
    (Algebra.TensorProduct.lTensor B (finitePresentationAlgEquiv A B C).toAlgHom).comp
        (universalPoint A B C) = TauCeti.Algebra.WeilRestriction.universalPoint A B C := by
  change homEquiv A B C _ ((homEquiv A B C _).symm _) = _
  exact Equiv.apply_symm_apply _ _

variable {A B C}

/-- The algebra comparison identifies the two actual point bijections for every test algebra. -/
theorem homEquiv_comp_finitePresentationAlgEquiv [FinitePresentation B C]
    (g : TauCeti.Algebra.WeilRestriction A B C →ₐ[A] T) :
    homEquiv A B C T (g.comp (finitePresentationAlgEquiv A B C).toAlgHom) =
      TauCeti.Algebra.WeilRestriction.homEquiv A B C T g := by
  rw [homEquiv_comp]
  change (Algebra.TensorProduct.lTensor B g).comp
      (homEquiv A B C _ ((homEquiv A B C _).symm _)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end WeilRestrictionFiniteType
end Langlands.Algebra
