import Langlands.Representation.Smooth.Transfer.GroupEquivalence
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-!
# Compact-coefficient classes under topological group equivalences

Internal same-carrier constructions, with contravariant action `h ↦ ρ (e h)`.
The smooth algebraic dual, compact support, and actual isomorphism quotient are
transported without admissibility or finite-dimensionality hypotheses.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uH uJ uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {J : Type uJ} [Group J] [TopologicalSpace J]

section Actions

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] [TopologicalSpace H] in
/-- Coefficients of the pulled-back action are precomposed with the group map. -/
theorem matrixCoefficient_comp_monoidHom (ρ : Representation ℂ G V)
    (f : H →* G) (ℓ : Module.Dual ℂ V) (v : V) :
    matrixCoefficient (ρ.comp f) ℓ v = matrixCoefficient ρ ℓ v ∘ f := rfl

/-- Compact smooth-dual coefficients are invariant under topological group equivalence. -/
theorem hasCompactSmoothDualCoefficients_comp_continuousMulEquiv_iff
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    HasCompactSmoothDualCoefficients (ρ.comp e.toMonoidHom) ↔
      HasCompactSmoothDualCoefficients ρ := by
  have forward (ρ : Representation ℂ G V) (e : H ≃ₜ* G)
      (hρ : HasCompactSmoothDualCoefficients ρ) :
      HasCompactSmoothDualCoefficients (ρ.comp e.toMonoidHom) := by
    intro v ℓ hℓ
    exact (hρ v ℓ
      ((isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ).mp hℓ)).comp_homeomorph
        e.toHomeomorph
  constructor
  · intro hρ v ℓ hℓ
    have h := hρ v ℓ
      ((isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ).mpr hℓ)
    have h' := h.comp_homeomorph e.symm.toHomeomorph
    have heq : matrixCoefficient (ρ.comp e.toMonoidHom) ℓ v ∘ e.symm.toHomeomorph =
        matrixCoefficient ρ ℓ v := by
      funext g
      change ℓ (ρ (e (e.symm g)) v) = ℓ (ρ g v)
      rw [e.apply_symm_apply]
    rwa [heq] at h'
  · exact forward ρ e

/-- Irreducibility is invariant under the surjective change of group. -/
theorem isIrreducible_comp_continuousMulEquiv_iff
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) ↔
      Representation.IsIrreducible ρ := by
  constructor
  · intro h
    let := h
    have h' := CuspidalSupport.isIrreducible_comp_of_surjective
      (ρ.comp e.toMonoidHom) e.symm.toMonoidHom e.symm.surjective
    have heq : (ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ρ := by
      ext g v
      change ρ (e (e.symm g)) v = ρ g v
      rw [e.apply_symm_apply]
    rwa [heq] at h'
  · intro h
    let := h
    exact CuspidalSupport.isIrreducible_comp_of_surjective ρ e.toMonoidHom e.surjective

namespace SmoothRep

/-- Intertwiners pull back by keeping the same linear map, across carrier universes. -/
def pullbackMap (e : H ≃ₜ* G) {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) :
    Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (e h)

@[simp]
theorem pullbackMap_toLinearMap (e : H ≃ₜ* G)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) :
    (pullbackMap e f).toLinearMap = f.toLinearMap := rfl

/-- Equivariant linear equivalences pull back with their original linear equivalence. -/
def pullbackEquiv (e : H ≃ₜ* G) {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.Equiv σ) : Representation.Equiv (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) :=
  CuspidalSupport.equivComp f e.toMonoidHom

@[simp]
theorem pullbackEquiv_toLinearEquiv (e : H ≃ₜ* G)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.Equiv σ) :
    (pullbackEquiv e f).toLinearEquiv = f.toLinearEquiv := rfl

end SmoothRep
end Actions

namespace SmoothRep

/-- Bundled smooth pullback on the same vector space. -/
def pullback (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    SmoothRep.{0, uH, uV} ℂ H :=
  of (A.representation.comp e.toMonoidHom)
    (isSmooth_comp e.toMonoidHom e.continuous A.isSmooth)

@[simp]
theorem pullback_representation (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    (pullback e A).representation = A.representation.comp e.toMonoidHom := rfl

/-- Smooth pullback is functorial on actual intertwiners. -/
def pullbackFunctor (e : H ≃ₜ* G) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H where
  obj := pullback e
  map f := ofHom (pullbackMap e (hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

end SmoothRep

namespace IrreducibleCompactCoefficientRep

/-- Pull back an actual compact-coefficient irreducible smooth representative. -/
def pullback (e : H ≃ₜ* G) (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    IrreducibleCompactCoefficientRep.{uH, uV} H :=
  ⟨SmoothRep.pullback e A.obj,
    (isIrreducible_comp_continuousMulEquiv_iff A.obj.representation e).mpr A.property.1,
    (hasCompactSmoothDualCoefficients_comp_continuousMulEquiv_iff
      A.obj.representation e).mpr A.property.2⟩

@[simp]
theorem pullback_apply (e : H ≃ₜ* G) (A : IrreducibleCompactCoefficientRep.{uG, uV} G)
    (h : H) (v : A.obj) :
    (pullback e A).obj.representation h v = A.obj.representation (e h) v := rfl

/-- Isomorphisms of actual representatives pull back to actual isomorphisms. -/
def pullbackIso (e : H ≃ₜ* G) {A B : IrreducibleCompactCoefficientRep.{uG, uV} G}
    (f : A ≅ B) : pullback e A ≅ pullback e B :=
  ObjectProperty.isoMk _ ((SmoothRep.pullbackFunctor e).mapIso
    ((irreducibleCompactCoefficientProperty G).ι.mapIso f))

/-- An actual equivariant linear equivalence induces an isomorphism of representatives. -/
def isoOfEquiv {A B : IrreducibleCompactCoefficientRep.{uG, uV} G}
    (f : A.obj.representation.Equiv B.obj.representation) : A ≅ B :=
  ObjectProperty.isoMk _ (SmoothRep.mkIso f)

/-- Pullback by the identity has the identity linear map as its comparison. -/
def pullbackReflIso (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    pullback (ContinuousMulEquiv.refl G) A ≅ A :=
  isoOfEquiv (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun _ => rfl))

/-- For `f : J ≃ₜ* H` and `e : H ≃ₜ* G`, pullback by `f.trans e`
agrees with pullback first by `e`, then by `f`, via the identity linear map. -/
def pullbackTransIso (e : H ≃ₜ* G) (f : J ≃ₜ* H)
    (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    pullback (f.trans e) A ≅ pullback f (pullback e A) :=
  isoOfEquiv (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun _ => rfl))

/-- Pullback followed by inverse pullback has the identity linear comparison. -/
def pullbackSymmIso (e : H ≃ₜ* G) (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    pullback e.symm (pullback e A) ≅ A :=
  isoOfEquiv (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun g => by
    ext v
    change A.obj.representation (e (e.symm g)) v = A.obj.representation g v
    rw [e.apply_symm_apply]))

end IrreducibleCompactCoefficientRep

namespace CompactCoefficientClass

/-- Contravariant transport of the existing quotient, by actual same-carrier pullback. -/
def pullback (e : H ≃ₜ* G) :
    CompactCoefficientClass.{uG, uV} G → CompactCoefficientClass.{uH, uV} H :=
  Quotient.lift (fun A => ofRep (IrreducibleCompactCoefficientRep.pullback e A)) (by
    rintro A B ⟨f⟩
    exact (ofRep_eq_iff _ _).mpr ⟨IrreducibleCompactCoefficientRep.pullbackIso e f⟩)

@[simp]
theorem pullback_ofRep (e : H ≃ₜ* G) (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    pullback e (ofRep A) = ofRep (IrreducibleCompactCoefficientRep.pullback e A) := rfl

/-- Representative independence is witnessed by transport of the actual isomorphism. -/
theorem pullback_ofRep_eq (e : H ≃ₜ* G) {A B : IrreducibleCompactCoefficientRep.{uG, uV} G}
    (h : ofRep A = ofRep B) :
    ofRep (IrreducibleCompactCoefficientRep.pullback e A) =
      ofRep (IrreducibleCompactCoefficientRep.pullback e B) :=
  congrArg (pullback e) h

@[simp]
theorem pullback_refl (a : CompactCoefficientClass.{uG, uV} G) :
    pullback (ContinuousMulEquiv.refl G) a = a := by
  induction a using Quotient.inductionOn with
  | h A =>
      exact (ofRep_eq_iff _ _).mpr ⟨IrreducibleCompactCoefficientRep.pullbackReflIso A⟩

/-- Explicit contravariant composition law. -/
theorem pullback_trans (e : H ≃ₜ* G) (f : J ≃ₜ* H)
    (a : CompactCoefficientClass.{uG, uV} G) :
    pullback (f.trans e) a = pullback f (pullback e a) := by
  induction a using Quotient.inductionOn with
  | h A =>
      exact (ofRep_eq_iff _ _).mpr ⟨IrreducibleCompactCoefficientRep.pullbackTransIso e f A⟩

@[simp]
theorem pullback_symm_pullback (e : H ≃ₜ* G) (a : CompactCoefficientClass.{uG, uV} G) :
    pullback e.symm (pullback e a) = a := by
  induction a using Quotient.inductionOn with
  | h A =>
      exact (ofRep_eq_iff _ _).mpr ⟨IrreducibleCompactCoefficientRep.pullbackSymmIso e A⟩

/-- The equivalence of compact-coefficient classes induced contravariantly by `e`. -/
def pullbackEquiv (e : H ≃ₜ* G) :
    CompactCoefficientClass.{uG, uV} G ≃ CompactCoefficientClass.{uH, uV} H where
  toFun := pullback e
  invFun := pullback e.symm
  left_inv := pullback_symm_pullback e
  right_inv := pullback_symm_pullback e.symm

@[simp]
theorem pullbackEquiv_ofRep (e : H ≃ₜ* G) (A : IrreducibleCompactCoefficientRep.{uG, uV} G) :
    pullbackEquiv e (ofRep A) = ofRep (IrreducibleCompactCoefficientRep.pullback e A) := rfl

@[simp]
theorem pullbackEquiv_symm (e : H ≃ₜ* G) :
    (pullbackEquiv.{uG, uH, uV} e).symm = pullbackEquiv e.symm := rfl

@[simp]
theorem pullbackEquiv_refl :
    pullbackEquiv (ContinuousMulEquiv.refl G) = Equiv.refl (CompactCoefficientClass.{uG, uV} G) :=
  Equiv.ext pullback_refl

/-- Composition of group equivalences reverses the order of class transport. -/
theorem pullbackEquiv_trans (e : H ≃ₜ* G) (f : J ≃ₜ* H) :
    pullbackEquiv (f.trans e) =
      (pullbackEquiv.{uG, uH, uV} e).trans (pullbackEquiv f) :=
  Equiv.ext (pullback_trans e f)

/-- Fixed vectors transport to the actual image subgroup, expressed by inverse comap. -/
theorem hasFixedVector_pullbackEquiv (e : H ≃ₜ* G) (K : Subgroup H)
    (a : CompactCoefficientClass.{uG, uV} G) :
    HasFixedVector K (pullbackEquiv e a) ↔ HasFixedVector (K.comap e.symm.toMonoidHom) a := by
  induction a using Quotient.inductionOn with
  | h A =>
    change fixedVectors (A.obj.representation.comp e.toMonoidHom) K ≠ ⊥ ↔
      fixedVectors A.obj.representation (K.comap e.symm.toMonoidHom) ≠ ⊥
    rw [fixedVectors_comp_mulEquiv A.obj.representation e.toMulEquiv K]
    rfl

/-- Membership in the fixed-subgroup stratum is preserved with the transported subgroup. -/
theorem mem_fixedStratum_pullbackEquiv (e : H ≃ₜ* G) (K : Subgroup H)
    (a : CompactCoefficientClass.{uG, uV} G) :
    pullbackEquiv e a ∈ fixedStratum K ↔ a ∈ fixedStratum (K.comap e.symm.toMonoidHom) :=
  hasFixedVector_pullbackEquiv e K a

end CompactCoefficientClass
end Langlands
