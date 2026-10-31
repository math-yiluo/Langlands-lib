import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionRestriction

/-! # Universal lifting through actual quotient-action restriction -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {X Z W : VariableActionSpace.{u, v} K}
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Lift a genuine quotient arrow through group restriction using its original
bounded algebra map and the specified compatible group homomorphism. -/
def restrictionLift (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) : Z ⟶ restrict X f where
  groupHom := k
  algebraMap := h.algebraMap
  equivariant g a := by
    change h.algebraMap ((X.algebraAction.obj.ρ (f (k g))).toAlgHom a) =
      (Z.algebraAction.obj.ρ g).toAlgHom (h.algebraMap a)
    rw [show f (k g) = h.groupHom g from
      congrArg (fun q : Z.groupType →ₜ* X.groupType => q g) hgroup]
    exact h.equivariant g a

@[simp]
theorem restrictionLift_groupHom (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (restrictionLift f h k hgroup).groupHom = k := rfl

@[simp]
theorem restrictionLift_algebraMap (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (restrictionLift f h k hgroup).algebraMap = h.algebraMap := rfl

/-- The constructed lift factors the original complete geometric arrow. -/
theorem restrictionLift_comp_restrictionMap (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    restrictionLift f h k hgroup ≫ restrictionMap X f = h := by
  apply Hom.ext
  · exact hgroup
  · rfl

/-- The prescribed group map and factorization determine the lift uniquely. -/
theorem restrictionLift_unique (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom)
    (l : Z ⟶ restrict X f) (lgroup : l.groupHom = k)
    (lfactor : l ≫ restrictionMap X f = h) : l = restrictionLift f h k hgroup := by
  apply Hom.ext
  · exact lgroup
  · exact congrArg (fun q : Z ⟶ X => q.algebraMap) lfactor

/-- The explicit universal property of the canonical restriction arrow. -/
theorem restrictionLift_existsUnique (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    ∃! l : Z ⟶ restrict X f, l.groupHom = k ∧ l ≫ restrictionMap X f = h := by
  refine ⟨restrictionLift f h k hgroup,
    ⟨rfl, restrictionLift_comp_restrictionMap f h k hgroup⟩, ?_⟩
  intro l hl
  exact restrictionLift_unique f h k hgroup l hl.1 hl.2

/-- Composition with the actual restriction arrow is an equivalence of the
morphism sets lying over the specified continuous group homomorphisms. -/
def restrictionHomEquiv (f : H →ₜ* X.groupType) (k : Z.groupType →ₜ* H) :
    {l : Z ⟶ restrict X f // l.groupHom = k} ≃
      {h : Z ⟶ X // f.comp k = h.groupHom} where
  toFun l := ⟨l.val ≫ restrictionMap X f, by
    change f.comp k = f.comp l.val.groupHom
    rw [l.property]⟩
  invFun h := ⟨restrictionLift f h.val k h.property, rfl⟩
  left_inv l := by
    apply Subtype.ext
    apply Hom.ext
    · exact l.property.symm
    · rfl
  right_inv h := by
    apply Subtype.ext
    exact restrictionLift_comp_restrictionMap f h.val k h.property

@[simp]
theorem restrictionHomEquiv_apply (f : H →ₜ* X.groupType) (k : Z.groupType →ₜ* H)
    (l : {l : Z ⟶ restrict X f // l.groupHom = k}) :
    (restrictionHomEquiv f k l).val = l.val ≫ restrictionMap X f := rfl

@[simp]
theorem restrictionHomEquiv_symm_apply (f : H →ₜ* X.groupType)
    (k : Z.groupType →ₜ* H) (h : {h : Z ⟶ X // f.comp k = h.groupHom}) :
    ((restrictionHomEquiv f k).symm h).val = restrictionLift f h.val k h.property := rfl

/-- The old identity-group factor is the corresponding special case. -/
theorem restrictionLift_eq_fixedFactor (h : Z ⟶ X) :
    restrictionLift h.groupHom h (ContinuousMonoidHom.id Z.groupType)
      (by ext g; rfl) = fixedFactor h := by
  apply Hom.ext <;> rfl

/-- Lifting the canonical restriction arrow along the identity gives identity. -/
theorem restrictionLift_restrictionMap (f : H →ₜ* X.groupType) :
    restrictionLift f (restrictionMap X f) (ContinuousMonoidHom.id H)
      (by ext g; rfl) = 𝟙 (restrict X f) := by
  apply Hom.ext <;> rfl

/-- Lifting commutes with precomposition by arbitrary actual quotient arrows. -/
theorem restrictionLift_precomp (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) (p : W ⟶ Z) :
    restrictionLift f (p ≫ h) (k.comp p.groupHom)
      (by ext g; exact congrArg (fun q : Z.groupType →ₜ* X.groupType =>
        q (p.groupHom g)) hgroup) = p ≫ restrictionLift f h k hgroup := by
  apply Hom.ext <;> rfl

section SuccessiveRestriction

variable {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Two successive universal lifts agree with the lift along the composite
restriction after the canonical identity-on-algebra comparison. -/
theorem restrictionLift_comp (f : H →ₜ* X.groupType) (g : J →ₜ* H)
    (h : Z ⟶ X) (k : Z.groupType →ₜ* J)
    (hgroup : (f.comp g).comp k = h.groupHom) :
    restrictionLift g (restrictionLift f h (g.comp k) hgroup) k rfl ≫
        (restrictCompIso X f g).hom =
      restrictionLift (f.comp g) h k hgroup := by
  apply Hom.ext <;> rfl

end SuccessiveRestriction

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Actual continuous spectra retain precisely the prescribed group lift. -/
@[simp]
theorem spectrumFunctor_restrictionLift_groupHom (f : H →ₜ* X.groupType)
    (h : Z ⟶ X) (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (spectrumFunctor.map (restrictionLift f h k hgroup)).groupHom = k := rfl

/-- The lift has exactly the original continuous seminorm map on the unchanged
underlying spectra of the target quotient. -/
@[simp]
theorem spectrumFunctor_restrictionLift_spaceMap (f : H →ₜ* X.groupType)
    (h : Z ⟶ X) (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (spectrumFunctor.map (restrictionLift f h k hgroup)).spaceMap =
      (spectrumFunctor.map h).spaceMap := rfl

/-- Evaluation on actual bounded multiplicative seminorms uses the original
bounded algebra pullback. -/
theorem spectrumFunctor_restrictionLift_apply (f : H →ₜ* X.groupType)
    (h : Z ⟶ X) (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom)
    (x : BanachSpectrum Z.algebraAction.obj.V) (a : X.algebraAction.obj.V) :
    BanachSpectrum.toMulRingSeminorm
      ((spectrumFunctor.map (restrictionLift f h k hgroup)).spaceMap x) a =
      x (h.algebraMap a) := rfl

/-- The spectrum functor carries the complete lifted factorization to its
actual continuous equivariant factorization. -/
theorem spectrumFunctor_restrictionLift_factorization (f : H →ₜ* X.groupType)
    (h : Z ⟶ X) (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    spectrumFunctor.map (restrictionLift f h k hgroup) ≫
        spectrumFunctor.map (restrictionMap X f) = spectrumFunctor.map h := by
  rw [← Functor.map_comp, restrictionLift_comp_restrictionMap]

end Spectrum

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
