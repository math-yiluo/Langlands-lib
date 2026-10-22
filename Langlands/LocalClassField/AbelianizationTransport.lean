import Langlands.ClassFieldTheory.Local.Galois

/-!
# Transport on topological abelianizations

The quotient is the published quotient by the closed commutator subgroup.
Its functorial maps give an actual topological equivalence for an actual
topological group equivalence. No reciprocity equivalence is chosen.
-/

noncomputable section

universe uG uH uJ uA

namespace Langlands.LocalClassField

variable {G : Type uG} {H : Type uH} {J : Type uJ}
  [Group G] [Group H] [Group J]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J]

/-- The induced map agrees with the original map on quotient generators. -/
@[simp]
theorem abelianizationMap_projection (f : G →ₜ* H) (g : G) :
    abelianizationMap f (abelianizationProjection G g) =
      abelianizationProjection H (f g) := rfl

/-- Continuous homomorphisms out of the actual quotient are determined by
their values after its surjective projection. -/
theorem abelianization_hom_ext {A : Type uA} [Monoid A] [TopologicalSpace A]
    {f g : TopologicalAbelianization G →ₜ* A}
    (h : ∀ x : G, f (abelianizationProjection G x) =
      g (abelianizationProjection G x)) : f = g := by
  ext x
  refine QuotientGroup.induction_on x ?_
  exact h

/-- Topological abelianization preserves the identity map. -/
@[simp]
theorem abelianizationMap_id :
    abelianizationMap (ContinuousMonoidHom.id G) =
      ContinuousMonoidHom.id (TopologicalAbelianization G) := by
  apply abelianization_hom_ext
  intro g
  rfl

/-- Topological abelianization preserves composition, including maps between
groups in different universes. -/
theorem abelianizationMap_comp (f : G →ₜ* H) (g : H →ₜ* J) :
    abelianizationMap (g.comp f) =
      (abelianizationMap g).comp (abelianizationMap f) := by
  apply abelianization_hom_ext
  intro x
  rfl

/-- An actual topological group equivalence induces an actual equivalence
of the closed-commutator quotients. The inverse is the induced inverse map. -/
def abelianizationCongr (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H where
  toFun := abelianizationMap (e : G →ₜ* H)
  invFun := abelianizationMap (e.symm : H →ₜ* G)
  left_inv x := by
    refine QuotientGroup.induction_on x ?_
    intro g
    change abelianizationProjection G (e.symm (e g)) = abelianizationProjection G g
    rw [e.symm_apply_apply]
  right_inv x := by
    refine QuotientGroup.induction_on x ?_
    intro h
    change abelianizationProjection H (e (e.symm h)) = abelianizationProjection H h
    rw [e.apply_symm_apply]
  map_mul' := map_mul (abelianizationMap (e : G →ₜ* H))
  continuous_toFun := (abelianizationMap (e : G →ₜ* H)).continuous
  continuous_invFun := (abelianizationMap (e.symm : H →ₜ* G)).continuous

@[simp]
theorem abelianizationCongr_projection (e : G ≃ₜ* H) (g : G) :
    abelianizationCongr e (abelianizationProjection G g) =
      abelianizationProjection H (e g) := rfl

/-- The inverse transport is definitionally induced by the inverse
topological group equivalence. -/
@[simp]
theorem abelianizationCongr_symm (e : G ≃ₜ* H) :
    (abelianizationCongr e).symm = abelianizationCongr e.symm := rfl

@[simp]
theorem abelianizationCongr_refl :
    abelianizationCongr (ContinuousMulEquiv.refl G) =
      ContinuousMulEquiv.refl (TopologicalAbelianization G) := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro g
  rfl

/-- Transport respects composition; no choice of quotient representatives
is present in either route. -/
theorem abelianizationCongr_trans (e : G ≃ₜ* H) (d : H ≃ₜ* J) :
    abelianizationCongr (e.trans d) =
      (abelianizationCongr e).trans (abelianizationCongr d) := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro g
  rfl

variable {A : Type uA} [Group A] [IsMulCommutative A]
  [TopologicalSpace A] [T1Space A]

/-- Descent of a continuous character commutes with precomposition.
This uses the closed-commutator quotient, not the algebraic abelianization. -/
theorem abelianizationLift_comp (f : G →ₜ* H) (χ : H →ₜ* A) :
    abelianizationLift (χ.comp f) =
      (abelianizationLift χ).comp (abelianizationMap f) := by
  apply abelianization_hom_ext
  intro g
  rfl

/-- In particular, character descent is compatible with the constructed
topological equivalence of abelianizations. -/
theorem abelianizationLift_comp_equiv (e : G ≃ₜ* H) (χ : H →ₜ* A) :
    abelianizationLift (χ.comp (e : G →ₜ* H)) =
      (abelianizationLift χ).comp
        (abelianizationCongr e : TopologicalAbelianization G →ₜ*
          TopologicalAbelianization H) :=
  abelianizationLift_comp (e : G →ₜ* H) χ

end Langlands.LocalClassField
