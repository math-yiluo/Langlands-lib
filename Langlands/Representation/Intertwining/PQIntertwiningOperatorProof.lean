import Langlands.Representation.Intertwining.PQIntertwiningOperatorStatement
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof

/-! # The intertwining operator of a PQ-regular representation -/

noncomputable section

namespace Langlands

section Separation

variable {H B : Type*} [Group H] [CommGroup B]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {σ : Representation ℂ H W}

/-- Equivariance extends linearly from the group to its group algebra. -/
theorem intertwining_groupAlgebra_apply (f : ρ.IntertwiningMap σ) (φ : B →* H)
    (c : MonoidAlgebra ℂ B) (x : V) :
    f (Representation.asAlgebraHom (ρ.comp φ) c x) =
      Representation.asAlgebraHom (σ.comp φ) c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single b z =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    exact congrArg (fun y => z • y)
      (Representation.IntertwiningMap.isIntertwining ρ σ f (φ b) x)

/-- A central group-algebra element acts equivariantly on every representation. -/
def centralGroupAlgebraAction (ρ : Representation ℂ H V) (φ : B →* H)
    (hφ : ∀ b, φ b ∈ Subgroup.center H) (c : MonoidAlgebra ℂ B) :
    ρ.IntertwiningMap ρ where
  toLinearMap := Representation.asAlgebraHom (ρ.comp φ) c
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change Representation.asAlgebraHom (ρ.comp φ) c (ρ h x) =
      ρ h (Representation.asAlgebraHom (ρ.comp φ) c x)
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | single b z =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      change ρ (φ b) (ρ h x) = ρ h (ρ (φ b) x)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp (hφ b) h]

/-- Disjoint action kernels give unique extension of an equivariant map from a
subrepresentation. -/
theorem existsUnique_intertwining_extension
    (φ : B →* H) (hφ : ∀ b, φ b ∈ Subgroup.center H)
    (T : Subrepresentation ρ) (q : T.toRepresentation.IntertwiningMap σ)
    (h : groupAlgebraKernel σ φ ⊔
      groupAlgebraKernel (ρ.quotient T.toSubmodule
        (fun g _ hx => T.apply_mem_toSubmodule g hx)) φ = ⊤) :
    ∃! K : ρ.IntertwiningMap σ, ∀ x : T, K x = q x := by
  have h1 : (1 : MonoidAlgebra ℂ B) ∈ groupAlgebraKernel σ φ ⊔
      groupAlgebraKernel (ρ.quotient T.toSubmodule
        (fun g _ hx => T.apply_mem_toSubmodule g hx)) φ := by rw [h]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  have ha0 := (mem_groupAlgebraKernel_iff σ φ a).mp ha
  have hbσ : Representation.asAlgebraHom (σ.comp φ) b = 1 := by
    have he := congrArg (Representation.asAlgebraHom (σ.comp φ)) hab
    simpa only [map_add, map_one, ha0, zero_add] using he
  let π : ρ.IntertwiningMap
      (ρ.quotient T.toSubmodule (fun g _ hx => T.apply_mem_toSubmodule g hx)) :=
    { toLinearMap := T.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hbT (x : V) : Representation.asAlgebraHom (ρ.comp φ) b x ∈ T := by
    change Representation.asAlgebraHom (ρ.comp φ) b x ∈ T.toSubmodule
    rw [← Submodule.Quotient.mk_eq_zero]
    change π (Representation.asAlgebraHom (ρ.comp φ) b x) = 0
    rw [intertwining_groupAlgebra_apply π φ]
    rw [(mem_groupAlgebraKernel_iff _ φ b).mp hb]
    rfl
  let E : ρ.IntertwiningMap T.toRepresentation :=
    { toLinearMap := (Representation.asAlgebraHom (ρ.comp φ) b).codRestrict
        T.toSubmodule hbT
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining ρ ρ
          (centralGroupAlgebraAction ρ φ hφ b) g x }
  let K : ρ.IntertwiningMap σ := q.comp E
  have hK (x : T) : K x = q x := by
    let ι : T.toRepresentation.IntertwiningMap ρ :=
      { toLinearMap := T.toSubmodule.subtype
        isIntertwining' _ := rfl }
    have he : E (x : V) = Representation.asAlgebraHom (T.toRepresentation.comp φ) b x := by
      apply Subtype.ext
      exact (intertwining_groupAlgebra_apply ι φ b x).symm
    change q (E (x : V)) = q x
    rw [he, intertwining_groupAlgebra_apply q φ, hbσ]
    rfl
  refine ⟨K, hK, ?_⟩
  intro L hL
  ext x
  have hLb := intertwining_groupAlgebra_apply L φ b x
  rw [hbσ] at hLb
  change L (Representation.asAlgebraHom (ρ.comp φ) b x) = L x at hLb
  calc
    L x = L (E x : V) := hLb.symm
    _ = q (E x) := hL (E x)
    _ = K x := rfl

end Separation

end Langlands

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

set_option maxHeartbeats 800000 in
/-- Renard VII.3.4: the unique intertwiner characterized by the supplied
identification of the identity support subquotient. -/
theorem pqIntertwiningOperator : PQIntertwiningOperatorStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro σ hregular e
  let I := (leviInductionFunctor p l r hp hr hl hmul).obj σ
  let R := (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ).obj σ
  let S := closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  let T := boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  let qS : (T.obj σ).toRepresentation.IntertwiningMap σ.representation :=
    e.toIntertwiningMap.comp (S.quotientProjection T σ).hom
  obtain ⟨K, hK, hunique⟩ := existsUnique_intertwining_extension
    (ρ := R.ρ) (rationalPoints.map a)
    ha.isCentralSplitTorus.isCentral.map_mem_center (T.obj σ) qS hregular
  obtain ⟨F, hF⟩ := leviFrobeniusReciprocity k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ I σ
  change _ ≃ₗ[ℂ] R.ρ.IntertwiningMap σ.representation at F
  let J := F.symm K
  refine ⟨J, ?_, ?_⟩
  · intro f hf y hy heq
    subst y
    rw [← hF J f]
    change (F (F.symm K)) _ = _
    rw [F.apply_symm_apply]
    exact hK ⟨_, hy⟩
  · intro L hL
    apply F.injective
    change F L = F (F.symm K)
    rw [F.apply_symm_apply]
    apply hunique
    intro x
    obtain ⟨f, hf, hfx⟩ := x.property
    exact (congrArg (F L) hfx.symm).trans
      ((hF L f).trans (hL f hf (x : R) x.property hfx.symm))

end Langlands.Aubert.General.RepresentedParabolic
