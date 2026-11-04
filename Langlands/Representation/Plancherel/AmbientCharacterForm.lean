import Langlands.Representation.Plancherel.IntertwiningCone
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # Local character forms induced from a single ambient positive form -/

noncomputable section

universe u

namespace Langlands.LinearAlgebra.PositiveQuotient

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm)
  (hp : ∀ x : V, x ≠ 0 → 0 < B x x)
  (q : V →ₗ[ℝ] W) (hq : Function.Surjective q)

include hs hp in
private theorem kernel_isCompl_orthogonal :
    IsCompl (LinearMap.ker q) (B.orthogonal (LinearMap.ker q)) := by
  have hn : (B.restrict (LinearMap.ker q)).Nondegenerate := by
    constructor
    · intro x hx
      by_contra hx0
      exact (ne_of_gt (hp x (fun h => hx0 (Subtype.ext h)))) (hx x)
    · intro x hx
      by_contra hx0
      exact (ne_of_gt (hp x (fun h => hx0 (Subtype.ext h)))) (hx x)
  exact B.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hn

/-- Restriction identifies the orthogonal complement of its kernel with its target. -/
def orthogonalRestrictionEquiv : B.orthogonal (LinearMap.ker q) ≃ₗ[ℝ] W := by
  let N := B.orthogonal (LinearMap.ker q)
  have hc := kernel_isCompl_orthogonal B hs hp q
  refine LinearEquiv.ofBijective (q.comp N.subtype) ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hc.disjoint ((x : V) - (y : V))
    · change q ((x : V) - (y : V)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    · exact N.sub_mem x.property y.property
  · intro x
    obtain ⟨y, rfl⟩ := hq x
    have hy : y ∈ LinearMap.ker q ⊔ N := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨z, hz, n, hn, hadd⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨n, hn⟩, ?_⟩
    change q n = q y
    rw [← hadd, map_add, show q z = 0 from hz, zero_add]

/-- The lift selected by orthogonality to the actual kernel of `q`. -/
def orthogonalLift : W →ₗ[ℝ] V :=
  (B.orthogonal (LinearMap.ker q)).subtype.comp
    (orthogonalRestrictionEquiv B hs hp q hq).symm.toLinearMap

@[simp] theorem map_orthogonalLift (x : W) :
    q (orthogonalLift B hs hp q hq x) = x :=
  (orthogonalRestrictionEquiv B hs hp q hq).apply_symm_apply x

theorem orthogonalLift_mem (x : W) :
    orthogonalLift B hs hp q hq x ∈ B.orthogonal (LinearMap.ker q) :=
  ((orthogonalRestrictionEquiv B hs hp q hq).symm x).property

/-- The local form is the pullback of the ambient form by the orthogonal lift. -/
def quotientForm : LinearMap.BilinForm ℝ W :=
  B.compl₁₂ (orthogonalLift B hs hp q hq) (orthogonalLift B hs hp q hq)

@[simp] theorem quotientForm_apply (x y : W) :
    quotientForm B hs hp q hq x y =
      B (orthogonalLift B hs hp q hq x) (orthogonalLift B hs hp q hq y) := rfl

theorem quotientForm_symm : (quotientForm B hs hp q hq).IsSymm :=
  ⟨fun _ _ => hs.eq _ _⟩

theorem quotientForm_pos {x : W} (hx : x ≠ 0) :
    0 < quotientForm B hs hp q hq x x := by
  apply hp
  intro hz
  apply hx
  rw [← map_orthogonalLift B hs hp q hq x, hz, map_zero]

/-- The orthogonal lift is adjoint to restriction for the induced local form. -/
theorem pairing_orthogonalLift (x : W) (y : V) :
    B (orthogonalLift B hs hp q hq x) y = quotientForm B hs hp q hq x (q y) := by
  have hk : y - orthogonalLift B hs hp q hq (q y) ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker, map_sub, map_orthogonalLift, sub_self]
  have hz := (orthogonalLift_mem B hs hp q hq x)
    (y - orthogonalLift B hs hp q hq (q y)) hk
  have hz' := hs.isRefl _ _ hz
  rw [map_sub] at hz'
  exact sub_eq_zero.mp hz'

end Langlands.LinearAlgebra.PositiveQuotient

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Plancherel

open Langlands.LinearAlgebra.PositiveQuotient

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
  (B : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar T)) (hs : B.IsSymm)
  (hp : ∀ x : RealTorusSpace.Vstar T, x ≠ 0 → 0 < B x x)

/-- The actual restriction map's orthogonal lift for a specified ambient form. -/
def characterRestrictionOrthogonalLift :
    RealTorusSpace.Vstar A →ₗ[ℝ] RealTorusSpace.Vstar T := by
  let _ := hT.finite_realCharacterSpace
  exact orthogonalLift B hs hp
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
    (hA.rationalCharacterRestrictReal_surjective_of_mono hT (CommGroupScheme.groupHom f))

/-- The actual local form induced from a single ambient positive form. -/
def inducedCharacterForm : LinearMap.BilinForm ℝ (RealTorusSpace.Vstar A) :=
  B.compl₁₂ (characterRestrictionOrthogonalLift hA hT f B hs hp)
    (characterRestrictionOrthogonalLift hA hT f B hs hp)

@[simp] theorem restrict_characterRestrictionOrthogonalLift (x : RealTorusSpace.Vstar A) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      (characterRestrictionOrthogonalLift hA hT f B hs hp x) = x := by
  let _ := hT.finite_realCharacterSpace
  exact map_orthogonalLift B hs hp _ _ x

theorem inducedCharacterForm_symm : (inducedCharacterForm hA hT f B hs hp).IsSymm :=
  ⟨fun _ _ => hs.eq _ _⟩

theorem inducedCharacterForm_pos {x : RealTorusSpace.Vstar A} (hx : x ≠ 0) :
    0 < inducedCharacterForm hA hT f B hs hp x x := by
  apply hp
  intro hz
  apply hx
  rw [← restrict_characterRestrictionOrthogonalLift hA hT f B hs hp x, hz, map_zero]

/-- Compatibility is constructed from the actual monomorphism of split tori
and one ambient form, rather than postulated for independently chosen forms. -/
theorem inducedCharacterForm_compatible :
    CompatibleCharacterForms f (inducedCharacterForm hA hT f B hs hp) B
      (characterRestrictionOrthogonalLift hA hT f B hs hp) := by
  refine ⟨restrict_characterRestrictionOrthogonalLift hA hT f B hs hp, ?_⟩
  intro x y
  let _ := hT.finite_realCharacterSpace
  exact pairing_orthogonalLift B hs hp _ _ x y

end Langlands.Plancherel
