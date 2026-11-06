import Langlands.LocalFactor.NonabelianUniquenessStatement
import Langlands.VirtualRepresentation.ExactInductionTwist

/-!
# Twisting, trivial induction and the common-closure generator span

The Library projection formula `FiniteRepresentation.induceTwistEquiv`
(`χ ⊗ Ind_S A ≅ Ind_S ((χ|_S) ⊗ A)` on the actual equivariant-function model)
is transported to common-closure induction. Induction from the whole group
is identified with the original representation by evaluation at `1`.
On the actual common-closure exact virtual groups, these give the twist
compatibility of `CommonClosure.induce` and `induce F E E h = id`.
-/

noncomputable section

universe uK uG uV uF

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
variable {S : Subgroup G} [S.FiniteIndex]

/-- Induction from a subgroup containing every element is evaluation at `1`,
for any restriction along a map acting as the inclusion. -/
def induceTopLinearEquiv (hS : ∀ g : G, g ∈ S) (φ : S →* G) (hφ : ∀ s : S, φ s = s)
    (A : FiniteRepresentation.{uK, uG, uV} K G) :
    Representation.coindV S.subtype (restrict φ A).representation ≃ₗ[K] A where
  toFun f := f.val 1
  invFun a := ⟨fun x => A.representation x a, by
    intro s g
    change A.representation ((s : G) * g) a = A.representation (φ s) (A.representation g a)
    rw [hφ, map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hf := f.property ⟨x, hS x⟩ 1
    change f.val (x * 1) = A.representation (φ ⟨x, hS x⟩) (f.val 1) at hf
    rw [mul_one, hφ] at hf
    exact hf.symm
  right_inv a := by
    change A.representation 1 a = a
    rw [map_one, Module.End.one_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Induction from the whole group is the original representation. -/
def induceTopEquiv (hS : ∀ g : G, g ∈ S) (φ : S →* G) (hφ : ∀ s : S, φ s = s)
    (A : FiniteRepresentation.{uK, uG, uV} K G) :
    Equiv (induce S (restrict φ A)) A :=
  Representation.Equiv.mk (induceTopLinearEquiv hS φ hφ A) (by
    intro g
    apply LinearMap.ext
    intro f
    have hf := f.property ⟨g, hS g⟩ 1
    change f.val (g * 1) = A.representation (φ ⟨g, hS g⟩) (f.val 1) at hf
    rw [mul_one, hφ] at hf
    change f.val (1 * g) = A.representation g (f.val 1)
    rw [one_mul]
    exact hf)

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The continuous inclusion of a smaller actual Weil subgroup in a larger one. -/
def weilInclusion (E L : Extension F) (h : E.field ≤ L.field) :
    weilSubgroup F L →ₜ* weilSubgroup F E where
  toMonoidHom := Subgroup.inclusion (weilSubgroup_antitone F E L h)
  continuous_toFun := continuous_inclusion (weilSubgroup_antitone F E L h)

/-- The common-closure projection formula on actual exact virtual groups:
twisting an induced class by `χ` is inducing the class twisted by the
restriction of `χ`. -/
theorem continuousTwist_induce (E L : Extension F) (h : E.field ≤ L.field)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (x : Virtual.{uF, uV} F L) :
    ExactGrothendieckGroup.continuousTwist χ (induce F E L h x) =
      induce F E L h
        (ExactGrothendieckGroup.continuousTwist (χ.comp (weilInclusion F E L h)) x) := by
  have key : (ExactGrothendieckGroup.continuousTwist.{uF, max uF uV} χ).toLinearMap.comp
      (induce.{uF, uV} F E L h) =
      (induce.{uF, uV} F E L h).comp
        (ExactGrothendieckGroup.continuousTwist (χ.comp (weilInclusion F E L h))).toLinearMap := by
    apply ExactGrothendieckGroup.hom_ext
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change ExactGrothendieckGroup.continuousTwist χ
          (induce F E L h (ExactGrothendieckGroup.ofRepresentation _ A)) =
        induce F E L h (ExactGrothendieckGroup.continuousTwist _
          (ExactGrothendieckGroup.ofRepresentation _ A))
      change ExactGrothendieckGroup.twist χ.toMonoidHom _ _ _
          (ExactGrothendieckGroup.induce _ _ _ _
            (ExactGrothendieckGroup.restrict _ _ _ _
              (ExactGrothendieckGroup.ofRepresentation _ A))) =
        ExactGrothendieckGroup.induce _ _ _ _
          (ExactGrothendieckGroup.restrict _ _ _ _
            (ExactGrothendieckGroup.twist _ _ _ _
              (ExactGrothendieckGroup.ofRepresentation _ A)))
      rw [ExactGrothendieckGroup.restrict_ofRepresentation,
        ExactGrothendieckGroup.induce_ofRepresentation,
        ExactGrothendieckGroup.twist_ofRepresentation,
        ExactGrothendieckGroup.twist_ofRepresentation,
        ExactGrothendieckGroup.restrict_ofRepresentation,
        ExactGrothendieckGroup.induce_ofRepresentation]
      apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
      exact (induceTwistEquiv _ χ.toMonoidHom _).symm
  exact LinearMap.congr_fun key x

/-- Induction from a field to itself is the identity of the actual exact
virtual group. -/
theorem induce_self (E : Extension F) (h : E.field ≤ E.field) :
    induce.{uF, uV} F E E h = LinearMap.id := by
  apply ExactGrothendieckGroup.hom_ext
  intro c
  induction c using Quotient.inductionOn with
  | h A =>
    change induce F E E h (ExactGrothendieckGroup.ofRepresentation _ A) =
      ExactGrothendieckGroup.ofRepresentation _ A
    change ExactGrothendieckGroup.induce _ _ _ _
        (ExactGrothendieckGroup.restrict _ _ _ _
          (ExactGrothendieckGroup.ofRepresentation _ A)) = _
    rw [ExactGrothendieckGroup.restrict_ofRepresentation,
      ExactGrothendieckGroup.induce_ofRepresentation]
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact induceTopEquiv (fun g => g.property) _ (fun _ => rfl) A.val

end Langlands.LocalFactor.CommonClosure

namespace Langlands.LocalFactor

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every difference of two continuous character lines of the same actual Weil
subgroup is a generator, induced from the field to itself. -/
theorem characterClass_sub_mem_span (E : Extension F) (χ χ' : weilSubgroup F E →ₜ* ℂˣ) :
    ExactGrothendieckGroup.characterClass.{uF, max uF uV} χ -
        ExactGrothendieckGroup.characterClass χ' ∈
      Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) := by
  apply Submodule.subset_span
  refine ⟨E, le_rfl, χ, χ', ?_⟩
  rw [induce_self]
  rfl

/-- Twisting by a continuous character of the actual Weil subgroup preserves the
integral span of the generators. -/
theorem continuousTwist_mem_span (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ)
    {x : Virtual.{uF, uV} F E}
    (hx : x ∈ Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E)) :
    ExactGrothendieckGroup.continuousTwist χ x ∈
      Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) := by
  have hle : Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) ≤
      (Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E)).comap
        (ExactGrothendieckGroup.continuousTwist χ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨L, h, ψ, ψ', rfl⟩
    apply Submodule.subset_span
    refine ⟨L, h, χ.comp (weilInclusion F E L h) * ψ,
      χ.comp (weilInclusion F E L h) * ψ', ?_⟩
    change ExactGrothendieckGroup.continuousTwist χ (induce F E L h _) = _
    rw [continuousTwist_induce, map_sub,
      ExactGrothendieckGroup.continuousTwist_characterClass,
      ExactGrothendieckGroup.continuousTwist_characterClass]
  exact hle hx

end Langlands.LocalFactor
