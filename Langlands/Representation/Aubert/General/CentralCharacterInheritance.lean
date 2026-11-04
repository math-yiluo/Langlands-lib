import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Representation.Category.Subquotients

/-! # Full-center character inheritance for actual factors and Jacquet modules -/

noncomputable section

namespace Langlands.UnitaryCentralCharacter

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Restrict the same smooth unitary full-center character along an actual
injective intertwiner. -/
def pullbackInjective (c : UnitaryCentralCharacter σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    UnitaryCentralCharacter ρ where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z v := by
    apply hf
    rw [f.isIntertwining, map_smul, c.acts]

/-- Descend the same smooth unitary full-center character along an actual
surjective intertwiner. -/
def pushforwardSurjective (c : UnitaryCentralCharacter ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    UnitaryCentralCharacter σ where
  character := c.character
  isOpen_ker := c.isOpen_ker
  norm_eq_one := c.norm_eq_one
  acts z w := by
    obtain ⟨v, rfl⟩ := hf w
    rw [← f.isIntertwining, c.acts, map_smul]

open CategoryTheory SmoothRep

/-- The literal invariant subspace inherits the given full-center datum. -/
def restrictSubrepresentation
    {A : SmoothRep.{0, uG, uV} ℂ G} (c : UnitaryCentralCharacter A.representation)
    (S : Subrepresentation A.representation) :
    UnitaryCentralCharacter (subrepresentation A S).representation :=
  c.pullbackInjective (hom (subtype A S)) (subtype_injective A S)

/-- The literal module quotient inherits the given full-center datum. -/
def descendQuotient
    {A : SmoothRep.{0, uG, uV} ℂ G} (c : UnitaryCentralCharacter A.representation)
    (S : Subrepresentation A.representation) :
    UnitaryCentralCharacter (quotient A S).representation :=
  c.pushforwardSurjective (hom (mkQ A S)) (mkQ_surjective A S)

end Langlands.UnitaryCentralCharacter

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- A unitary full-center character of nonzero actual induction forces its
inducing scalar character to have norm one on the full ambient center. -/
theorem norm_inducingScalar_ambientCenter_eq_one
    {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hZM : Subgroup.center G ≤ M)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    [Nontrivial ((normalizedInductionFunctor h hU).obj A)]
    (c : UnitaryCentralCharacter
      ((normalizedInductionFunctor h hU).obj A).representation)
    (χ : Subgroup.center M →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center M) (v : A),
      A.representation (z : M) v = (χ z : ℂ) • v)
    (z : Subgroup.center G) :
    ‖(χ (ambientCenterToLeviCenter M hZM z) : ℂ)‖ = 1 := by
  obtain ⟨f, hf⟩ := exists_ne (0 : (normalizedInductionFunctor h hU).obj A)
  have heq : χ (ambientCenterToLeviCenter M hZM z) = c.character z := by
    apply Units.ext
    apply smul_left_injective ℂ hf
    exact (normalizedInductionCentralCharacter_acts h hU hZM A χ hscalar z f).symm.trans
      (c.acts z f)
  rw [heq]
  exact c.norm_eq_one z

/-- Ambient central scalars descend unchanged to the actual normalized
Jacquet quotient: their inverse half modulus is one. -/
theorem normalizedJacquet_ambientCenter_acts
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hZM : Subgroup.center G ≤ M)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (c : UnitaryCentralCharacter A.representation)
    (z : Subgroup.center G)
    (v : (normalizedJacquetFunctor U M hU hMU).obj A) :
    ((normalizedJacquetFunctor U M hU hMU).obj A).representation
      (ambientCenterToLeviCenter M hZM z : M) v = (c.character z : ℂ) • v := by
  obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 v
  rw [normalizedJacquetFunctor_obj_apply]
  have hhalf := closedHalfCharacter_eq_one_of_mem_center U M hU hMU
    (ambientCenterToLeviCenter M hZM z : M) z.property
  have hinv : HaarModulus.closedInverseHalfCharacter U hU M hMU
      (ambientCenterToLeviCenter M hZM z : M) = 1 := by
    change (HaarModulus.closedHalfCharacter U hU M hMU
      (ambientCenterToLeviCenter M hZM z : M))⁻¹ = 1
    rw [hhalf, inv_one]
  rw [hinv, Units.val_one, one_smul]
  change Jacquet.Localization.mk A.representation U 1
      (A.representation (z : G) w) =
    (c.character z : ℂ) • Jacquet.Localization.mk A.representation U 1 w
  rw [c.acts, map_smul]

/-- A scalar full-center character of a nonzero actual normalized Jacquet
module has norm one on the ambient center whenever the ambient representation
has the given unitary central character. -/
theorem norm_jacquetScalar_ambientCenter_eq_one
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hZM : Subgroup.center G ≤ M)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    [Nontrivial ((normalizedJacquetFunctor U M hU hMU).obj A)]
    (c : UnitaryCentralCharacter A.representation)
    (χ : Subgroup.center M →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center M)
      (v : (normalizedJacquetFunctor U M hU hMU).obj A),
      ((normalizedJacquetFunctor U M hU hMU).obj A).representation (z : M) v =
        (χ z : ℂ) • v)
    (z : Subgroup.center G) :
    ‖(χ (ambientCenterToLeviCenter M hZM z) : ℂ)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : (normalizedJacquetFunctor U M hU hMU).obj A)
  have heq : χ (ambientCenterToLeviCenter M hZM z) = c.character z := by
    apply Units.ext
    apply smul_left_injective ℂ hv
    exact (hscalar (ambientCenterToLeviCenter M hZM z) v).symm.trans
      (normalizedJacquet_ambientCenter_acts U M hU hMU hZM A c z v)
  rw [heq]
  exact c.norm_eq_one z

end Langlands.Aubert.General
