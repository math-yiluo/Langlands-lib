import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.Global.IdeleAbsoluteValue
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! # Algebraic characters and actual norm-one adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- An actual F-rational algebraic character, with no commutativity assumption on G. -/
abbrev AlgebraicCharacter := G ⟶ (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp

/-- Evaluation of an actual algebraic character in the units of a coefficient algebra. -/
def characterUnits (χ : AlgebraicCharacter F G) (A : CommAlgCat.{u} (CommRingCat.of F)) :
    G.affinePoints A →* Aˣ :=
  (GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) A).toMonoidHom.comp
    (G.affinePointsTarget χ A)

omit [NumberField F] in
/-- Character evaluation commutes with extension of coefficients. -/
theorem characterUnits_naturality (χ : AlgebraicCharacter F G)
    {A B : CommAlgCat.{u} (CommRingCat.of F)} (f : A ⟶ B) (x : G.affinePoints A) :
    characterUnits F G χ B (G.affinePointMap f x) =
      Units.map f.hom.toRingHom.toMonoidHom (characterUnits F G χ A x) := by
  have h := DFunLike.congr_fun (G.affinePointsTarget_naturality χ f) x
  simp only [MonoidHom.comp_apply] at h
  change GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) B
    (G.affinePointsTarget χ B (G.affinePointMap f x)) = _
  rw [← h]
  exact GroupScheme.Gm.affineUnitsEquiv_naturality (CommRingCat.of F) f _

omit [NumberField F] in
/-- Character evaluation is continuous for the regular-function point topology. -/
theorem continuous_characterUnits (χ : AlgebraicCharacter F G)
    (A : CommAlgCat.{u} (CommRingCat.of F)) [TopologicalSpace A] :
    Continuous[G.affinePointsTopologicalSpace A, _] (characterUnits F G χ A) := by
  let : TopologicalSpace (G.affinePoints A) := G.affinePointsTopologicalSpace A
  let : TopologicalSpace (GroupScheme.affinePoints
      (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp A) :=
    GroupScheme.affinePointsTopologicalSpace (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp A
  exact (GroupScheme.Gm.continuous_affineUnitsEquiv (CommRingCat.of F) A).comp
    (G.continuous_affinePointsTarget A χ)

/-- The continuous idele-valued evaluation of an actual F-rational character. -/
def character (χ : AlgebraicCharacter F G) : AdelicGroupPoints F G →ₜ* Ideles F where
  toMonoidHom := characterUnits F G χ (CommAlgCat.of F (AdeleRing (𝓞 F) F))
  continuous_toFun := continuous_characterUnits F G χ
    (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Principal rational points evaluate to the corresponding principal idele. -/
theorem character_rational (χ : AlgebraicCharacter F G) (x : RationalGroupPoints F G) :
    character F G χ (rational F G x) =
      diagonalUnits F (characterUnits F G χ (CommAlgCat.of F F) x) :=
  characterUnits_naturality F G χ
    (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) x

/-- The genuine normalized adelic absolute value of an algebraic character. -/
def characterNorm (χ : AlgebraicCharacter F G) : AdelicGroupPoints F G →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.full F).comp (character F G χ)

/-- The product formula makes every character norm trivial on principal points. -/
@[simp] theorem characterNorm_rational (χ : AlgebraicCharacter F G)
    (x : RationalGroupPoints F G) : characterNorm F G χ (rational F G x) = 1 := by
  change IdeleAbsoluteValue.full F (character F G χ (rational F G x)) = 1
  rw [character_rational, IdeleAbsoluteValue.full_diagonalUnits]

/-- The actual norm-one subgroup, the intersection of all algebraic character-norm kernels. -/
def normOneSubgroup : Subgroup (AdelicGroupPoints F G) :=
  ⨅ χ : AlgebraicCharacter F G, (characterNorm F G χ).toMonoidHom.ker

@[simp] theorem mem_normOneSubgroup (x : AdelicGroupPoints F G) :
    x ∈ normOneSubgroup F G ↔ ∀ χ : AlgebraicCharacter F G, characterNorm F G χ x = 1 := by
  simp only [normOneSubgroup, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

/-- The norm-one subgroup is normal, as an intersection of kernels. -/
instance normOneSubgroup_normal : (normOneSubgroup F G).Normal :=
  Subgroup.normal_iInf_normal fun _ => inferInstance

/-- The norm-one subgroup is closed by continuity of all actual character norms. -/
theorem isClosed_normOneSubgroup : IsClosed (normOneSubgroup F G : Set (AdelicGroupPoints F G)) := by
  change IsClosed (↑(⨅ χ : AlgebraicCharacter F G,
    (characterNorm F G χ).toMonoidHom.ker) : Set (AdelicGroupPoints F G))
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun χ => isClosed_singleton.preimage (characterNorm F G χ).continuous

/-- The actual principal rational subgroup lies in the norm-one subgroup. -/
theorem rationalSubgroup_le_normOneSubgroup : rationalSubgroup F G ≤ normOneSubgroup F G := by
  rintro _ ⟨x, rfl⟩
  exact (mem_normOneSubgroup F G _).mpr fun χ => characterNorm_rational F G χ x

/-- Rational points as actual norm-one adelic points. -/
def rationalNormOne : RationalGroupPoints F G →* normOneSubgroup F G :=
  (rational F G).codRestrict (normOneSubgroup F G) fun x =>
    (mem_normOneSubgroup F G _).mpr fun χ => characterNorm_rational F G χ x

@[simp] theorem rationalNormOne_val (x : RationalGroupPoints F G) :
    (rationalNormOne F G x : AdelicGroupPoints F G) = rational F G x := rfl

variable [IsAffine G.X.left]

/-- The norm-one points inherit a Hausdorff topological group structure. -/
instance normOneIsTopologicalGroup : IsTopologicalGroup (normOneSubgroup F G) := inferInstance

/-- Finite-type actual norm-one points are locally compact as a closed subgroup. -/
instance normOneLocallyCompactSpace [LocallyOfFiniteType G.X.hom] :
    LocallyCompactSpace (normOneSubgroup F G) :=
  (isClosed_normOneSubgroup F G).locallyCompactSpace

end Langlands.Global.AdelicGroupPoints
