import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.SemigroupPartition
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Trivial subgroups and vanishing ambient weight support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TrivialSubgroup

variable {B : Scheme.{u}} (G : GroupScheme B)

/-- The canonical unit represents the all-test identity subgroup. -/
theorem bot_isRepresentedBy_kernelUnit :
    (⊥ : SubgroupFunctor G).IsRepresentedBy (kernelUnit G) := by
  refine ⟨⟨fun {T} x y _ => toUnit_unique x y⟩, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change y ≫ (kernelUnit G).hom.hom = toUnit T ≫ (kernelUnit G).hom.hom
    exact congrArg (fun f : T ⟶ (Grp.trivial (Over B)).X =>
      f ≫ (kernelUnit G).hom.hom) (toUnit_unique y (toUnit T))
  · intro hx
    have hx : x = 1 := hx
    exact ⟨toUnit T, hx.symm⟩

/-- The identity section of a separated group scheme is a closed subgroup. -/
theorem kernelUnit_isClosedSubgroup [IsSeparated G.X.hom] :
    IsClosedSubgroup (kernelUnit G) := by
  change IsClosedImmersion η[G.X].left
  have he : η[G.X].left ≫ G.X.hom = 𝟙 B := η[G.X].w
  have : IsClosedImmersion (η[G.X].left ≫ G.X.hom) :=
    he.symm ▸ (inferInstance : IsClosedImmersion (𝟙 B))
  exact .of_comp _ G.X.hom

end TrivialSubgroup

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A semigroup selects no weight of the actual ambient tangent action. -/
def HasNoAmbientWeights (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) : Prop :=
  ∀ χ ∈ A, χ ∉ actionWeightSupport b ⊤

/-- The unit over a field is a smooth connected closed representative of bot. -/
theorem bot_isSmoothConnectedClosed :
    IsSmoothConnectedClosed (⊥ : SubgroupFunctor G) := by
  refine ⟨Grp.trivial (Over (Spec (CommRingCat.of k))), kernelUnit G,
    bot_isRepresentedBy_kernelUnit G, kernelUnit_isClosedSubgroup G, ?_, ?_⟩
  · change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of k))
    infer_instance

omit [IsAffineHom G.X.hom] in
/-- Every automorphic action fixes the identity subgroup. -/
theorem bot_isStable (b : AutomorphicAction S.toGrp G) :
    b.IsStable ⊥ := by
  intro T s x hx
  have hx : x = 1 := hx
  subst x
  exact b.act_one s

/-- The tangent image of the identity subgroup is zero. -/
theorem bot_hasLieImage :
    HasLieImage (⊥ : SubgroupFunctor G) ⊥ := by
  intro X
  simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Submodule.mem_bot]
  constructor
  · intro hx
    change X.toMul = 1
    exact Subtype.ext hx
  · rintro rfl
    rfl

/-- The weight span indexed by the empty semigroup is zero. -/
theorem semigroupWeightSpan_bot (b : AutomorphicAction S.toGrp G) :
    semigroupWeightSpan b ⊥ = ⊥ := by
  apply iSup_eq_bot.mpr
  intro χ
  exact False.elim χ.property

/-- A semigroup selecting no ambient weights has zero weight span. -/
theorem semigroupWeightSpan_eq_bot_of_noAmbientWeights
    (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (hA : HasNoAmbientWeights b A) :
    semigroupWeightSpan b A = ⊥ := by
  apply iSup_eq_bot.mpr
  intro χ
  exact actionWeightSpace_eq_bot_of_not_mem_support b (hA χ χ.property)

/-- Realization uniqueness identifies the empty-semigroup subgroup with bot. -/
theorem semigroupSubgroup_bot
    (hreal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G) :
    semigroupSubgroup b ⊥ = ⊥ := by
  have h := (hreal k G hG inferInstance S hS b ⊥).2.2.2.2.2
  apply (h ⊥ bot_isSmoothConnectedClosed (bot_isStable b) ?_).symm
  rw [semigroupWeightSpan_bot]
  exact bot_hasLieImage

/-- With realization uniqueness, absence of ambient weights forces triviality. -/
theorem semigroupSubgroup_eq_bot_of_noAmbientWeights
    (hreal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (hA : HasNoAmbientWeights b A) :
    semigroupSubgroup b A = ⊥ := by
  have h := (hreal k G hG inferInstance S hS b A).2.2.2.2.2
  apply (h ⊥ bot_isSmoothConnectedClosed (bot_isStable b) ?_).symm
  rw [semigroupWeightSpan_eq_bot_of_noAmbientWeights b A hA]
  exact bot_hasLieImage

/-- A cyclic tail with no ambient weights is the trivial all-test subgroup. -/
theorem weightFiltration_eq_bot_of_noAmbientWeights
    (hreal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) (r : ℕ)
    (h : ∀ n : ℕ, r ≤ n → 0 < n → n • a ∉ actionWeightSupport b ⊤) :
    weightFiltration b a r = ⊥ := by
  apply semigroupSubgroup_eq_bot_of_noAmbientWeights hreal hG hS b
  rintro χ ⟨n, hn, hn0, rfl⟩
  exact h n hn hn0

/-- A nonzero character occurs in conjugation precisely when it is a relative root. -/
theorem mem_actionWeightSupport_conjugation_iff
    (i : S.toGrp ⟶ G) {χ : characterLattice S} (hχ : χ ≠ 0) :
    χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤ ↔
      χ ∈ relativeRoots i := by
  constructor
  · rintro ⟨X, hX0, hX, _⟩
    refine ⟨hχ, (Submodule.ne_bot_iff _).mpr ⟨X, ?_, hX0⟩⟩
    simpa only [actionWeightSpace_conjugation] using hX
  · rintro ⟨_, hχ⟩
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    refine ⟨X, hX0, ?_, Subgroup.mem_top _⟩
    simpa only [actionWeightSpace_conjugation] using hX

/-- Root-free positive multiples give a trivial cyclic conjugation tail. -/
theorem weightFiltration_eq_bot_of_noRelativeRoots
    (hreal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (r : ℕ)
    (h : ∀ n : ℕ, r ≤ n → 0 < n → n • a ∉ relativeRoots i) :
    weightFiltration (AutomorphicAction.conjugation i) a r = ⊥ := by
  apply weightFiltration_eq_bot_of_noAmbientWeights hreal hG hS
  intro n hn hn0 hsupport
  exact h n hn hn0
    ((mem_actionWeightSupport_conjugation_iff i
      (hS.nsmul_ne_zero ha (by omega))).mp hsupport)

/-- Without a double root or higher roots, the second conjugation tail vanishes. -/
theorem weightFiltration_two_eq_bot_of_noDoubleRoot
    (hreal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (h2 : 2 • a ∉ relativeRoots i)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    weightFiltration (AutomorphicAction.conjugation i) a 2 = ⊥ := by
  apply weightFiltration_eq_bot_of_noRelativeRoots hreal hG hS i ha
  intro n hn hn0
  by_cases hn2 : n = 2
  · simpa only [hn2] using h2
  · exact hhigh n (by omega)

end RelativeRoot

end Langlands.GroupScheme
