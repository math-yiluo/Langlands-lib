import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicStandardSiegelRoots
import Langlands.GroupScheme.Rational.StandardMinimalLeviStructure
import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusStatement
import Langlands.GroupScheme.Derived.CentralSplitTorusProductStatement

/-! # Existence of the actual algebraic Siegel setup from three structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Generic minimality makes the canonical empty-index standard parabolic
representative an actual minimal rational parabolic subgroup. -/
theorem Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal
    (hmin : GenericMinimalParabolicStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    IsMinimalParabolicSubgroup (Standard.parabolicHom i ν ∅) := by
  have hF := hmin k G hG T i hi ν hν
  rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν,
    ← (Standard.isRepresentedBy_parabolicHom i ν ∅).2] at hF
  obtain ⟨P', j', hj', heq⟩ := isMinimalParabolicFunctor_iff_exists.mp hF
  refine ⟨hj'.1.of_range_eq (Standard.isClosedSubgroup_parabolicHom i ν ∅) heq, ?_⟩
  intro Q q hq hle
  rw [← heq] at hle ⊢
  exact hj'.2 Q q hq hle

end Langlands.GroupScheme

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme

/-- The exact actual algebraic setup of the Siegel target exists for every
connected reductive group over a number field. This is a proposition target. -/
def SiegelAlgebraicSetupExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j

/-- The supplied product scheme map of two commutative factors is the
underlying map of the published product homomorphism. -/
theorem subgroupProductMap_eq_prodHom {S : Scheme.{u}}
    {A B C : CommGroupScheme S} (a : A ⟶ C) (b : B ⟶ C) :
    subgroupProductMap (CommGroupScheme.groupHom a) (CommGroupScheme.groupHom b) =
      (prodHom (CommGroupScheme.groupHom a) (CommGroupScheme.groupHom b)
        (fun _ _ _ => Commute.all _ _)).hom.hom := by
  have h := comp_prodHom (CommGroupScheme.groupHom a) (CommGroupScheme.groupHom b)
    (fun _ _ _ => Commute.all _ _) (A.X ⊗ B.X) (𝟙 _)
  simpa only [Category.id_comp, productPointsEquiv_fst, productPointsEquiv_snd,
    subgroupProductMap] using h.symm

/-- The generic minimal parabolic, derived maximal split torus and derived/central
split product statements give the actual algebraic Siegel setup. All other clauses
come from published proofs. -/
theorem siegelAlgebraicSetupExistence_of_structural
    (hmin : GenericMinimalParabolicStatement.{u})
    (hder : DerivedMaximalSplitTorusStatement.{u})
    (hprod : DerivedCentralSplitTorusProductStatement.{u}) :
    SiegelAlgebraicSetupExistenceStatement.{u} := by
  intro F _ _ G _ _ hG
  obtain ⟨T, i, -, hi, -⟩ := cocharacterMaximalSplitTorus F G (Dynamic.trivialCocharacter G)
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  obtain ⟨D, d, -, -, hd⟩ := derivedSubgroupRepresentability F G
  obtain ⟨T₀, t₀, e, ht₀, he_closed, he⟩ := hder F G D d hG hd T i hi
  obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement F G hG
  obtain ⟨c, hc, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have hiso := hprod F G D d hG hd T T₀ A i t₀ e a c hi ht₀ he_closed he ha hc
  obtain ⟨-, hRL, hU⟩ := standardMinimalLeviStructure F G T i ν hG hi hν
  refine ⟨T, i, ν, T₀, e, hi, hν,
    Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν hmin hG hi hν,
    hRL, hU, standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    relativeRoots_torusToStandardParabolic F G T i ν hG hi hν,
    ⟨D, d, t₀, hd, ht₀, he⟩, A, c, ?_, ?_⟩
  · rw [hc]
    exact ha
  · rw [subgroupProductMap_eq_prodHom e c]
    exact hiso.surjective

end Langlands.Global.AdelicSiegelFactors
