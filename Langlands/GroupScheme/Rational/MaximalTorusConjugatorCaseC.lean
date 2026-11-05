import Langlands.GroupScheme.Rational.MaximalTorusConjugatorReductionCases
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorGeometricConjugacy
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Assembly of the generic semisimple-centralizer case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Generic conjugation data for Case C.** Every maximal torus `j₀` of a smooth connected
affine group `G` over a field with a noncentral geometric semisimple Lie element admits: a field
`K` over `k` whose rational function fields are rational function fields over `k`; a smooth
connected affine closed subgroup `i : H ⟶ G_K` of smaller Lie dimension; an algebraically closed
field `Ω` over `K`; and a point `c : Spec Ω ⟶ G_K` whose image in `G` is dense and which
conjugates the base change of `j₀` into `H` over every test scheme. -/
def SemisimpleCentralizerConjugationDataStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ → HasNoncentralGeometricSemisimpleElement G →
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
        ReducesRationalFunctionFields (algebraBaseMap k K) ∧
        ∃ (H : GroupScheme (Spec (CommRingCat.of K))) (_ : Smooth H.X.hom)
          (_ : IsAffineHom H.X.hom) (_ : ConnectedSpace H.X.left)
          (i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G),
          IsClosedSubgroup i ∧ Lie.dimension H < Lie.dimension G ∧
          ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra K Ω) (_ : IsAlgClosed Ω)
            (c : Over.mk (algebraBaseMap K Ω) ⟶
              ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X),
            DenseRange (baseChangePointsEquiv (algebraBaseMap k K) G
              (Over.mk (algebraBaseMap K Ω)) c).left ∧
            ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Over.mk (algebraBaseMap K Ω))
              (t : V ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X),
              t ∈ ((SubgroupFunctor.range j₀).baseChange (algebraBaseMap k K)).carrier V →
                (y ≫ c) * t * (y ≫ c)⁻¹ ∈ (SubgroupFunctor.range i).carrier V

/-- Generic conjugation data give Case C, assuming maximal-torus conjugacy over algebraically
closed fields and stability of maximal tori under field extension. -/
theorem semisimpleCentralizerConjugatorReduction_of_data
    (hconj : MaximalTorusConjugacyStatement.{u}) (hbc : MaximalTorusBaseChangeStatement.{u})
    (hD : SemisimpleCentralizerConjugationDataStatement.{u}) :
    SemisimpleCentralizerConjugatorReductionStatement.{u} := by
  intro k _ G _ _ _ T₀ j₀ hj₀ hS
  obtain ⟨K, _, _, hb, H, _, _, _, i, hi, hdim, Ω, _, _, _, c, hcd, hc⟩ :=
    hD k G T₀ j₀ hj₀ hS
  obtain ⟨T, j, hj⟩ := maximalTorusExistence K H
  obtain ⟨h₁, hconjY⟩ := exists_torusConjugator_of_conj_mem_range hconj hbc hj₀ hj hi c hc
  refine ⟨K, inferInstance, algebraBaseMap k K, hb, H, inferInstance, inferInstance,
    inferInstance, T, j, i, Over.mk (algebraBaseMap K Ω), (h₁ ≫ i.hom.hom) * c, hj, hdim, ?_⟩
  exact isTorusConjugatorTransfer_of_translate (TorusExistence.flat_algebraBaseMap Ω)
    (TorusExistence.surjective_algebraBaseMap Ω)
    (by change QuasiCompact (Spec.map _); infer_instance) h₁ c hconjY hcd

/-- Case B, generic conjugation data, maximal-torus conjugacy over algebraically closed fields
and stability of maximal tori under field extension give unirationality of every actual
parameter scheme. -/
theorem maximalTorusParameterUnirational_of_isogeny_data
    (hB : MaximalTorusIsogenyReductionStatement.{u})
    (hconj : MaximalTorusConjugacyStatement.{u}) (hbc : MaximalTorusBaseChangeStatement.{u})
    (hD : SemisimpleCentralizerConjugationDataStatement.{u}) :
    MaximalTorusParameterUnirationalStatement.{u} :=
  maximalTorusParameterUnirational_of_cases hB
    (semisimpleCentralizerConjugatorReduction_of_data hconj hbc hD)

end Langlands.GroupScheme
