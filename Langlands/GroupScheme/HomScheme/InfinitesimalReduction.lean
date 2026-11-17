import Langlands.AlgebraicGeometry.AffineTestMorphismProperty
import Langlands.GroupScheme.HomScheme.ConjugatorLifting
import Langlands.GroupScheme.HomScheme.HenselianSplitSourceLifting
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Torus.MultiplicativeTypeInfinitesimalLiftStatement

/-! # Reduction of infinitesimal homomorphism lifting to square-zero tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The square-zero input needed for formal nilpotent induction, uniform over
all affine tests of the fixed base and pair of group schemes. -/
def HasAffineSquareZeroConjugatorLifting (H G : GroupScheme S) : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A), I ^ 2 = ⊥ →
    Langlands.AlgebraicGeometry.affineTestMorphismProperty
      (HasConjugatorLifting H G) (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The specified-conjugator property over square-zero affine tests implies
the same property over every nilpotent affine quotient test. -/
theorem hasConjugatorLifting_nilpotent
    (h : HasAffineSquareZeroConjugatorLifting H G)
    (A : Type u) [CommRing A] (I : Ideal A) (hI : IsNilpotent I) :
    Langlands.AlgebraicGeometry.affineTestMorphismProperty
      (HasConjugatorLifting H G) (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  Langlands.AlgebraicGeometry.affineTestMorphismProperty_nilpotent
    (HasConjugatorLifting H G) h A I hI

/-- Remove the canonical identity pullbacks of a pulled-back homomorphism. -/
theorem removeIdentityBase_map (f : H ⟶ G) :
    (baseChangeIdIso H).inv ≫ (baseChange (𝟙 S)).map f ≫
      (baseChangeIdIso G).hom = f := by
  have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality f
  change (baseChange (𝟙 S)).map f ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso H).hom ≫ f at hn
  rw [hn, Iso.inv_hom_id_assoc]

/-- On the identity test, the actual pulled-back point is the usual base-point
pullback. -/
theorem pulledBackPoint_identity (g : Over.mk (𝟙 S) ⟶ G.X) :
    RelativeLevi.pulledBackPoint G (Over.mk (𝟙 S)) g =
      baseChangeBasePoint (𝟙 S) G g := by
  apply (baseChangeBasePointsEquiv (𝟙 S) G).injective
  rw [baseChangeBasePoint, MulEquiv.apply_symm_apply]
  calc
    _ = g := RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint G
      (Over.mk (𝟙 S)) g
    _ = G.constantPoint g (Over.mk (𝟙 S)) := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp g.left).symm

/-- Conjugating a constant family over the identity test is the identity
pullback of the original conjugation. -/
theorem conjugateRelative_identityBase (f : H ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    conjugateRelative ((baseChange (𝟙 S)).map f) g =
      (baseChange (𝟙 S)).map (f ≫ (G.innerIso g).hom) := by
  rw [Functor.map_comp, baseChange_innerIso_hom]
  unfold conjugateRelative
  rw [pulledBackPoint_identity]
  rfl

/-- Recover actual homomorphism lifts and conjugacy by a point restricting to
the identity from the relative specified-conjugator property. -/
theorem homLifting_of_hasConjugatorLifting {S₀ : Scheme.{u}} (r : S₀ ⟶ S)
    (h : HasConjugatorLifting H G
      (Over.homMk r (by simp) : Over.mk r ⟶ Over.mk (𝟙 S))) :
    (∀ u₀ : (baseChange r).obj H ⟶ (baseChange r).obj G,
      ∃ f : H ⟶ G, (baseChange r).map f = u₀) ∧
    (∀ f f' : H ⟶ G, (baseChange r).map f = (baseChange r).map f' →
      ∃ g : Over.mk (𝟙 S) ⟶ G.X,
        G.constantPoint g (Over.mk r) = 1 ∧ f' = f ≫ (G.innerIso g).hom) := by
  constructor
  · intro u₀
    obtain ⟨i, hi⟩ := h.1 u₀
    refine ⟨(baseChangeIdIso H).inv ≫ i ≫ (baseChangeIdIso G).hom, ?_⟩
    exact (evaluate_identityBase i (Over.mk r)).symm.trans hi
  · intro f f' hf
    let a : Over.mk r ⟶ Over.mk (𝟙 S) := Over.homMk r (by simp)
    have hh : evaluate a ((baseChange (𝟙 S)).map f') =
        conjugateRelative (evaluate a ((baseChange (𝟙 S)).map f)) 1 := by
      rw [conjugateRelative_one]
      exact (evaluate_baseChange a f').trans
        (hf.symm.trans (evaluate_baseChange a f).symm)
    obtain ⟨g, hg, he⟩ := h.2
      ((baseChange (𝟙 S)).map f) ((baseChange (𝟙 S)).map f') 1 hh
    refine ⟨g, hg, ?_⟩
    rw [conjugateRelative_identityBase] at he
    have hremove := congrArg
      (fun i => (baseChangeIdIso H).inv ≫ i ≫ (baseChangeIdIso G).hom) he
    simpa only [removeIdentityBase_map] using hremove

/-- The unchanged published target follows from the square-zero relative
lifting property on every smooth target and multiplicative-type source. -/
theorem multiplicativeTypeInfinitesimalLift_of_squareZero
    (hsq : ∀ (S : Scheme.{u}) (H G : GroupScheme S) [Smooth G.X.hom],
      RelativeMultiplicativeType.IsMultiplicativeType H →
        HasAffineSquareZeroConjugatorLifting H G) :
    MultiplicativeTypeInfinitesimalLiftStatement.{u} := by
  intro A _ J hJ G H _ hH
  let r := Spec.algebraMap A (A ⧸ J)
  have hnil := hasConjugatorLifting_nilpotent (hsq _ H G hH) A J hJ
  apply homLifting_of_hasConjugatorLifting r
  exact hnil (𝟙 _) r (by simp [r, Spec.algebraMap])

end Langlands.GroupScheme.HomScheme
