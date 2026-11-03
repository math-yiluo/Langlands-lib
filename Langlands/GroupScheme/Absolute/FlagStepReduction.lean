import Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeSteps
import Langlands.GroupScheme.Absolute.BorelProperQuotientStatement
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverStatement
import Langlands.GroupScheme.Absolute.FlagQuotientFixedContainment
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SchemeActionInvariantOpen

/-! # Conditional assembly of the flag step from its geometric inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Construct the factor through an arbitrary Borel from the proper-quotient,
invariant-affine-cover, conjugacy, and generic unipotent-fixedness inputs. -/
def factorThroughBorelOfFlagInputs
    (hproper : SomeBorelQuotientProperStatement.{u})
    (hcover : FlagInvariantAffineOpenCoverStatement.{u})
    (hconj : BorelConjugacyStatement.{u})
    (hfixed : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (U : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left],
      IsUnipotent U → ∀ (Q : Over (Spec (CommRingCat.of k))),
      IsProper Q.hom → ∀ (a : SchemeAction U Q),
      (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
        ∃ V : Q.left.Opens, Set.range x.left ⊆ V ∧ IsAffine V ∧ a.IsInvariantOpen V) →
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q, a.IsFixed x)
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (ht : IsMaximalTorus t)
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (hi : IsClosedSubgroup i) (hUs : Smooth U.X.hom)
    (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U)
    (hthrough : ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
      IsBorelSubgroup b' → SubgroupFunctor.range t ≤ SubgroupFunctor.range b' →
        SubgroupFunctor.range i ≤ SubgroupFunctor.range b')
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (hb : IsBorelSubgroup b) : {f : U ⟶ B // f ≫ b = i} := by
  classical
  apply Classical.choice
  have : Smooth U.X.hom := hUs
  have : ConnectedSpace U.X.left := hUc
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨B₀, b₀, hb₀, hQproper⟩ := hproper k G inferInstance
  obtain ⟨Q, q, hsep, hlft, hqc, hqs, hsur, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B₀ b₀ hb₀.isClosedSubgroup hb₀.smooth
  have : IsSeparated Q.hom := hsep
  have : LocallyOfFiniteType Q.hom := hlft
  have : QuasiCompact Q.hom := hqc
  have : Smooth q.left := hqs
  have : Surjective q.left := hsur
  have : QuasiCompact q.left := hqqc
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b₀) q hfib
  have hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q := by
    intro Z g h
    exact Dynamic.flagQuotientSchemeAction_act_lift G (SubgroupFunctor.range b₀) q hfib g h
  have hP : IsProper Q.hom := hQproper Q q hsep hlft hqc hqs hsur hqqc hfib
  have hV : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
      ∃ V : Q.left.Opens,
        Set.range x.left ⊆ V ∧ IsAffine V ∧ (a.restrict i).IsInvariantOpen V := by
    intro x
    obtain ⟨V, hVa, hx, hVi⟩ := hcover k G T t ht U i hi hUs hUc hUu hthrough
      B₀ b₀ hb₀ Q q hsep hlft hqc inferInstance hsur hqqc hfib a hact x
    exact ⟨V, hx, hVa, hVi⟩
  have hF := hfixed k U hUu Q hP (a.restrict i) hV
  exact ⟨factorThroughBorelOfFixedQuotient hconj k G B₀ b₀ hb₀ U i hi Q q hfib
    a hact hF B b hb⟩

/-- The constructed factors give the exact flag-step conclusion once the four
explicit geometric inputs have been proved. -/
theorem unipotentTorusBorelsToAllBorels_of_geometric_inputs
    (hproper : SomeBorelQuotientProperStatement.{u})
    (hcover : FlagInvariantAffineOpenCoverStatement.{u})
    (hconj : BorelConjugacyStatement.{u})
    (hfixed : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (U : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left],
      IsUnipotent U → ∀ (Q : Over (Spec (CommRingCat.of k))),
      IsProper Q.hom → ∀ (a : SchemeAction U Q),
      (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q,
        ∃ V : Q.left.Opens, Set.range x.left ⊆ V ∧ IsAffine V ∧ a.IsInvariantOpen V) →
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q, a.IsFixed x) :
    UnipotentTorusBorelsToAllBorelsStatement.{u} := by
  intro k _ _ G _ _ _ T t ht U i hi hUs hUc hUu hthrough B b hb
  let f := factorThroughBorelOfFlagInputs hproper hcover hconj hfixed k G T t ht
    U i hi hUs hUc hUu hthrough B b hb
  exact SubgroupFunctor.range_le_of_factor f.val f.property

end Langlands.GroupScheme
