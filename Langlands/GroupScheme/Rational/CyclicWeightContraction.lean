import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Rational.ActionCharacterWeights
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.RootSubgroup

/-! # Contraction from positive cyclic action support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace AutomorphicAction

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}

/-- The action descends through the specified character to a multiplicative-group
 action for which every point has an identity orbit limit. -/
def IsContractingAlongCharacter (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) : Prop :=
  ∃ e : AutomorphicAction (Gm B).toGrp G,
    e.restrict (CommGroupScheme.groupHom a) = b ∧ e.unipotent = ⊤

end AutomorphicAction

namespace RelativeRoot

section CharacterEquivariance

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G H : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (j : H ⟶ G)
    (e : AutomorphicAction (Gm B).toGrp H)
    (hequiv : ∀ (T : Over B) (s : T ⟶ S.X) (h : T ⟶ H.X),
      e.act (s ≫ (CommGroupScheme.groupHom a).hom.hom) h ≫ j.hom.hom =
        (AutomorphicAction.conjugation i).act s (h ≫ j.hom.hom))

include hequiv

/-- Equivariance along a character sends identity-limit extensions to intrinsic
relative-root extensions on every test scheme. -/
theorem map_unipotent_le_subgroup_of_character_equivariant :
    e.unipotent.map j ≤ subgroup i a := by
  have horbit {T : Over B} (h : T ⟶ H.X) :
      T ◁ (CommGroupScheme.groupHom a).hom.hom ≫ e.orbit h ≫ j.hom.hom =
        orbit i (h ≫ j.hom.hom) := by
    rw [AutomorphicAction.orbit, ← Category.assoc, e.naturality,
      whiskerLeft_snd, whiskerLeft_fst_assoc, hequiv, orbit, Category.assoc]
  intro T g hg
  obtain ⟨h, ⟨f, hf, hf0⟩, rfl⟩ := SubgroupFunctor.mem_map.mp hg
  refine ⟨f ≫ j.hom.hom, ?_, ?_⟩
  · rw [IsOrbitExtension, whiskerLeft_comp, Category.assoc,
      ← Category.assoc (T ◁ AffineLine.unitInclusion B), hf, horbit]
  · rw [Dynamic.evalZero_comp, hf0, MonObj.one_comp]

end CharacterEquivariance

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Every positive cyclic weight is an integral multiple of its generator. -/
theorem semigroupWeightSpan_cyclicTail_le_integralActionWeightSpan
    (b : AutomorphicAction S.toGrp G) (a : characterLattice S) (r : ℕ) :
    semigroupWeightSpan b (cyclicTail a r) ≤ integralActionWeightSpan b a := by
  refine iSup_le fun χ => ?_
  rcases χ with ⟨χ, n, _, _, rfl⟩
  simpa only [natCast_zsmul, integralActionWeightSpan] using
    (le_iSup (fun m : ℤ => actionWeightSpace b (m • a)) (n : ℤ))

section FullGroup

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Positive cyclic support of the full tangent space forces actual contraction
through that character, including when the character is nonprimitive. -/
theorem isContractingAlongCharacter_of_actionWeightSupport_top_subset
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (a : characterLattice S) (ha : a ≠ 0)
    (hsupport : actionWeightSupport b ⊤ ⊆ cyclicTail a 1) :
    b.IsContractingAlongCharacter a := by
  have hstable : b.IsStable (⊤ : SubgroupFunctor G) := fun _ _ _ _ => trivial
  have hspan : semigroupWeightSpan b (cyclicTail a 1) = ⊤ := by
    apply top_unique
    exact (actionWeightSupport_subset_iff_tangentSubmodule_le
      b hS (𝟙 G) (SubgroupFunctor.top_isRepresentedBy_id G) hstable
      (cyclicTail a 1)).mp hsupport
  have hint : integralActionWeightSpan b a = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact semigroupWeightSpan_cyclicTail_le_integralActionWeightSpan b a 1
  have hkernel := b.kernelActsTrivially_of_integralActionWeightSpan_eq_top a hS hint
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k S hS a ha
  let := hqc
  let := hflat
  let := hsurj
  let e := b.quotientAction (CommGroupScheme.groupHom a) hkernel
  have he : e.restrict (CommGroupScheme.groupHom a) = b :=
    AutomorphicAction.quotientAction_restrict b _ hkernel
  refine ⟨e, he, e.unipotent_eq_top_of_positiveWeightSpan_eq_top ?_⟩
  apply positiveWeightSpan_eq_top_of_restrict_character e hS a ha
  rw [he]
  exact hspan

end FullGroup

/-- Every smooth connected invariant generator with positive cyclic support lies
in the intrinsic character-orbit subgroup. Ambient connectedness is unnecessary. -/
theorem le_subgroup_of_isSemigroupGenerator_cyclicTail
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)
    {F : SubgroupFunctor G}
    (hF : IsSemigroupGenerator (AutomorphicAction.conjugation i) (cyclicTail a 1) F) :
    F ≤ subgroup i a := by
  obtain ⟨⟨H, j, hj, hc, hs, hconn⟩, hstable, hsupport⟩ := hF
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hconn
  let : IsClosedImmersion j.hom.hom.left := hc
  let : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let b := AutomorphicAction.conjugation i
  let d := b.onRepresentedSubgroup j hj hstable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (h : T ⟶ H.X), d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom) :=
    fun _ s h => b.onRepresentedSubgroup_act_comp j hj hstable s h
  have hsupp : actionWeightSupport d ⊤ ⊆ cyclicTail a 1 := by
    rw [← actionWeightSupport_map j hj.1 d b hequiv ⊤,
      SubgroupFunctor.map_top, hj.2]
    exact hsupport
  obtain ⟨e, he, htop⟩ :=
    isContractingAlongCharacter_of_actionWeightSupport_top_subset d hS a ha hsupp
  have hem : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (h : T ⟶ H.X),
      e.act (s ≫ (CommGroupScheme.groupHom a).hom.hom) h ≫ j.hom.hom =
        b.act s (h ≫ j.hom.hom) := by
    intro T s h
    rw [← AutomorphicAction.restrict_act, he]
    exact hequiv T s h
  have hmap := map_unipotent_le_subgroup_of_character_equivariant i a j e hem
  rw [htop, SubgroupFunctor.map_top, hj.2] at hmap
  exact hmap

/-- The first generated cyclic-tail functor is contained in the intrinsic root
functor over every field, for every split torus and nonzero character. -/
theorem weightFiltration_one_le_subgroup
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0) :
    weightFiltration (AutomorphicAction.conjugation i) a 1 ≤ subgroup i a := by
  exact (semigroupSubgroup_le_iff _ _ _).mpr
    (fun _ hF => le_subgroup_of_isSemigroupGenerator_cyclicTail hS i a ha hF)

end RelativeRoot

end Langlands.GroupScheme
