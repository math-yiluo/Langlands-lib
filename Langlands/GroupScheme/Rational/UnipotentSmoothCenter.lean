import Langlands.GroupScheme.Rational.UnipotentPointsNilpotent
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.ImageEnvelopeStabilityProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Rational.Characters

/-! # Smooth stable central subgroups from uniform nilpotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IteratedCommutator

variable {B : Scheme.{u}} (G : GroupScheme B)

/-- The actual source of the left-nested commutator of length `n+1`. -/
@[reducible] def source : ℕ → Over B
  | 0 => G.X
  | n + 1 => source n ⊗ G.X

/-- The zeroth morphism is the identity; each successor brackets with one
further arbitrary point of the ambient group. -/
def word : (n : ℕ) → source G n ⟶ G.X
  | 0 => 𝟙 G.X
  | n + 1 => ⁅fst (source G n) G.X ≫ word n, snd (source G n) G.X⁆

theorem word_succ_points (n : ℕ) {T : Over B} (v : T ⟶ source G (n + 1)) :
    v ≫ word G (n + 1) =
      ⁅(v ≫ fst (source G n) G.X) ≫ word G n,
        v ≫ snd (source G n) G.X⁆ := by
  change v ≫ ⁅fst (source G n) G.X ≫ word G n, snd (source G n) G.X⁆ = _
  simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv,
    Category.assoc]

/-- The unit tuple in the iterated source. -/
def origin : (n : ℕ) → 𝟙_ (Over B) ⟶ source G n
  | 0 => 1
  | n + 1 => lift (origin n) 1

theorem origin_word (n : ℕ) : origin G n ≫ word G n = 1 := by
  cases n with
  | zero => simp [origin, word]
  | succ n =>
    rw [word_succ_points, origin, lift_fst, lift_snd]
    simp

/-- Every word value belongs to the corresponding abstract lower central term. -/
theorem word_mem_lowerCentralSeries (n : ℕ) {T : Over B} (v : T ⟶ source G n) :
    v ≫ word G n ∈ (⊤ : Subgroup (T ⟶ G.X)).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [word_succ_points, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator (ih _) (Subgroup.mem_top _)

variable {G}

/-- Vanishing of the next universal word puts the preceding whole source in
the all-refinement centre. -/
theorem center_containsImage_of_succ_eq_one (n : ℕ) (h : word G (n + 1) = 1) :
    (center G).ContainsImage (word G n) := by
  intro T v T' a g
  apply commutatorElement_eq_one_iff_commute.1
  have hh := congrArg (fun f => lift (a ≫ v) g ≫ f) h
  rw [word_succ_points, lift_fst, lift_snd, MonObj.comp_one] at hh
  simpa only [Category.assoc] using hh

variable {H : GroupScheme B} (b : AutomorphicAction H G)

/-- The diagonal action on the actual nested source. -/
def action : (n : ℕ) → PointwiseSchemeAction H (source G n)
  | 0 => b.toPointwiseSchemeAction
  | n + 1 => (action n).prod b.toPointwiseSchemeAction

theorem word_equivariant (n : ℕ) :
    (action b n).IsEquivariant b.toPointwiseSchemeAction (word G n) := by
  induction n with
  | zero =>
    intro T h v
    change b.act h v ≫ 𝟙 G.X = b.act h (v ≫ 𝟙 G.X)
    simp only [Category.comp_id]
  | succ n ih =>
    intro T h v
    change ((action b n).prod b.toPointwiseSchemeAction).act h v ≫ word G (n + 1) =
      b.act h (v ≫ word G (n + 1))
    rw [word_succ_points, word_succ_points]
    simp only [PointwiseSchemeAction.prod_act_fst,
      PointwiseSchemeAction.prod_act_snd, AutomorphicAction.toPointwiseSchemeAction_act,
      commutatorElement_def, b.act_mul_right, b.act_inv]
    rw [ih T h (v ≫ fst (source G n) G.X)]
    rfl

end IteratedCommutator

section CenterEnvelope

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The centre itself is a closed represented subgroup over a field. -/
theorem center_hasClosedRepresentative : (center G).HasClosedRepresentative := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hc : (SubgroupFunctor.range (𝟙 G)).centralizer = center G := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    constructor
    · intro hg T' a h
      exact hg T' a h (SubgroupFunctor.mem_range.2 ⟨h, by simp⟩)
    · intro hg T' a h _hh
      exact hg T' a h
  rw [← hc]
  exact (hasClosedRepresentative_normalizer_centralizer_range (𝟙 G)
    (by
      change IsClosedImmersion (𝟙 G.X.left)
      infer_instance)).2

/-- Minimality makes an image envelope central whenever its source is central.
No global product decomposition of arbitrary subgroup points is required. -/
theorem closedImageEnvelope_le_center {V : Over (Spec (CommRingCat.of k))}
    (f : V ⟶ G.X) (hf : (center G).ContainsImage f) :
    closedImageEnvelope f ≤ center G := by
  obtain ⟨C, c, hc, hrep⟩ := center_hasClosedRepresentative (G := G)
  exact closedImageEnvelope_le_of_containsImage f c hrep hc hf

end CenterEnvelope

namespace IteratedCommutator

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A uniform lower central bound kills the universal word of that index. -/
theorem word_eq_one_of_uniformNilpotence {d : ℕ} (hd : HasUniformNilpotentPoints G d) :
    word G d = 1 := by
  have hm := word_mem_lowerCentralSeries G d (𝟙 (source G d))
  rw [Category.id_comp, hd (source G d), Subgroup.mem_bot] at hm
  exact hm

/-- A nontrivial group with a finite universal word bound has a last nonzero
word immediately before its first zero word. -/
theorem exists_last_nontrivial_word
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥)
    (h : ∃ d, word G d = 1) :
    ∃ n, word G n ≠ 1 ∧ word G (n + 1) = 1 := by
  classical
  have hzero : word G 0 ≠ 1 := by
    intro hz
    apply hG
    apply SubgroupFunctor.ext
    intro T
    change (SubgroupFunctor.range (𝟙 G)).carrier T = ⊥
    apply le_antisymm _ bot_le
    intro x _hx
    change x = 1
    have hh := congrArg (fun f => x ≫ f) hz
    simpa only [word, Category.comp_id, MonObj.comp_one] using hh
  have hpos : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    exact hzero (hz ▸ Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  have he : Nat.find h - 1 + 1 = Nat.find h := by omega
  rw [he]
  exact Nat.find_spec h

/-- Every nested source has the geometric properties needed by pointed image
generation when the ambient group is smooth, connected and affine. -/
theorem source_good [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (n : ℕ) :
    ImageGeneration.FinitePowerGood _ (source G n) := by
  have hG := smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have hgood := ImageGeneration.finitePowerGood_of_geometricallyIntegral G.X
    inferInstance inferInstance hG
  induction n with
  | zero => exact hgood
  | succ n ih =>
    exact ImageGeneration.finitePowerGood_tensor _ _ ih hgood

end IteratedCommutator

/-- An actual nontrivial smooth connected central closed subgroup stable under
the given action, together with its restricted action and equivariant inclusion. -/
def HasNontrivialSmoothStableCentralSubgroup
    {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction H G) : Prop :=
  ∃ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G)
    (bZ : AutomorphicAction H Z),
    IsClosedSubgroup z ∧ Smooth Z.X.hom ∧ IsAffineHom Z.X.hom ∧
    GeometricallyConnected Z.X.hom ∧ ConnectedSpace Z.X.left ∧ IsCentral z ∧
    b.IsStable (SubgroupFunctor.range z) ∧ SubgroupFunctor.range z ≠ ⊥ ∧
    ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ Z.X),
      bZ.act h v ≫ z.hom.hom = b.act h (v ≫ z.hom.hom)

section Construction

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The last nontrivial universal commutator generates a nontrivial smooth
stable central closed subgroup over any field. -/
theorem hasNontrivialSmoothStableCentralSubgroup_of_uniformNilpotence
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    HasNontrivialSmoothStableCentralSubgroup b := by
  obtain ⟨d, hd⟩ := hNil
  obtain ⟨n, hn, hn'⟩ := IteratedCommutator.exists_last_nontrivial_word hG
    ⟨d, IteratedCommutator.word_eq_one_of_uniformNilpotence hd⟩
  have hgood := IteratedCommutator.source_good (G := G) n
  have : GeometricallyReduced (IteratedCommutator.source G n).hom := hgood.2.2.1
  have : GeometricallyIrreducible (IteratedCommutator.source G n).hom := hgood.2.2.2
  have hInt : GeometricallyIntegral (IteratedCommutator.source G n).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    (IteratedCommutator.source G n) hgood.1 hgood.2.1 hInt
    (IteratedCommutator.origin G n) (IteratedCommutator.word G n)
    (IteratedCommutator.origin_word G n)
  have hStable := b.closedImageEnvelope_isStable hH (IteratedCommutator.action b n)
    (IteratedCommutator.word G n) (IteratedCommutator.word_equivariant b n)
  have hcent := closedImageEnvelope_le_center (IteratedCommutator.word G n)
    (IteratedCommutator.center_containsImage_of_succ_eq_one n hn')
  have hRange : SubgroupFunctor.range D.inclusion ≠ ⊥ := by
    intro hz
    have hf : IteratedCommutator.word G n ∈
        (SubgroupFunctor.range D.inclusion).carrier (IteratedCommutator.source G n) :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, D.factor_comp⟩
    rw [hz, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hf
    exact hn hf
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  refine ⟨D.group, D.inclusion, D.action b hStable, D.closed, hD.1, hD.2.1,
    hD.2.2.1, GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom,
    ?_, ?_, hRange, ?_⟩
  · intro T v
    apply hcent T
    rw [← D.represents.2]
    exact SubgroupFunctor.mem_range.2 ⟨v, rfl⟩
  · rwa [D.represents.2]
  · intro T h v
    exact D.action_act_comp b hStable h v

/-- In particular the construction applies to every nontrivial smooth connected
affine unipotent group and every affine acting group over any field. -/
theorem hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    HasNontrivialSmoothStableCentralSubgroup b :=
  hasNontrivialSmoothStableCentralSubgroup_of_uniformNilpotence b hH hG
    (exists_hasUniformNilpotentPoints_of_isUnipotent hU)

end Construction

end Langlands.GroupScheme
