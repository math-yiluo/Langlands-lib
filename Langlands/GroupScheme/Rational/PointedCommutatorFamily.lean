import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Rational.AffineLineExtensions

/-! # Universal commutator families beginning with a pointed morphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PointedCommutatorFamily

variable {B : Scheme.{u}} {G : GroupScheme B} {V : Over B}

/-- The source of a family obtained from `V` by adjoining `n` group parameters. -/
@[reducible] def source (G : GroupScheme B) (V : Over B) : ℕ → Over B
  | 0 => V
  | n + 1 => source G V n ⊗ G.X

/-- Start with the supplied morphism, then bracket with each new group parameter. -/
def word (f : V ⟶ G.X) : (n : ℕ) → source G V n ⟶ G.X
  | 0 => f
  | n + 1 => ⁅fst (source G V n) G.X ≫ word f n, snd (source G V n) G.X⁆

theorem word_succ_points (f : V ⟶ G.X) (n : ℕ) {T : Over B}
    (v : T ⟶ source G V (n + 1)) :
    v ≫ word f (n + 1) =
      ⁅(v ≫ fst (source G V n) G.X) ≫ word f n,
        v ≫ snd (source G V n) G.X⁆ := by
  change v ≫ ⁅fst (source G V n) G.X ≫ word f n,
    snd (source G V n) G.X⁆ = _
  simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv,
    Category.assoc]

/-- The whole parameter scheme left after setting the initial variable to its basepoint. -/
@[reducible] def parameters (G : GroupScheme B) : ℕ → Over B
  | 0 => 𝟙_ (Over B)
  | n + 1 => parameters G n ⊗ G.X

/-- Set the initial variable to the basepoint and retain every group parameter. -/
def basepointSection (v₀ : 𝟙_ (Over B) ⟶ V) :
    (n : ℕ) → parameters G n ⟶ source G V n
  | 0 => v₀
  | n + 1 => basepointSection v₀ n ⊗ₘ 𝟙 G.X

/-- Every commutator family is identically the unit along this entire section. -/
theorem basepointSection_word (v₀ : 𝟙_ (Over B) ⟶ V)
    (f : V ⟶ G.X) (hf : v₀ ≫ f = 1) (n : ℕ) :
    basepointSection (G := G) v₀ n ≫ word f n = 1 := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [word_succ_points]
    simp only [basepointSection, tensorHom_fst, tensorHom_snd,
      Category.comp_id, Category.assoc, ih, MonObj.comp_one]
    simp

/-- A rational basepoint in each family source. -/
def origin (v₀ : 𝟙_ (Over B) ⟶ V) :
    (n : ℕ) → 𝟙_ (Over B) ⟶ source G V n
  | 0 => v₀
  | n + 1 => lift (origin v₀ n) 1

theorem origin_word (v₀ : 𝟙_ (Over B) ⟶ V)
    (f : V ⟶ G.X) (hf : v₀ ≫ f = 1) (n : ℕ) :
    origin (G := G) v₀ n ≫ word f n = 1 := by
  cases n with
  | zero => exact hf
  | succ n =>
    rw [word_succ_points, origin, lift_fst, lift_snd]
    simp

/-- Each family value lies in the matching lower central term on every test. -/
theorem word_mem_lowerCentralSeries (f : V ⟶ G.X) (n : ℕ)
    {T : Over B} (v : T ⟶ source G V n) :
    v ≫ word f n ∈ (⊤ : Subgroup (T ⟶ G.X)).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [word_succ_points, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator (ih _) (Subgroup.mem_top _)

/-- Vanishing of the next whole family puts the preceding image in the centre
on every scheme test and refinement. -/
theorem center_containsImage_of_succ_eq_one (f : V ⟶ G.X) (n : ℕ)
    (h : word f (n + 1) = 1) :
    (center G).ContainsImage (word f n) := by
  intro T v T' a g
  apply commutatorElement_eq_one_iff_commute.1
  have hh := congrArg (fun t => lift (a ≫ v) g ≫ t) h
  rw [word_succ_points, lift_fst, lift_snd, MonObj.comp_one] at hh
  simpa only [Category.assoc] using hh

section Field

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))}

/-- Uniform nilpotence kills the family with that many commutators. -/
theorem word_eq_one_of_uniformNilpotence (f : V ⟶ G.X)
    {d : ℕ} (hd : HasUniformNilpotentPoints G d) : word f d = 1 := by
  have hm := word_mem_lowerCentralSeries f d (𝟙 (source G V d))
  rw [Category.id_comp, hd (source G V d), Subgroup.mem_bot] at hm
  exact hm

/-- A nontrivial initial morphism has a last nontrivial family before a
uniform nilpotence bound. -/
theorem exists_last_nontrivial_word (f : V ⟶ G.X) (hf : f ≠ 1)
    (h : ∃ d, HasUniformNilpotentPoints G d) :
    ∃ n, word f n ≠ 1 ∧ word f (n + 1) = 1 := by
  classical
  have hzero : word f 0 ≠ 1 := hf
  have h' : ∃ d, word f d = 1 := by
    obtain ⟨d, hd⟩ := h
    exact ⟨d, word_eq_one_of_uniformNilpotence f hd⟩
  have hpos : 0 < Nat.find h' := by
    by_contra hn
    have hz : Nat.find h' = 0 := by omega
    exact hzero (hz ▸ Nat.find_spec h')
  refine ⟨Nat.find h' - 1, Nat.find_min h' (by omega), ?_⟩
  have he : Nat.find h' - 1 + 1 = Nat.find h' := by omega
  rw [he]
  exact Nat.find_spec h'

/-- The universal sources retain affine geometrically integral finite type
geometry when the initial source and the group have it. -/
theorem source_good [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (hV : ImageGeneration.FinitePowerGood _ V) (n : ℕ) :
    ImageGeneration.FinitePowerGood _ (source G V n) := by
  have hG := smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  have hgood := ImageGeneration.finitePowerGood_of_geometricallyIntegral G.X
    inferInstance inferInstance hG
  induction n with
  | zero => exact hV
  | succ n ih => exact ImageGeneration.finitePowerGood_tensor _ _ ih hgood

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

/-- Centralize a nontrivial pointed morphism without choosing rational points
of the ambient group: the last nontrivial universal family generates an actual
nontrivial smooth connected central closed subgroup. The factor through it
remains the unit on the whole basepoint section. -/
theorem exists_central_generatedImage
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hV : ImageGeneration.FinitePowerGood _ V)
    (v₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V)
    (f : V ⟶ G.X) (hf₀ : v₀ ≫ f = 1) (hf : f ≠ 1)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    ∃ (n : ℕ) (D : GeneratedImage (word f n)),
      Smooth D.group.X.hom ∧ IsAffineHom D.group.X.hom ∧
      GeometricallyConnected D.group.X.hom ∧ ConnectedSpace D.group.X.left ∧
      IsCentral D.inclusion ∧ SubgroupFunctor.range D.inclusion ≠ ⊥ ∧
      word f n ≠ 1 ∧ basepointSection (G := G) v₀ n ≫ D.factor = 1 := by
  obtain ⟨n, hn, hn'⟩ := exists_last_nontrivial_word f hf hNil
  have hgood := source_good (G := G) hV n
  have : GeometricallyReduced (source G V n).hom := hgood.2.2.1
  have : GeometricallyIrreducible (source G V n).hom := hgood.2.2.2
  have hInt : GeometricallyIntegral (source G V n).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    (source G V n) hgood.1 hgood.2.1 hInt (origin v₀ n) (word f n)
    (origin_word v₀ f hf₀ n)
  have hcent := closedImageEnvelope_le_center (word f n)
    (center_containsImage_of_succ_eq_one f n hn')
  have hRange : SubgroupFunctor.range D.inclusion ≠ ⊥ := by
    intro hz
    have hm : word f n ∈ (SubgroupFunctor.range D.inclusion).carrier (source G V n) :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, D.factor_comp⟩
    rw [hz, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
    exact hn hm
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  refine ⟨n, D, hD.1, hD.2.1, hD.2.2.1,
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom,
    ?_, hRange, hn, ?_⟩
  · intro T v
    apply hcent T
    rw [← D.represents.2]
    exact SubgroupFunctor.mem_range.2 ⟨v, rfl⟩
  · let : Mono D.inclusion.hom.hom := D.represents.1
    apply (cancel_mono D.inclusion.hom.hom).1
    rw [Category.assoc, D.factor_comp, MonObj.one_comp]
    exact basepointSection_word v₀ f hf₀ n

/-- A nonconstant affine-line map into an actual smooth connected affine
unipotent group yields a nontrivial central family with the entire zero section
still killed, over every field and in every characteristic. -/
theorem exists_central_generatedImage_of_not_hasConstantAffineLineMaps
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : ¬ HasConstantAffineLineMaps G) :
    ∃ (a : AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X) (n : ℕ)
      (D : GeneratedImage (word (affineLineDifference a) n)),
      Smooth D.group.X.hom ∧ IsAffineHom D.group.X.hom ∧
      GeometricallyConnected D.group.X.hom ∧ ConnectedSpace D.group.X.left ∧
      IsCentral D.inclusion ∧ SubgroupFunctor.range D.inclusion ≠ ⊥ ∧
      word (affineLineDifference a) n ≠ 1 ∧
      basepointSection (G := G) (AffineLine.zeroSection _) n ≫ D.factor = 1 := by
  classical
  have hex : ∃ a : AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X,
      affineLineDifference a ≠ 1 := by
    by_contra! hn
    apply hG
    intro a
    exact ⟨AffineLine.zeroSection _ ≫ a, (affineLineDifference_eq_one_iff a).1 (hn a)⟩
  obtain ⟨a, ha⟩ := hex
  have hA : ImageGeneration.FinitePowerGood _
      (AffineLine.scheme (Spec (CommRingCat.of k))) :=
    ImageGeneration.finitePowerGood_of_geometricallyIntegral _
      (by dsimp [AffineLine.scheme]; infer_instance)
      (by dsimp [AffineLine.scheme]; infer_instance)
      (by dsimp [AffineLine.scheme]; infer_instance)
  obtain ⟨n, D, hD⟩ := exists_central_generatedImage hA (AffineLine.zeroSection _)
    (affineLineDifference a) (zeroSection_comp_affineLineDifference a) ha
    (exists_hasUniformNilpotentPoints_of_isUnipotent hU)
  exact ⟨a, n, D, hD⟩

end Field

end PointedCommutatorFamily

end Langlands.GroupScheme
