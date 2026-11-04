import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Normality of codimension-one connected unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IteratedCommutator

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A proper subgroup misses a universal word immediately before a word
whose entire image it contains. -/
theorem exists_last_word_not_contained (F : SubgroupFunctor G) (hF : F ≠ ⊤)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    ∃ n, ¬ F.ContainsImage (word G n) ∧ F.ContainsImage (word G (n + 1)) := by
  classical
  have hzero : ¬ F.ContainsImage (word G 0) := by
    intro h
    apply hF
    apply SubgroupFunctor.ext
    intro T
    apply (Subgroup.eq_top_iff' _).2
    intro x
    simpa only [word, Category.comp_id] using h T x
  have h : ∃ d, F.ContainsImage (word G d) := by
    obtain ⟨d, hd⟩ := hNil
    refine ⟨d, ?_⟩
    rw [word_eq_one_of_uniformNilpotence hd]
    intro T v
    rw [MonObj.comp_one]
    exact (F.carrier T).one_mem
  have hpos : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    exact hzero (hz ▸ Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  have he : Nat.find h - 1 + 1 = Nat.find h := by omega
  rw [he]
  exact Nat.find_spec h

/-- If all next universal commutators lie in a subgroup, the preceding
word normalizes it after every scheme refinement. -/
theorem normalizer_containsImage_of_succ_contained
    (F : SubgroupFunctor G) (n : ℕ) (h : F.ContainsImage (word G (n + 1))) :
    F.normalizer.ContainsImage (word G n) := by
  intro T v V a x hx
  let g := (a ≫ v) ≫ word G n
  have hc (y : V ⟶ G.X) : ⁅g, y⁆ ∈ F.carrier V := by
    have hh := h V (lift (a ≫ v) y)
    rw [word_succ_points, lift_fst, lift_snd] at hh
    exact hh
  change g * x * g⁻¹ ∈ F.carrier V ∧ g⁻¹ * x * g ∈ F.carrier V
  constructor
  · have hh := (F.carrier V).mul_mem (hc x) hx
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  · have hh := (F.carrier V).mul_mem ((F.carrier V).inv_mem (hc (g⁻¹ * x * g))) hx
    convert hh using 1
    simp only [commutatorElement_def]
    group

end IteratedCommutator

section NormalizerEnlargement

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]

/-- A proper smooth connected subgroup of a uniformly nilpotent smooth
connected affine group is strictly enlarged by a smooth connected closed
subgroup of its full scheme-theoretic normalizer. -/
theorem exists_smoothConnected_normalizer_enlargement
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (i : K ⟶ G),
      IsClosedSubgroup i ∧ Smooth K.X.hom ∧ IsAffineHom K.X.hom ∧
      ConnectedSpace K.X.left ∧ SubgroupFunctor.range j < SubgroupFunctor.range i ∧
      SubgroupFunctor.range i ≤ (SubgroupFunctor.range j).normalizer := by
  obtain ⟨n, hn, hn'⟩ :=
    IteratedCommutator.exists_last_word_not_contained (SubgroupFunctor.range j) hproper hNil
  let f : H.X ⊗ IteratedCommutator.source G n ⟶ G.X :=
    (fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ IteratedCommutator.word G n)
  have hgood := ImageGeneration.finitePowerGood_tensor _ _
    (IteratedCommutator.source_good (G := H) 0)
    (IteratedCommutator.source_good (G := G) n)
  have : GeometricallyReduced (H.X ⊗ IteratedCommutator.source G n).hom := hgood.2.2.1
  have : GeometricallyIrreducible (H.X ⊗ IteratedCommutator.source G n).hom := hgood.2.2.2
  have hInt : GeometricallyIntegral (H.X ⊗ IteratedCommutator.source G n).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  have hpoint : lift 1 (IteratedCommutator.origin G n) ≫ f = 1 := by
    simp only [f, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd,
      MonObj.one_comp, IteratedCommutator.origin_word, one_mul]
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    (H.X ⊗ IteratedCommutator.source G n) hgood.1 hgood.2.1 hInt
    (lift 1 (IteratedCommutator.origin G n)) f hpoint
  have hHle : SubgroupFunctor.range j ≤ closedImageEnvelope f := by
    intro T x hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hh := closedImageEnvelope_containsImage f T
      (lift h (toUnit T ≫ IteratedCommutator.origin G n))
    simpa only [f, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      Category.assoc, IteratedCommutator.origin_word, MonObj.comp_one, mul_one] using hh
  have hword : (closedImageEnvelope f).ContainsImage (IteratedCommutator.word G n) := by
    intro T v
    have hh := closedImageEnvelope_containsImage f T (lift 1 v)
    simpa only [f, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd,
      MonObj.one_comp, one_mul] using hh
  have hne : closedImageEnvelope f ≠ SubgroupFunctor.range j := by
    intro he
    exact hn (he ▸ hword)
  have hN : (SubgroupFunctor.range j).normalizer.ContainsImage f := by
    intro T v
    rw [show v ≫ f = (v ≫ fst _ _ ≫ j.hom.hom) *
        (v ≫ snd _ _ ≫ IteratedCommutator.word G n) by
      simp only [f, MonObj.comp_mul]]
    apply ((SubgroupFunctor.range j).normalizer.carrier T).mul_mem
    · exact (SubgroupFunctor.range j).le_normalizer T
        (SubgroupFunctor.mem_range.2 ⟨v ≫ fst _ _, by simp⟩)
    · exact IteratedCommutator.normalizer_containsImage_of_succ_contained _ n hn' T
        (v ≫ snd _ _)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, iN, hiN, hrepN⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range j hj).1
  have hDle := closedImageEnvelope_le_of_containsImage f iN hrepN hiN hN
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  refine ⟨D.group, D.inclusion, D.closed, hD.1, hD.2.1,
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom, ?_, ?_⟩
  · rw [D.represents.2]
    exact lt_of_le_of_ne hHle (Ne.symm hne)
  · rwa [D.represents.2]

/-- An actual smooth connected closed enlargement inside the full normalizer
of the supplied subgroup. -/
structure SmoothConnectedNormalizerEnlargement (j : H ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  closed : IsClosedSubgroup inclusion
  smooth : Smooth group.X.hom
  affine : IsAffineHom group.X.hom
  connected : ConnectedSpace group.X.left
  larger : SubgroupFunctor.range j < SubgroupFunctor.range inclusion
  normalizes : SubgroupFunctor.range inclusion ≤ (SubgroupFunctor.range j).normalizer

/-- Choose a smooth connected closed normalizer enlargement over the ground
field from the universal commutator construction. -/
def smoothConnectedNormalizerEnlargement_of_uniformNilpotence
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    SmoothConnectedNormalizerEnlargement j :=
  Classical.choice (by
    obtain ⟨K, i, hi, hKs, hKa, hKc, hstrict, hKle⟩ :=
      exists_smoothConnected_normalizer_enlargement j hj hproper hNil
    exact ⟨⟨K, i, hi, hKs, hKa, hKc, hstrict, hKle⟩⟩)

/-- A smooth connected closed subgroup of codimension at most one is normal
in a uniformly nilpotent smooth connected affine group. -/
theorem isNormal_of_lieDimension_le_succ_of_uniformNilpotence
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hdim : Lie.dimension G ≤ Lie.dimension H + 1)
    (hNil : ∃ d, HasUniformNilpotentPoints G d) :
    (SubgroupFunctor.range j).IsNormal := by
  classical
  by_cases htop : SubgroupFunctor.range j = ⊤
  · rw [htop]
    intro T g x _hg _hx
    trivial
  obtain ⟨K, i, hi, hKs, hKa, hKc, hstrict, hKle⟩ :=
    exists_smoothConnected_normalizer_enlargement j hj htop hNil
  let : Smooth K.X.hom := hKs
  let : IsAffineHom K.X.hom := hKa
  let : ConnectedSpace K.X.left := hKc
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let e : H ⟶ K := hrep.factorHom j hstrict.le
  have he : e ≫ i = j := hrep.factorHom_comp j hstrict.le
  have hec : IsClosedSubgroup e := IsClosedSubgroup.of_comp hi (by rwa [he])
  have hene : ¬ IsIso e := by
    intro h
    let : IsIso e := h
    apply hstrict.ne
    rw [← he]
    exact SubgroupFunctor.range_iso_comp (asIso e) i
  have hHK := Lie.dimension_lt_of_proper_closedSubgroup e hec hene
  have hiIso : IsIso i := by
    by_contra h
    have hKG := Lie.dimension_lt_of_proper_closedSubgroup i hi h
    omega
  let : IsIso i := hiIso
  intro T g x _hg hx
  apply (SubgroupFunctor.range j).isNormalizedBy_normalizer T g x _ hx
  apply hKle T
  apply SubgroupFunctor.mem_range.2
  refine ⟨g ≫ (inv i).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

/-- Every smooth connected codimension-one closed subgroup of a smooth
connected affine unipotent group is normal on all scheme tests. -/
theorem isNormal_of_lieDimension_le_succ_of_isUnipotent
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hdim : Lie.dimension G ≤ Lie.dimension H + 1) (hU : IsUnipotent G) :
    (SubgroupFunctor.range j).IsNormal :=
  isNormal_of_lieDimension_le_succ_of_uniformNilpotence j hj hdim
    (exists_hasUniformNilpotentPoints_of_isUnipotent hU)

end NormalizerEnlargement

end Langlands.GroupScheme
