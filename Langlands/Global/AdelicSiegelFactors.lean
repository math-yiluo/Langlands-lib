import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.RelativeRootChamber
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Actual adelic compact factors and chamber products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Opposite
open scoped CategoryTheory.MonObj NNReal Topology Pointwise

namespace Langlands.Global

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (H G : GroupScheme (Spec (CommRingCat.of F)))

/-- The algebraic structural condition that every ambient rational character
restricts trivially along the actual morphism. -/
def CharactersTrivialAlong (f : H ⟶ G) : Prop :=
  ∀ χ : AlgebraicCharacter F G, f ≫ χ = 1

omit [NumberField F] in
/-- The identity-valued algebraic character evaluates to the identity unit. -/
@[simp] theorem characterUnits_one
    (A : CommAlgCat.{u} (CommRingCat.of F)) (x : H.affinePoints A) :
    characterUnits F H (1 : AlgebraicCharacter F H) A x = 1 := by
  simp [characterUnits, GroupScheme.affinePointsTarget_apply]

/-- Algebraic character triviality implies the genuine adelic norm-one inclusion. -/
theorem range_le_normOne_of_charactersTrivialAlong (f : H ⟶ G)
    (hf : CharactersTrivialAlong F H G f) :
    (map F H G f).toMonoidHom.range ≤ normOneSubgroup F G := by
  rintro _ ⟨x, rfl⟩
  apply (mem_normOneSubgroup F G _).mpr
  intro χ
  change characterNorm F G χ (map F H G f x) = 1
  rw [← characterNorm_comp, hf χ]
  change IdeleAbsoluteValue.full F (characterUnits F H 1 _ x) = 1
  rw [characterUnits_one, map_one]

end AdelicGroupPoints

namespace AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Actual closed group-scheme models of the shared standard unipotent and Levi
functors for the empty simple-root subset. Minimality is a separate obligation. -/
structure StandardFactorData [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) where
  unipotent : GroupScheme (Spec (CommRingCat.of F))
  levi : GroupScheme (Spec (CommRingCat.of F))
  unipotentInclusion : unipotent ⟶ G
  leviInclusion : levi ⟶ G
  unipotent_closed : IsClosedSubgroup unipotentInclusion
  levi_closed : IsClosedSubgroup leviInclusion
  unipotent_represents : (standardUnipotent i ν ∅).IsRepresentedBy unipotentInclusion
  levi_represents : (standardLevi i ν ∅).IsRepresentedBy leviInclusion

/-- The compact data in the actual unipotent group, actual norm-one Levi,
and actual ambient adelic group. Existence and maximality are not assumed. -/
structure CompactFactors
    (N M : GroupScheme (Spec (CommRingCat.of F))) where
  omegaN : Set (AdelicGroupPoints F N)
  omegaM : Set (normOneSubgroup F M)
  compact_omegaN : IsCompact omegaN
  compact_omegaM : IsCompact omegaM
  compactSubgroup : Subgroup (AdelicGroupPoints F G)
  compact_compactSubgroup : IsCompact (compactSubgroup : Set (AdelicGroupPoints F G))

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (D : StandardFactorData F G T i ν)
  (C : CompactFactors F G D.unipotent D.levi)

/-- The unipotent factor really maps into the shared standard unipotent functor. -/
theorem unipotent_mem_standard (n : AdelicGroupPoints F D.unipotent) :
    map F D.unipotent G D.unipotentInclusion n ∈
      (standardUnipotent i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
  have hn : map F D.unipotent G D.unipotentInclusion n ∈
      (SubgroupFunctor.range D.unipotentInclusion).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := ⟨n, rfl⟩
  rwa [D.unipotent_represents.2] at hn

/-- The Levi factor really maps into the shared standard Levi functor. -/
theorem levi_mem_standard (m : AdelicGroupPoints F D.levi) :
    map F D.levi G D.leviInclusion m ∈
      (standardLevi i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
  have hm : map F D.levi G D.leviInclusion m ∈
      (SubgroupFunctor.range D.leviInclusion).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := ⟨m, rfl⟩
  rwa [D.levi_represents.2] at hm

/-- The compact prefix ΩN ΩM, mapped through the actual inclusions. -/
def compactPrefix : Set (AdelicGroupPoints F G) :=
  (map F D.unipotent G D.unipotentInclusion '' C.omegaN) *
    ((fun m : normOneSubgroup F D.levi =>
      map F D.levi G D.leviInclusion m) '' C.omegaM)

variable (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The actual continuous map of the intrinsic positive torus into the ambient group. -/
def positiveMap : PositiveRealTorus.intrinsicSubgroup F T₀ →ₜ* AdelicGroupPoints F G where
  toMonoidHom :=
    (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i)).toMonoidHom.comp
      (PositiveRealTorus.intrinsicSubgroup F T₀).subtype
  continuous_toFun :=
    (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i)).continuous.comp continuous_subtype_val

/-- The actual ordered factor product ΩN ΩM A K for any subset A of the positive torus. -/
def productSet (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)) :
    Set (AdelicGroupPoints F G) :=
  compactPrefix F G T i ν D C * (positiveMap F G T i T₀ j '' A) * C.compactSubgroup

/-- The product with the shared normalized weak simple-root chamber. -/
def weakSiegelProduct (t : ℝ≥0ˣ) : Set (AdelicGroupPoints F G) :=
  productSet F G T i ν D C T₀ j
    (PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)

/-- The product with explicitly indexed normalized strict simple-root inequalities. -/
def strictSiegelProduct (b : characterLattice T → ℝ≥0ˣ) : Set (AdelicGroupPoints F G) :=
  productSet F G T i ν D C T₀ j
    (PositiveRealTorus.strictSimpleRootChamber F T₀ T j b G i ν)

theorem mem_productSet_iff (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀))
    (g : AdelicGroupPoints F G) :
    g ∈ productSet F G T i ν D C T₀ j A ↔
      ∃ n ∈ C.omegaN, ∃ m ∈ C.omegaM, ∃ a ∈ A,
        ∃ k ∈ C.compactSubgroup,
          map F D.unipotent G D.unipotentInclusion n *
            map F D.levi G D.leviInclusion m * positiveMap F G T i T₀ j a * k = g := by
  simp only [productSet, compactPrefix, Set.mem_mul, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩,
      _, ⟨a, ha, rfl⟩, rfl⟩, k, hk, h⟩
    exact ⟨n, hn, m, hm, a, ha, k, hk, h⟩
  · rintro ⟨n, hn, m, hm, a, ha, k, hk, h⟩
    exact ⟨_, ⟨_, ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩,
      _, ⟨a, ha, rfl⟩, rfl⟩, k, hk, h⟩

theorem productSet_mono {A B : Set (PositiveRealTorus.intrinsicSubgroup F T₀)}
    (h : A ⊆ B) :
    productSet F G T i ν D C T₀ j A ⊆ productSet F G T i ν D C T₀ j B :=
  Set.mul_subset_mul_right (Set.mul_subset_mul_left (Set.image_mono h))

theorem strictSiegelProduct_subset_weak (t : ℝ≥0ˣ) :
    strictSiegelProduct F G T i ν D C T₀ j (fun _ => t) ⊆
      weakSiegelProduct F G T i ν D C T₀ j t :=
  productSet_mono F G T i ν D C T₀ j
    (PositiveRealTorus.strictCharacterChamber_subset_weak F T₀ T j
      (simpleRelativeRoots i ν) (fun _ => t))

/-- Containment in the actual norm-one group follows from explicit algebraic
character-triviality on the unipotent and torus inclusions. -/
theorem productSet_subset_normOne
    (hN : CharactersTrivialAlong F D.unipotent G D.unipotentInclusion)
    (hT : CharactersTrivialAlong F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i))
    (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)) :
    productSet F G T i ν D C T₀ j A ⊆ normOneSubgroup F G := by
  have hn : map F D.unipotent G D.unipotentInclusion '' C.omegaN ⊆ normOneSubgroup F G := by
    rintro _ ⟨n, _, rfl⟩
    exact range_le_normOne_of_charactersTrivialAlong F D.unipotent G D.unipotentInclusion hN
      ⟨n, rfl⟩
  have hm : (fun m : normOneSubgroup F D.levi =>
      map F D.levi G D.leviInclusion m) '' C.omegaM ⊆ normOneSubgroup F G := by
    rintro _ ⟨m, _, rfl⟩
    exact map_normOneSubgroup_le F D.levi G D.leviInclusion ⟨m, m.property, rfl⟩
  have ha : positiveMap F G T i T₀ j '' A ⊆ normOneSubgroup F G := by
    rintro _ ⟨a, _, rfl⟩
    exact range_le_normOne_of_charactersTrivialAlong F T₀.toGrp G
      (CommGroupScheme.groupHom j ≫ i) hT ⟨a, rfl⟩
  exact Subgroup.mul_subset (Subgroup.mul_subset (Subgroup.mul_subset hn hm) ha)
    (compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup)

variable [IsAffine G.X.left]

/-- The prefix really is compact in the actual adelic topology. -/
theorem isCompact_compactPrefix : IsCompact (compactPrefix F G T i ν D C) :=
  (C.compact_omegaN.image (map F D.unipotent G D.unipotentInclusion).continuous).mul
    (C.compact_omegaM.image
      ((map F D.levi G D.leviInclusion).continuous.comp continuous_subtype_val))

/-- Restricting the torus factor to a compact subset gives a compact product. -/
theorem isCompact_productSet {A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)}
    (hA : IsCompact A) : IsCompact (productSet F G T i ν D C T₀ j A) :=
  ((isCompact_compactPrefix F G T i ν D C).mul
    (hA.image (positiveMap F G T i T₀ j).continuous)).mul C.compact_compactSubgroup

end AdelicSiegelFactors

end Langlands.Global
