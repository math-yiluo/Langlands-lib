import Langlands.Global.InfinitePlaceLeviIwasawaStatement
import Langlands.Global.InfinitePlaceIwasawaBaseChange
import Langlands.GroupScheme.AffinePointClosedImmersion

/-! # Actual completion transport for Levi-compatible Iwasawa decompositions -/

noncomputable section

universe u v w z uM vM

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.CompactIwasawa

variable {G : Type w} {G' : Type z} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G']

/-- Compactness and maximality among every compact overgroup. -/
def IsMaximalCompact (K : Subgroup G) : Prop :=
  IsCompact (K : Set G) ∧
    ∀ L : Subgroup G, IsCompact (L : Set G) → K ≤ L → L = K

/-- A multiplicative homeomorphism preserves maximal compact subgroups. -/
theorem IsMaximalCompact.map {K : Subgroup G}
    (hK : IsMaximalCompact K) (e : G ≃ₜ* G') :
    IsMaximalCompact (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.1.image e.continuous
  · intro L hL hle
    have hpre : IsCompact (L.comap e.toMonoidHom : Set G) :=
      e.toHomeomorph.isCompact_preimage.mpr hL
    have heq := hK.2 (L.comap e.toMonoidHom) hpre
      (Subgroup.map_le_iff_le_comap.mp hle)
    have hmap := congrArg (Subgroup.map e.toMonoidHom) heq
    simpa only [Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective] using hmap

variable {P : Type u} {P' : Type v} {M : Type uM} {M' : Type vM}
  [Group P] [Group P'] [Group M] [Group M']
  [TopologicalSpace M] [TopologicalSpace M']

/-- All four compact, covering and Levi-intersection conclusions for actual
homomorphisms into an ambient group. -/
def IsLeviCompatibleDecomposition (p : P →* G) (m : M →* G)
    (K : Subgroup G) : Prop :=
  IsMaximalCompact K ∧
    Set.range p * (K : Set G) = Set.univ ∧
    Set.range p ∩ (K : Set G) = Set.range m ∩ (K : Set G) ∧
    IsMaximalCompact (K.comap m)

/-- Existence of a compact satisfying all four Levi-compatible conclusions. -/
def HasLeviCompatibleDecomposition (p : P →* G) (m : M →* G) : Prop :=
  ∃ K : Subgroup G, IsLeviCompatibleDecomposition p m K

omit [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M]
    [TopologicalSpace M'] in
/-- The actual inverse-image subgroup commutes with compatible point comparisons. -/
theorem comap_map_eq_of_comm (m : M →* G) (m' : M' →* G')
    (eM : M ≃* M') (eG : G ≃* G')
    (comm : ∀ x, m' (eM x) = eG (m x)) (K : Subgroup G) :
    (K.map eG.toMonoidHom).comap m' = (K.comap m).map eM.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv]
  have heq : eG.symm (m' x) = m (eM.symm x) := by
    apply eG.injective
    rw [eG.apply_symm_apply, ← comm, eM.apply_symm_apply]
  rw [heq]

/-- Commuting comparisons preserve each conclusion, including maximal compactness
on the Levi carrier equipped with its own topology. -/
theorem IsLeviCompatibleDecomposition.transport
    {p : P →* G} {p' : P' →* G'} {m : M →* G} {m' : M' →* G'}
    {K : Subgroup G} (h : IsLeviCompatibleDecomposition p m K)
    (eP : P ≃* P') (eM : M ≃ₜ* M') (eG : G ≃ₜ* G')
    (commP : ∀ x, p' (eP x) = eG (p x))
    (commM : ∀ x, m' (eM x) = eG (m x)) :
    IsLeviCompatibleDecomposition p' m' (K.map eG.toMonoidHom) := by
  refine ⟨h.1.map eG, ?_, ?_, ?_⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy : eG.symm y ∈ Set.range p * (K : Set G) := by
      rw [h.2.1]
      trivial
    obtain ⟨a, ⟨x, rfl⟩, b, hb, hab⟩ := Set.mem_mul.mp hy
    refine Set.mem_mul.mpr
      ⟨p' (eP x), ⟨eP x, rfl⟩, eG b, ⟨b, hb, rfl⟩, ?_⟩
    rw [commP, ← map_mul, hab, eG.apply_symm_apply]
  · have hrangeP : Set.range p' = eG '' Set.range p := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨p (eP.symm x), ⟨eP.symm x, rfl⟩,
          (commP (eP.symm x)).symm.trans (congrArg p' (eP.apply_symm_apply x))⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨eP x, commP x⟩
    have hrangeM : Set.range m' = eG '' Set.range m := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨m (eM.symm x), ⟨eM.symm x, rfl⟩,
          (commM (eM.symm x)).symm.trans (congrArg m' (eM.apply_symm_apply x))⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨eM x, commM x⟩
    rw [hrangeP, hrangeM, Subgroup.coe_map]
    change eG '' Set.range p ∩ eG '' (K : Set G) =
      eG '' Set.range m ∩ eG '' (K : Set G)
    rw [← Set.image_inter eG.injective, ← Set.image_inter eG.injective, h.2.2.1]
  · rw [comap_map_eq_of_comm m m' eM.toMulEquiv eG.toMulEquiv commM]
    exact h.2.2.2.map eM

/-- Existence of all four conclusions is invariant under compatible homeomorphisms. -/
theorem hasLeviCompatibleDecomposition_iff
    (p : P →* G) (p' : P' →* G') (m : M →* G) (m' : M' →* G')
    (eP : P ≃* P') (eM : M ≃ₜ* M') (eG : G ≃ₜ* G')
    (commP : ∀ x, p' (eP x) = eG (p x))
    (commM : ∀ x, m' (eM x) = eG (m x)) :
    HasLeviCompatibleDecomposition p m ↔ HasLeviCompatibleDecomposition p' m' := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨_, hK.transport eP eM eG commP commM⟩
  · rintro ⟨K, hK⟩
    refine ⟨_, hK.transport eP.symm eM.symm eG.symm ?_ ?_⟩
    · intro x
      apply eG.injective
      rw [eG.apply_symm_apply, ← commP, eP.apply_symm_apply]
    · intro x
      apply eG.injective
      rw [eG.apply_symm_apply, ← commM, eM.apply_symm_apply]

end Langlands.CompactIwasawa

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The generic compact predicate agrees with the published actual-point predicate. -/
theorem isMaximalCompactSubgroup_iff (v : NumberField.InfinitePlace F)
    (K : Subgroup (InfinitePlaceGroupPoints F G v)) :
    IsMaximalCompactSubgroup F G v K ↔ CompactIwasawa.IsMaximalCompact K := Iff.rfl

/-- No conclusion is lost in the generic two-homomorphism formulation. -/
theorem isLeviCompatibleIwasawaCompact_iff
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (v : NumberField.InfinitePlace F)
    (K : Subgroup (InfinitePlaceGroupPoints F G v)) :
    IsLeviCompatibleIwasawaCompact F G P p M l v K ↔
      CompactIwasawa.IsLeviCompatibleDecomposition
        (P.affinePointsTarget p (CommAlgCat.of F v.Completion))
        (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F v.Completion)) K := Iff.rfl

local instance leviCompletionPointTopology
    (H : GroupScheme (Spec (CommRingCat.of F))) (v : NumberField.InfinitePlace F) :
    TopologicalSpace ((completionBaseChange F H v).affinePoints
      (CommAlgCat.of v.Completion v.Completion)) :=
  (completionBaseChange F H v).affinePointsTopologicalSpace
    (CommAlgCat.of v.Completion v.Completion)

/-- Actual completion base change preserves all four Levi-compatible conclusions.
Both the ambient group and the Levi use their existing evaluation topologies. -/
theorem hasLeviCompatibleDecomposition_completionBaseChange_iff
    [IsAffine G.X.left]
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left] (l : M ⟶ P)
    (v : NumberField.InfinitePlace F) :
    (∃ K, IsLeviCompatibleIwasawaCompact F G P p M l v K) ↔
      CompactIwasawa.HasLeviCompatibleDecomposition
        ((completionBaseChange F P v).affinePointsTarget
          ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p)
          (CommAlgCat.of v.Completion v.Completion))
        ((completionBaseChange F M v).affinePointsTarget
          (((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map l) ≫
            ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p))
          (CommAlgCat.of v.Completion v.Completion)) := by
  change CompactIwasawa.HasLeviCompatibleDecomposition _ _ ↔ _
  apply CompactIwasawa.hasLeviCompatibleDecomposition_iff _ _ _ _
    (affinePointsBaseChangeMulEquiv F v.Completion v.Completion P)
    (completionBaseChangeHomeomorph F M v) (completionBaseChangeHomeomorph F G v)
  · intro x
    exact (affinePointsBaseChangeMulEquiv_target F v.Completion v.Completion p x).symm
  · intro x
    rw [← Functor.map_comp]
    exact (affinePointsBaseChangeMulEquiv_target F v.Completion v.Completion (l ≫ p) x).symm

/-- The actual point map of the specified Levi into the ambient group is a closed
embedding; reductivity supplies the required affine schemes. -/
theorem isClosedEmbedding_leviPoints
    (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F) :
    Topology.IsClosedEmbedding
      (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F v.Completion)) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsClosedImmersion (l ≫ p).hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (l.hom.hom.left ≫ p.hom.hom.left))
  exact M.isClosedEmbedding_affinePointsTarget G (CommAlgCat.of F v.Completion) (l ≫ p)

/-- Compactness transfers to the exact inverse-image subgroup on the Levi carrier. -/
theorem isCompact_comap_leviPoints
    (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F)
    (K : Subgroup (InfinitePlaceGroupPoints F G v))
    (hK : IsCompact (K : Set (InfinitePlaceGroupPoints F G v))) :
    IsCompact (K.comap (M.affinePointsTarget (l ≫ p)
      (CommAlgCat.of F v.Completion)) : Set (InfinitePlaceGroupPoints F M v)) :=
  (isClosedEmbedding_leviPoints F G hG P p hp M l hl v).isCompact_preimage hK

end Langlands.Global.InfinitePlaceGroupPoints
