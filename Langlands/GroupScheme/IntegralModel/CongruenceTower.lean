import Langlands.GroupScheme.IntegralModel.LocalField
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Actual positive-level congruence towers of integral group models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section PointRestriction

variable {B S T U : Scheme.{u}} (b : S ⟶ B) (c : T ⟶ B)
  (t : T ⟶ S) (ht : t ≫ b = c) (G : GroupScheme B)

/-- Restriction along an actual map of test schemes over the original base,
with source and target the actual sections of the two group-scheme pullbacks. -/
def baseChangePointRestriction :
    (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X) →*
      (Over.mk (𝟙 T) ⟶ ((baseChange c).obj G).X) :=
  (baseChangeBasePointsEquiv c G).symm.toMonoidHom.comp
    ((G.points.map (Over.homMk t ht : Over.mk c ⟶ Over.mk b).op).hom.comp
      (baseChangeBasePointsEquiv b G).toMonoidHom)

theorem baseChangePointRestriction_project
    (x : (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X)) :
    baseChangeBasePointsEquiv c G (baseChangePointRestriction b c t ht G x) =
      (Over.homMk t ht : Over.mk c ⟶ Over.mk b) ≫
        baseChangeBasePointsEquiv b G x :=
  (baseChangeBasePointsEquiv c G).apply_symm_apply _

/-- The transition restricts the original point along `t`. -/
theorem baseChangePointRestriction_fst
    (x : (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X)) :
    (baseChangePointRestriction b c t ht G x).left ≫ pullback.fst G.X.hom c =
      t ≫ (x.left ≫ pullback.fst G.X.hom b) := by
  rw [← baseChangeBasePointsEquiv_left, baseChangePointRestriction_project]
  change t ≫ (baseChangeBasePointsEquiv b G x).left = _
  rw [baseChangeBasePointsEquiv_left]

/-- Restricting a changed section is the section changed directly to the target base. -/
theorem baseChangePointRestriction_section (x : Over.mk (𝟙 B) ⟶ G.X) :
    baseChangePointRestriction b c t ht G (baseChangeSectionHom b G x) =
      baseChangeSectionHom c G x := by
  apply (baseChangeBasePointsEquiv c G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left,
    baseChangePointRestriction_fst, baseChangeSectionHom_fst,
    baseChangeSectionHom_fst, ← Category.assoc, ht]

/-- Identity restriction is the identity on actual pullback sections. -/
theorem baseChangePointRestriction_id
    (x : (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X)) :
    baseChangePointRestriction b b (𝟙 S) (by simp) G x = x := by
  apply (baseChangeBasePointsEquiv b G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left,
    baseChangePointRestriction_fst, Category.id_comp]

/-- Actual point restrictions compose in the order of the test-scheme maps. -/
theorem baseChangePointRestriction_comp (d : U ⟶ B) (s : U ⟶ T)
    (hs : s ≫ c = d) (x : (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X)) :
    baseChangePointRestriction c d s hs G (baseChangePointRestriction b c t ht G x) =
      baseChangePointRestriction b d (s ≫ t)
        (by rw [Category.assoc, ht, hs]) G x := by
  apply (baseChangeBasePointsEquiv d G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left,
    baseChangePointRestriction_fst, baseChangePointRestriction_fst,
    baseChangePointRestriction_fst, Category.assoc]

variable {G} {H : GroupScheme B}

/-- Restriction is natural in the original group scheme. -/
theorem baseChangePointRestriction_naturality (f : G ⟶ H)
    (x : (Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X)) :
    baseChangePointRestriction b c t ht H
        (x ≫ ((baseChange b).map f).hom.hom) =
      (baseChangePointRestriction b c t ht G x) ≫ ((baseChange c).map f).hom.hom := by
  apply (baseChangeBasePointsEquiv c H).injective
  change baseChangeBasePointsEquiv c H
      (baseChangePointRestriction b c t ht H (x ≫ ((baseChange b).map f).hom.hom)) =
    baseChangeBasePointsEquiv c H
      (baseChangePointRestriction b c t ht G x ≫ ((baseChange c).map f).hom.hom)
  rw [baseChangePointRestriction_project, baseChangeBasePointsEquiv_comp,
    baseChangeBasePointsEquiv_comp, baseChangePointRestriction_project, Category.assoc]

end PointRestriction

namespace IntegralModel

section Coefficients

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Positive congruence levels use the actual quotient by a power of the maximal ideal. -/
abbrev congruenceRing (n : ℕ+) := R ⧸ (IsLocalRing.maximalIdeal R) ^ (n : ℕ)

/-- The actual quotient coefficient homomorphism at a positive level. -/
def congruenceQuotient (n : ℕ+) : R →+* congruenceRing R n :=
  Ideal.Quotient.mk _

/-- The spectrum map of the actual maximal-ideal-power quotient. -/
def congruenceBaseMap (n : ℕ+) :
    Spec (CommRingCat.of (congruenceRing R n)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (congruenceQuotient R n))

/-- The canonical quotient from a deeper positive level to a shallower one. -/
def congruenceRingTransition {n k : ℕ+} (h : n ≤ k) :
    congruenceRing R k →+* congruenceRing R n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (show (n : ℕ) ≤ (k : ℕ) from h))

@[simp] theorem congruenceRingTransition_quotient {n k : ℕ+} (h : n ≤ k) (r : R) :
    congruenceRingTransition R h (congruenceQuotient R k r) =
      congruenceQuotient R n r := rfl

@[simp] theorem congruenceRingTransition_refl (n : ℕ+) :
    congruenceRingTransition R (le_refl n) = RingHom.id _ :=
  Ideal.Quotient.factor_eq

@[simp] theorem congruenceRingTransition_comp {n k l : ℕ+} (h : n ≤ k) (j : k ≤ l) :
    (congruenceRingTransition R h).comp (congruenceRingTransition R j) =
      congruenceRingTransition R (h.trans j) :=
  Ideal.Quotient.factor_comp _ _

/-- The actual map of spectra inducing a transition between congruence levels. -/
def congruenceTransitionBaseMap {n k : ℕ+} (h : n ≤ k) :
    Spec (CommRingCat.of (congruenceRing R n)) ⟶
      Spec (CommRingCat.of (congruenceRing R k)) :=
  Spec.map (CommRingCat.ofHom (congruenceRingTransition R h))

theorem congruenceTransitionBaseMap_comm {n k : ℕ+} (h : n ≤ k) :
    congruenceTransitionBaseMap R h ≫ congruenceBaseMap R k = congruenceBaseMap R n := by
  rw [congruenceTransitionBaseMap, congruenceBaseMap, ← Spec.map_comp]
  rfl

@[simp] theorem congruenceTransitionBaseMap_refl (n : ℕ+) :
    congruenceTransitionBaseMap R (le_refl n) = 𝟙 _ := by
  simp [congruenceTransitionBaseMap]

theorem congruenceTransitionBaseMap_comp {n k l : ℕ+} (h : n ≤ k) (j : k ≤ l) :
    congruenceTransitionBaseMap R h ≫ congruenceTransitionBaseMap R j =
      congruenceTransitionBaseMap R (h.trans j) := by
  rw [congruenceTransitionBaseMap, congruenceTransitionBaseMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congruenceRingTransition_comp R h j)

/-- The canonical level-one coefficient equivalence with the actual residue quotient. -/
def congruenceResidueRingEquiv :
    congruenceRing R 1 ≃+* IsLocalRing.ResidueField R :=
  Ideal.quotEquivOfEq (pow_one (IsLocalRing.maximalIdeal R))

@[simp] theorem congruenceResidueRingEquiv_quotient (r : R) :
    congruenceResidueRingEquiv R (congruenceQuotient R 1 r) =
      IsLocalRing.residue R r := rfl

/-- The spectrum isomorphism of the canonical level-one residue-quotient equivalence. -/
def congruenceResidueBaseIso :
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ≅
      Spec (CommRingCat.of (congruenceRing R 1)) :=
  Scheme.Spec.mapIso (congruenceResidueRingEquiv R).toCommRingCatIso.op

theorem congruenceResidueBaseIso_comm :
    (congruenceResidueBaseIso R).hom ≫ congruenceBaseMap R 1 = residueBaseMap R := by
  change Spec.map (CommRingCat.ofHom (congruenceResidueRingEquiv R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (congruenceQuotient R 1)) = residueBaseMap R
  rw [← Spec.map_comp]
  rfl

/-- The canonical residue comparison as an isomorphism of tests over the original ring. -/
def congruenceResidueTestIso :
    Over.mk (residueBaseMap R) ≅ Over.mk (congruenceBaseMap R 1) :=
  Over.isoMk (congruenceResidueBaseIso R) (congruenceResidueBaseIso_comm R)

end Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- The actual group-scheme base change to the positive congruence quotient. -/
abbrev congruenceFibre (n : ℕ+) :
    GroupScheme (Spec (CommRingCat.of (congruenceRing R n))) :=
  (baseChange (congruenceBaseMap R n)).obj M.group

/-- Reduction of the original integral sections modulo the actual maximal ideal power. -/
def reductionAt (n : ℕ+) : M.integralSections →* rationalPoints (M.congruenceFibre n) :=
  baseChangeSectionHom (congruenceBaseMap R n) M.group

theorem reductionAt_left (n : ℕ+) (x : M.integralSections) :
    (M.reductionAt n x).left =
      pullback.lift (congruenceBaseMap R n ≫ x.left) (𝟙 _)
        (by simp [Category.assoc, x.w]) :=
  baseChangeSectionHom_left (congruenceBaseMap R n) M.group x

/-- The actual restriction of quotient-valued points from level `k` to level `n ≤ k`. -/
def congruenceTransition {n k : ℕ+} (h : n ≤ k) :
    rationalPoints (M.congruenceFibre k) →* rationalPoints (M.congruenceFibre n) :=
  baseChangePointRestriction (congruenceBaseMap R k) (congruenceBaseMap R n)
    (congruenceTransitionBaseMap R h) (congruenceTransitionBaseMap_comm R h) M.group

theorem congruenceTransition_fst {n k : ℕ+} (h : n ≤ k)
    (x : rationalPoints (M.congruenceFibre k)) :
    (M.congruenceTransition h x).left ≫ pullback.fst M.group.X.hom (congruenceBaseMap R n) =
      congruenceTransitionBaseMap R h ≫
        (x.left ≫ pullback.fst M.group.X.hom (congruenceBaseMap R k)) :=
  baseChangePointRestriction_fst _ _ _ _ _ _

/-- The original reductions factor through every shallower quotient. -/
@[simp] theorem congruenceTransition_reductionAt {n k : ℕ+} (h : n ≤ k)
    (x : M.integralSections) :
    M.congruenceTransition h (M.reductionAt k x) = M.reductionAt n x :=
  baseChangePointRestriction_section _ _ _ _ _ _

@[simp] theorem congruenceTransition_refl (n : ℕ+)
    (x : rationalPoints (M.congruenceFibre n)) :
    M.congruenceTransition (le_refl n) x = x := by
  unfold congruenceTransition
  simp only [congruenceTransitionBaseMap_refl]
  exact baseChangePointRestriction_id _ _ _

theorem congruenceTransition_comp {n k l : ℕ+} (h : n ≤ k) (j : k ≤ l)
    (x : rationalPoints (M.congruenceFibre l)) :
    M.congruenceTransition h (M.congruenceTransition j x) =
      M.congruenceTransition (h.trans j) x := by
  unfold congruenceTransition
  simp only [baseChangePointRestriction_comp, congruenceTransitionBaseMap_comp]

/-- The positive-level congruence kernel in the original integral section group. -/
def congruenceKernelAt (n : ℕ+) : Subgroup M.integralSections := (M.reductionAt n).ker

@[simp] theorem mem_congruenceKernelAt (n : ℕ+) (x : M.integralSections) :
    x ∈ M.congruenceKernelAt n ↔ M.reductionAt n x = 1 := Iff.rfl

instance congruenceKernelAt_normal (n : ℕ+) : (M.congruenceKernelAt n).Normal := by
  change (M.reductionAt n).ker.Normal
  infer_instance

/-- The same positive-level kernel represented in the supplied generic rational points. -/
def congruenceSubgroupAt (n : ℕ+) : Subgroup (rationalPoints G) :=
  (M.congruenceKernelAt n).map M.integralPointMap

@[simp] theorem mem_congruenceSubgroupAt (n : ℕ+) (g : rationalPoints G) :
    g ∈ M.congruenceSubgroupAt n ↔
      ∃ x : M.integralSections, M.reductionAt n x = 1 ∧ M.integralPointMap x = g := Iff.rfl

theorem congruenceSubgroupAt_le_integralPoints (n : ℕ+) :
    M.congruenceSubgroupAt n ≤ M.integralPoints := by
  rintro g ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- The positive congruence image with the integral-point image as ambient group. -/
def congruenceInIntegralPointsAt (n : ℕ+) : Subgroup M.integralPoints :=
  (M.congruenceKernelAt n).map M.integralPointMap.rangeRestrict

instance congruenceInIntegralPointsAt_normal (n : ℕ+) :
    (M.congruenceInIntegralPointsAt n).Normal :=
  Subgroup.Normal.map (inferInstance : (M.congruenceKernelAt n).Normal)
    M.integralPointMap.rangeRestrict M.integralPointMap.rangeRestrict_surjective

theorem congruenceInIntegralPointsAt_eq_subgroupOf (n : ℕ+) :
    M.congruenceInIntegralPointsAt n =
      (M.congruenceSubgroupAt n).subgroupOf M.integralPoints := by
  ext g
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, congrArg Subtype.val h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h⟩

instance congruenceSubgroupAt_normal_in_integralPoints (n : ℕ+) :
    ((M.congruenceSubgroupAt n).subgroupOf M.integralPoints).Normal := by
  rw [← M.congruenceInIntegralPointsAt_eq_subgroupOf]
  infer_instance

/-- Deeper reductions impose stronger congruence conditions on integral sections. -/
theorem congruenceKernelAt_antitone : Antitone M.congruenceKernelAt := by
  intro n k h x hx
  rw [mem_congruenceKernelAt] at hx ⊢
  rw [← M.congruenceTransition_reductionAt h, hx, map_one]

/-- The actual generic congruence subgroups form an antitone positive tower. -/
theorem congruenceSubgroupAt_antitone : Antitone M.congruenceSubgroupAt := by
  intro n k h g hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨x, M.congruenceKernelAt_antitone h hx, rfl⟩

/-- The actual level-one quotient points, identified with the existing special-fibre points
through the canonical residue-quotient equivalence. -/
def congruenceResiduePointsEquiv :
    rationalPoints (M.congruenceFibre 1) ≃* rationalPoints M.specialFibre :=
  (baseChangeBasePointsEquiv (congruenceBaseMap R 1) M.group).trans
    ((M.group.points.mapIso (congruenceResidueTestIso R).op).groupIsoToMulEquiv.trans
      (baseChangeBasePointsEquiv (residueBaseMap R) M.group).symm)

/-- The level-one point equivalence is restriction along the spectrum of the canonical
coefficient quotient equivalence. -/
theorem congruenceResiduePointsEquiv_apply
    (x : rationalPoints (M.congruenceFibre 1)) :
    M.congruenceResiduePointsEquiv x =
      baseChangePointRestriction (congruenceBaseMap R 1) (residueBaseMap R)
        (congruenceResidueBaseIso R).hom (congruenceResidueBaseIso_comm R) M.group x := rfl

@[simp] theorem congruenceResiduePointsEquiv_reductionAt (x : M.integralSections) :
    M.congruenceResiduePointsEquiv (M.reductionAt 1 x) = M.reduction x := by
  rw [congruenceResiduePointsEquiv_apply]
  exact baseChangePointRestriction_section _ _ _ _ _ _

@[simp] theorem congruenceKernelAt_one : M.congruenceKernelAt 1 = M.congruenceKernel := by
  ext x
  change M.reductionAt 1 x = 1 ↔ M.reduction x = 1
  constructor
  · intro hx
    rw [← M.congruenceResiduePointsEquiv_reductionAt, hx, map_one]
  · intro hx
    apply M.congruenceResiduePointsEquiv.injective
    rw [M.congruenceResiduePointsEquiv_reductionAt, hx, map_one]

@[simp] theorem congruenceSubgroupAt_one :
    M.congruenceSubgroupAt 1 = M.congruenceSubgroup := by
  unfold congruenceSubgroupAt congruenceSubgroup
  rw [M.congruenceKernelAt_one]

@[simp] theorem congruenceInIntegralPointsAt_one :
    M.congruenceInIntegralPointsAt 1 = M.congruenceInIntegralPoints := by
  unfold congruenceInIntegralPointsAt congruenceInIntegralPoints
  rw [M.congruenceKernelAt_one]

variable {M} {N : IntegralModel R K H} {f : G ⟶ H}

/-- The actual quotient-fibre homomorphism of a compatible model homomorphism. -/
def Hom.congruenceFibreMap (φ : M.Hom N f) (n : ℕ+) :
    M.congruenceFibre n ⟶ N.congruenceFibre n :=
  (baseChange (congruenceBaseMap R n)).map φ.hom

/-- Reduction commutes with model homomorphisms at every positive level. -/
theorem Hom.reductionAt_naturality (φ : M.Hom N f) (n : ℕ+) (x : M.integralSections) :
    N.reductionAt n (rationalPoints.map φ.hom x) =
      rationalPoints.map (φ.congruenceFibreMap n) (M.reductionAt n x) :=
  baseChangeSectionHom_naturality (congruenceBaseMap R n) φ.hom x

theorem Hom.congruenceTransition_naturality (φ : M.Hom N f) {n k : ℕ+} (h : n ≤ k)
    (x : rationalPoints (M.congruenceFibre k)) :
    N.congruenceTransition h (rationalPoints.map (φ.congruenceFibreMap k) x) =
      rationalPoints.map (φ.congruenceFibreMap n) (M.congruenceTransition h x) :=
  baseChangePointRestriction_naturality _ _ _ _ φ.hom x

theorem Hom.map_mem_congruenceKernelAt (φ : M.Hom N f) (n : ℕ+)
    {x : M.integralSections} (hx : x ∈ M.congruenceKernelAt n) :
    rationalPoints.map φ.hom x ∈ N.congruenceKernelAt n := by
  rw [mem_congruenceKernelAt] at hx ⊢
  rw [φ.reductionAt_naturality, hx, map_one]

/-- The generic compatible homomorphism carries the actual congruence image into its counterpart. -/
theorem Hom.map_mem_congruenceSubgroupAt (φ : M.Hom N f) (n : ℕ+)
    {g : rationalPoints G} (hg : g ∈ M.congruenceSubgroupAt n) :
    rationalPoints.map f g ∈ N.congruenceSubgroupAt n := by
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨rationalPoints.map φ.hom x, φ.map_mem_congruenceKernelAt n hx,
    φ.integralPointMap_naturality x⟩

end IntegralModel
end Langlands.GroupScheme
