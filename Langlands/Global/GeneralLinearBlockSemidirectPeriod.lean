import Langlands.GroupScheme.GeneralLinearBlockLeviProjection
import Langlands.GroupScheme.GeneralLinearPermutationConjugation
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.Global.GeneralLinearBlockUnipotentQuotient
import Langlands.Global.AdelicSubgroupQuotientTransport
import Langlands.Global.LeftCosetSemidirectPeriod

/-! # Period reduction on adelic block unipotent subgroups of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MeasureTheory Opposite Set
  Topology
open scoped CategoryTheory.MonObj RestrictedProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.GeneralLinearBlockSemidirect

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints

section Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Invertible matrices with prescribed entries at prescribed positions form a closed set. -/
theorem isClosed_setOf_entries {A : Type*} [CommRing A] [TopologicalSpace A] [T2Space A]
    (P : n → n → Prop) (c : n → n → A) :
    IsClosed {g : GL n A | ∀ i j, P i j → (g : Matrix n n A) i j = c i j} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

variable {A : Type*} [CommRing A]

theorem isClosed_blockUnipotentSubgroup [TopologicalSpace A] [T2Space A] (e : n → ℤ) :
    IsClosed (blockUnipotentSubgroup A e : Set (GL n A)) :=
  isClosed_setOf_entries (fun i j => e i ≤ e j) (fun i j => (1 : Matrix n n A) i j)

theorem isClosed_blockUnipotentSubgroup_inf_blockLeviSubgroup [TopologicalSpace A] [T2Space A]
    (e w : n → ℤ) :
    IsClosed ((blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w : Subgroup (GL n A)) :
      Set (GL n A)) := by
  rw [Subgroup.coe_inf]
  exact (isClosed_blockUnipotentSubgroup e).inter
    (isClosed_setOf_entries (fun i j => w i ≠ w j) (fun _ _ => 0))

/-- A matrix whose image under an injective coefficient map is block unipotent is itself block
unipotent. -/
theorem mem_blockUnipotentSubgroup_of_map {B : Type*} [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) (w : n → ℤ) {g : GL n A}
    (hg : Matrix.GeneralLinearGroup.map f g ∈ blockUnipotentSubgroup B w) :
    g ∈ blockUnipotentSubgroup A w := by
  intro i j hij
  apply hf
  have h := hg i j hij
  rw [Matrix.GeneralLinearGroup.map_apply] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact (map_one f).symm
  · exact (map_zero f).symm

end Matrix

variable (F : Type u) [Field F] [NumberField F] {n : Type} [Fintype n] [DecidableEq n]

local notation "GLG" => Langlands.GroupScheme.GeneralLinear.groupScheme n (CommRingCat.of F)
local notation "RF" => CommRingCat.of F
local notation "AF" => CommAlgCat.of F (AdeleRing (𝓞 F) F)
local notation "QF" => CommAlgCat.of F F

local instance blockSemidirectIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme n (CommRingCat.of F)

local instance blockSemidirectSmooth : Smooth (GLG).X.hom :=
  smoothStatement n (CommRingCat.of F)

/-- The full adele ring is Hausdorff. -/
theorem adeleRing_t2Space : T2Space (AdeleRing (𝓞 F) F) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/-- A matrix-subgroup functor whose adelic matrix subgroup is closed has closed adelic points. -/
theorem isClosed_adelicPoints_ofMatrixSubgroups {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    (hc : IsClosed (H (CommRingCat.of (AdeleRing (𝓞 F) F)) :
      Set (GL n (AdeleRing (𝓞 F) F)))) :
    IsClosed (adelicPoints F GLG (ofMatrixSubgroups (R := RF) H hH) :
      Set (AdelicGroupPoints F GLG)) := by
  have h := hc.preimage (continuous_affinePointsEquiv n RF AF)
  convert h using 1
  ext x
  exact mem_ofMatrixSubgroups_affinePoints_iff RF AF x

variable (e w : n → ℤ)

theorem isClosed_adelicPoints_blockUnipotent :
    IsClosed (adelicPoints F GLG (blockUnipotent n RF e) : Set (AdelicGroupPoints F GLG)) :=
  let := adeleRing_t2Space F
  isClosed_adelicPoints_ofMatrixSubgroups F (H := fun A => blockUnipotentSubgroup A e)
    (hH := fun f _ hg => map_mem_blockUnipotentSubgroup e f.hom hg)
    (isClosed_blockUnipotentSubgroup e)

theorem isClosed_adelicPoints_leviUnipotent :
    IsClosed (adelicPoints F GLG (leviUnipotent n RF e w) : Set (AdelicGroupPoints F GLG)) :=
  let := adeleRing_t2Space F
  isClosed_adelicPoints_ofMatrixSubgroups F
    (H := fun A => blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w)
    (hH := fun f _ hg => ⟨map_mem_blockUnipotentSubgroup e f.hom hg.1,
      map_mem_blockLeviSubgroup w f.hom hg.2⟩)
    (isClosed_blockUnipotentSubgroup_inf_blockLeviSubgroup e w)

local instance blockSemidirectClosed :
    IsClosed (adelicPoints F GLG (blockUnipotent n RF e) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_blockUnipotent F e

local instance blockSemidirectLeviClosed :
    IsClosed (adelicPoints F GLG (leviUnipotent n RF e w) : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints_leviUnipotent F e w

local instance blockSemidirectLocallyCompact :
    LocallyCompactSpace (adelicPoints F GLG (blockUnipotent n RF e)) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace

local instance blockSemidirectLeviLocallyCompact :
    LocallyCompactSpace (adelicPoints F GLG (leviUnipotent n RF e w)) :=
  (isClosed_adelicPoints_leviUnipotent F e w).locallyCompactSpace

variable {e w} (hw : ∀ i j, e i ≤ e j → w i ≤ w j)

/-- The inclusion of the coarser block unipotent adelic points. -/
def normalInclusion :
    adelicPoints F GLG (blockUnipotent n RF w) →* adelicPoints F GLG (blockUnipotent n RF e) :=
  Subgroup.inclusion (blockUnipotent_le_of_le RF hw _)

variable (e w) in
/-- The inclusion of the block Levi part. -/
def leviInclusion :
    adelicPoints F GLG (leviUnipotent n RF e w) →* adelicPoints F GLG (blockUnipotent n RF e) :=
  Subgroup.inclusion (leviUnipotent_le RF e w _)

/-- The coarser block Levi projection on adelic points. -/
def leviProjection :
    adelicPoints F GLG (blockUnipotent n RF e) →* adelicPoints F GLG (leviUnipotent n RF e w) :=
  pointsLeviProjection RF hw AF

theorem leviProjection_leviInclusion (m : adelicPoints F GLG (leviUnipotent n RF e w)) :
    leviProjection F hw (leviInclusion F e w m) = m :=
  pointsLeviProjection_inclusion RF hw AF m

theorem exists_normalInclusion_eq (x : adelicPoints F GLG (blockUnipotent n RF e))
    (hx : leviProjection F hw x = 1) : ∃ y, normalInclusion F hw y = x :=
  ⟨⟨x.val, (pointsLeviProjection_eq_one_iff RF hw AF x).mp hx⟩, rfl⟩

theorem leviProjection_normalInclusion (y : adelicPoints F GLG (blockUnipotent n RF w)) :
    leviProjection F hw (normalInclusion F hw y) = 1 :=
  (pointsLeviProjection_eq_one_iff RF hw AF _).mpr y.property

theorem isEmbedding_normalInclusion : IsEmbedding (normalInclusion F hw) :=
  IsEmbedding.inclusion (blockUnipotent_le_of_le RF hw _)

theorem continuous_leviInclusion : Continuous (leviInclusion F e w) :=
  (IsEmbedding.inclusion (leviUnipotent_le RF e w _)).continuous

theorem continuous_leviProjection : Continuous (leviProjection F hw) :=
  continuous_pointsLeviProjection RF hw AF

theorem leviInclusion_mem_rationalSubgroup (m : adelicPoints F GLG (leviUnipotent n RF e w))
    (hm : m ∈ rationalSubgroup F GLG (leviUnipotent n RF e w)) :
    leviInclusion F e w m ∈ rationalSubgroup F GLG (blockUnipotent n RF e) := by
  obtain ⟨q, rfl⟩ := hm
  exact ⟨⟨q.val, leviUnipotent_le RF e w _ q.property⟩, rfl⟩

theorem leviProjection_mem_rationalSubgroup (x : adelicPoints F GLG (blockUnipotent n RF e))
    (hx : x ∈ rationalSubgroup F GLG (blockUnipotent n RF e)) :
    leviProjection F hw x ∈ rationalSubgroup F GLG (leviUnipotent n RF e w) := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨pointsLeviProjection RF hw QF q, Subtype.ext
    (pointsLeviProjection_naturality RF hw
      (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) q)⟩

theorem normalInclusion_mem_rationalSubgroup_iff
    (y : adelicPoints F GLG (blockUnipotent n RF w)) :
    normalInclusion F hw y ∈ rationalSubgroup F GLG (blockUnipotent n RF e) ↔
      y ∈ rationalSubgroup F GLG (blockUnipotent n RF w) := by
  constructor
  · rintro ⟨q, hq⟩
    have hval : AdelicGroupPoints.rational F GLG q.val = y.val :=
      congrArg Subtype.val hq
    have hy : affinePointsEquiv n RF AF y.val ∈ blockUnipotentSubgroup (AdeleRing (𝓞 F) F) w :=
      (mem_ofMatrixSubgroups_affinePoints_iff (H := fun A => blockUnipotentSubgroup A w)
        (hH := fun f _ hg => map_mem_blockUnipotentSubgroup w f.hom hg) RF AF y.val).mp
        y.property
    have hq' : q.val ∈ (blockUnipotent n RF w).carrier ((algSpec RF).obj (op QF)) := by
      have : Nontrivial (AF : Type u) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
      have key := affinePointsEquiv_naturality (R := RF) (S := QF) (T := AF)
        (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))) q.val
      rw [show (algSpec RF).map (CommAlgCat.ofHom (Algebra.ofId F (AdeleRing (𝓞 F) F))).op ≫
        q.val = y.val from hval] at key
      rw [key] at hy
      exact (mem_ofMatrixSubgroups_affinePoints_iff (H := fun A => blockUnipotentSubgroup A w)
        (hH := fun f _ hg => map_mem_blockUnipotentSubgroup w f.hom hg) RF QF q.val).mpr
        (mem_blockUnipotentSubgroup_of_map (RingHom.injective _) w hy)
    exact ⟨⟨q.val, hq'⟩, Subtype.ext hval⟩
  · rintro ⟨q, rfl⟩
    exact ⟨⟨q.val, blockUnipotent_le_of_le RF hw _ q.property⟩, rfl⟩

include hw in
/-- The block Levi part of a compact block unipotent quotient has compact quotient. -/
theorem leviRationalQuotientCompactSpace
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF e))] :
    CompactSpace (RationalQuotient F GLG (leviUnipotent n RF e w)) := by
  let Γ := rationalSubgroup F GLG (blockUnipotent n RF e)
  let ΓM := rationalSubgroup F GLG (leviUnipotent n RF e w)
  let f : LeftCosetSpace Γ → LeftCosetSpace ΓM :=
    LeftCosetSpace.lift Γ (fun x => LeftCosetSpace.mk ΓM (leviProjection F hw x))
      fun r x => by
        rw [map_mul]
        exact LeftCosetSpace.mk_subgroup_mul ΓM
          ⟨_, leviProjection_mem_rationalSubgroup F hw r.val r.property⟩ _
  have hf : Continuous f := LeftCosetSpace.continuous_lift Γ _ _
    ((LeftCosetSpace.continuous_mk ΓM).comp (continuous_leviProjection F hw))
  refine Function.Surjective.compactSpace hf fun q => ?_
  obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective ΓM q
  exact ⟨LeftCosetSpace.mk Γ (leviInclusion F e w m),
    congrArg (LeftCosetSpace.mk ΓM) (leviProjection_leviInclusion F hw m)⟩

/-- Vanishing of every period along the coarser block unipotent quotient, on all translates by
the block Levi part, forces vanishing of the full block unipotent period. -/
theorem integral_fundamentalDomain_eq_zero
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF e))]
    [CompactSpace (RationalQuotient F GLG (blockUnipotent n RF w))]
    (φ : adelicPoints F GLG (blockUnipotent n RF e) → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ r ∈ rationalSubgroup F GLG (blockUnipotent n RF e), ∀ x, φ (r * x) = φ x)
    (hN : ∀ m : adelicPoints F GLG (leviUnipotent n RF e w),
      ∫ y in LeftCosetSpace.fundamentalDomain (rationalSubgroup F GLG (blockUnipotent n RF w))
          (isDiscrete_rationalSubgroup F GLG _),
        φ (normalInclusion F hw y * leviInclusion F e w m) ∂Measure.haar = 0) :
    ∫ x in LeftCosetSpace.fundamentalDomain (rationalSubgroup F GLG (blockUnipotent n RF e))
        (isDiscrete_rationalSubgroup F GLG _), φ x ∂Measure.haar = 0 := by
  have := leviRationalQuotientCompactSpace F hw
  exact LeftCosetSpace.Semidirect.integral_fundamentalDomain_eq_zero_of_compact
    (normalInclusion F hw) (leviInclusion F e w) (leviProjection F hw)
    (leviProjection_leviInclusion F hw) (exists_normalInclusion_eq F hw)
    (leviProjection_normalInclusion F hw) (isEmbedding_normalInclusion F hw)
    (continuous_leviInclusion F) (continuous_leviProjection F hw)
    (rationalSubgroup F GLG (blockUnipotent n RF e)) (isDiscrete_rationalSubgroup F GLG _)
    (rationalSubgroup F GLG (leviUnipotent n RF e w)) (isDiscrete_rationalSubgroup F GLG _)
    (leviInclusion_mem_rationalSubgroup F) (leviProjection_mem_rationalSubgroup F hw)
    (rationalSubgroup F GLG (blockUnipotent n RF w)) (isDiscrete_rationalSubgroup F GLG _)
    (normalInclusion_mem_rationalSubgroup_iff F hw) φ hφ hφΓ hN

end Langlands.Global.GeneralLinearBlockSemidirect

namespace Langlands.Global.GeneralLinearBlockSemidirect

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]

/-- A threshold block unipotent subgroup of `GL_m` has compact rational quotient, by permutation
conjugation to the standard two-block unipotent subgroup. -/
theorem thresholdRationalQuotientCompactSpace [CompactSpace (AdeleQuotient F)] {m : ℕ}
    (e : Fin m → ℤ) (c : ℤ) :
    CompactSpace (RationalQuotient F
      (Langlands.GroupScheme.GeneralLinear.groupScheme (Fin m) (CommRingCat.of F))
      (blockUnipotent (Fin m) (CommRingCat.of F) (thresholdWeight e c))) := by
  obtain ⟨a, b, h, τ, -, -, hτ⟩ := exists_perm_thresholdWeight_eq_twoBlockWeight e c
  rw [blockUnipotent_eq_comap_innerIso_permPoint (R := CommRingCat.of F) hτ]
  exact rationalQuotientCompactSpace_comap F _ (GeneralLinearBlockUnipotent.subgroup F h)

end Langlands.Global.GeneralLinearBlockSemidirect
