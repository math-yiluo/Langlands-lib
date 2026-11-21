import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.AdelicBlockScalarSections
import Langlands.Global.AdelicGLStandardCompactMaximal
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Automorphic.GeneralLinearAdelicForms
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.UnitaryCharacterPairing
import Langlands.GroupScheme.GeneralLinearBlockLeviProjection

/-! # The standard block-induced scalar model on group-scheme points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1150000

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints PrimitiveAdelicHeight
open Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "GLG" => groupScheme (Fin n) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "U" => blockUnipotentScheme (Fin n) 𝕜 wt
local notation "M" => blockLeviScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt
local notation "uG" => blockUnipotentHom (Fin n) 𝕜 wt
local notation "mG" => blockLeviHom (Fin n) 𝕜 wt

local instance blockEisensteinGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme (Fin n) 𝕜

/-- The scheme inclusion of the block-unipotent radical into the parabolic. -/
def blockUnipotentInclusion : U ⟶ P :=
  (isRepresentedBy_blockParabolic (Fin n) 𝕜 wt).factorHom uG <| by
    rw [(isRepresentedBy_blockUnipotent (Fin n) 𝕜 wt).2]
    intro T x hx
    exact (mem_blockParabolic wt).mpr fun i j hij => by
      have h := (mem_blockUnipotent wt).mp hx i j hij.le
      rw [h, Matrix.one_apply_ne (ne_of_apply_ne _ hij.ne)]

/-- The scheme inclusion of the block-diagonal Levi into the parabolic. -/
def blockLeviInclusion : M ⟶ P :=
  (isRepresentedBy_blockParabolic (Fin n) 𝕜 wt).factorHom mG <| by
    rw [(isRepresentedBy_blockLevi (Fin n) 𝕜 wt).2]
    intro T x hx
    exact (mem_blockParabolic wt).mpr fun i j hij => (mem_blockLevi wt).mp hx i j hij.ne

omit [NumberField F] in
@[simp]
theorem blockUnipotentInclusion_comp : blockUnipotentInclusion F B ≫ p = uG :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

omit [NumberField F] in
@[simp]
theorem blockLeviInclusion_comp : blockLeviInclusion F B ≫ p = mG :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

variable (n) in
/-- The standard matrix compact subgroup on the actual scheme point carrier. -/
abbrev standardCompactPoints : Subgroup (AdelicGroupPoints F GLG) :=
  RankinSelbergGlobal.gaugeStandardCompact F n

variable (n) in
/-- The integral finite-adelic matrices on the scheme point carrier. -/
def standardFiniteCompactPoints : OpenSubgroup (FiniteAdelicGroupPoints F GLG) where
  toSubgroup := (FiniteAdelicGL.standardIntegral F n).toSubgroup.comap
    (finiteHomeomorph F n).toMonoidHom
  isOpen' := (FiniteAdelicGL.standardIntegral F n).isOpen.preimage (finiteHomeomorph F n).continuous

variable (n) in
theorem standardFiniteCompactPoints_isCompact :
    IsCompact (standardFiniteCompactPoints F n : Set (FiniteAdelicGroupPoints F GLG)) :=
  (finiteHomeomorph F n).toHomeomorph.isCompact_preimage.mpr (FiniteAdelicGL.standardIntegralCompact F n)

/-- The block-parabolic scheme points identify with the usual block-upper matrices. -/
def blockParabolicPointsEquiv (S : CommAlgCat.{u} 𝕜) :
    (P).affinePoints S ≃* B.parabolic S :=
  ((isRepresentedBy_blockParabolic (Fin n) 𝕜 wt).pointsEquiv ((algSpec 𝕜).obj (op S))).trans
    ((ofMatrixSubgroupsAffineEquiv
      (hH := fun f _ hg => map_mem_blockParabolicSubgroup wt f.hom hg) 𝕜 S).trans
      (MulEquiv.subgroupCongr (blockParabolicSubgroup_blockShapeWeight B S)))

omit [NumberField F] in
@[simp]
theorem blockParabolicPointsEquiv_val (S : CommAlgCat.{u} 𝕜) (x : (P).affinePoints S) :
    (blockParabolicPointsEquiv F B S x).val =
      affinePointsEquiv (Fin n) 𝕜 S ((P).affinePointsTarget p S x) := rfl

/-- On the adelic points of the block parabolic, the standard compact yields the
actual block Iwasawa height on group-scheme points. -/
theorem isIwasawaCompact_blockParabolic : IsIwasawaCompact p (standardCompactPoints F n) := by
  refine ⟨(adelicHomeomorph F n).toHomeomorph.isCompact_preimage.mpr (isCompact_standardCompact F n), ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g, k, heq⟩ := AdelicBlockScalarSections.exists_parabolic_mul_standardCompact F B (adelicHomeomorph F n x)
  let S := CommAlgCat.of F (AdeleRing (𝓞 F) F)
  let y := (blockParabolicPointsEquiv F B S).symm g
  have hy : adelicHomeomorph F n (map F P GLG p y) = g.val := by
    change affinePointsEquiv (Fin n) 𝕜 S ((P).affinePointsTarget p S y) = g.val
    rw [← blockParabolicPointsEquiv_val, MulEquiv.apply_symm_apply]
  let z := (adelicHomeomorph F n).symm k.val
  have hz : z ∈ standardCompactPoints F n := by
    change (adelicHomeomorph F n) z ∈ standardCompact F n
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact k.property
  refine ⟨map F P GLG p y, ⟨y, rfl⟩, z, hz, (adelicHomeomorph F n).injective ?_⟩
  rw [map_mul, hy, ContinuousMulEquiv.apply_symm_apply]
  exact heq.symm

variable (n) in
theorem standardCompactPoints_isMaximalCompact :
    IsMaximalCompactSubgroup F GLG (standardCompactPoints F n) := by
  rw [standardCompactPoints, RankinSelbergGlobal.gaugeStandardCompact, Subgroup.comap_equiv_eq_map_symm']
  exact isMaximalCompactSubgroup_generalLinear F n

theorem mem_standardCompactPoints_iff (g : AdelicGroupPoints F GLG) :
    g ∈ standardCompactPoints F n ↔
      infinite F GLG g ∈ generalLinearStandardInfiniteCompact F n ∧
      finite F GLG g ∈ standardFiniteCompactPoints F n := by
  change (adelicHomeomorph F n g ∈ standardCompact F n) ↔ _
  rw [mem_standardCompact_iff, ← infiniteHomeomorph_infinite, ← finiteHomeomorph_finite]
  rfl

variable (n) in
theorem standardCompactPoints_comap_ofInfinite :
    (standardCompactPoints F n).comap (ofInfinite F GLG).toMonoidHom =
      generalLinearStandardInfiniteCompact F n := by
  ext g
  change ofInfinite F GLG g ∈ standardCompactPoints F n ↔ _
  rw [mem_standardCompactPoints_iff]
  change infinite F GLG (pair F GLG g 1) ∈ _ ∧ finite F GLG (pair F GLG g 1) ∈ _ ↔ _
  rw [infinite_pair, finite_pair]
  exact ⟨And.left, fun h => ⟨h, (standardFiniteCompactPoints F n).one_mem⟩⟩

theorem ofFinite_mem_standardCompactPoints (g : standardFiniteCompactPoints F n) :
    ofFinite F GLG g.val ∈ standardCompactPoints F n := by
  rw [mem_standardCompactPoints_iff]
  change infinite F GLG (pair F GLG 1 g.val) ∈ _ ∧ finite F GLG (pair F GLG 1 g.val) ∈ _
  rw [infinite_pair, finite_pair]
  exact ⟨(generalLinearStandardInfiniteCompact F n).one_mem, g.property⟩

theorem ofInfinite_mem_standardCompactPoints (g : generalLinearStandardInfiniteCompact F n) :
    ofInfinite F GLG g.val ∈ standardCompactPoints F n := by
  rw [mem_standardCompactPoints_iff]
  change infinite F GLG (pair F GLG g.val 1) ∈ _ ∧ finite F GLG (pair F GLG g.val 1) ∈ _
  rw [infinite_pair, finite_pair]
  exact ⟨g.property, (standardFiniteCompactPoints F n).one_mem⟩

/-- The scheme unipotent points are the original block-unipotent matrices. -/
def blockUnipotentPointsEquiv (S : CommAlgCat.{u} 𝕜) :
    (U).affinePoints S ≃* B.unipotentSubgroup S :=
  ((isRepresentedBy_blockUnipotent (Fin n) 𝕜 wt).pointsEquiv ((algSpec 𝕜).obj (op S))).trans
    ((ofMatrixSubgroupsAffineEquiv
      (hH := fun f _ hg => map_mem_blockUnipotentSubgroup wt f.hom hg) 𝕜 S).trans
      (MulEquiv.subgroupCongr (blockUnipotentSubgroup_blockShapeWeight B S)))

omit [NumberField F] in
@[simp]
theorem blockUnipotentPointsEquiv_val (S : CommAlgCat.{u} 𝕜) (x : (U).affinePoints S) :
    (blockUnipotentPointsEquiv F B S x).val =
      affinePointsEquiv (Fin n) 𝕜 S ((U).affinePointsTarget uG S x) := rfl

open Langlands.Automorphic (OperatorRealization)
open Langlands.Automorphic.UnitaryCharacterPairing (leftStabilizer)

private theorem realizedSection_unipotent
    (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
    (φ : AdelicBlockScalarSections.RealizedSections F B S) (v : AdelicGroupPoints F U)
    (g : AdelicGroupPoints F GLG) :
    φ.val (adelicHomeomorph F n (map F U GLG uG v * g)) = φ.val (adelicHomeomorph F n g) := by
  let u := blockUnipotentPointsEquiv F B (CommAlgCat.of F (AdeleRing (𝓞 F) F)) v
  obtain ⟨w, hw, he⟩ := u.property
  change w.val = u.val at he
  rw [map_mul]
  change φ.val (u.val * adelicHomeomorph F n g) = _
  rw [← he]
  exact φ.property.1 ⟨w, hw⟩ _

private theorem adelicHomeomorph_map_rational_parabolic
    (qRat : RationalGroupPoints F P) :
    adelicHomeomorph F n (map F P GLG p (rational F P qRat)) =
      (AdelicBlockParabolic.rational F B (blockParabolicPointsEquiv F B (CommAlgCat.of F F) qRat)).val := by
  have hqRat := (DFunLike.congr_fun (rational_naturality F P p) qRat).symm
  change map F P GLG p (rational F P qRat) =
    rational F GLG ((P).affinePointsTarget p (CommAlgCat.of F F) qRat) at hqRat
  rw [hqRat]
  exact adelicEquiv_rational F n _

private theorem realizedSection_rationalLevi
    (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
    (φ : AdelicBlockScalarSections.RealizedSections F B S) (qRat : RationalGroupPoints F M)
    (g : AdelicGroupPoints F GLG) :
    φ.val (adelicHomeomorph F n
        (map F M GLG (blockLeviInclusion F B ≫ p) (rational F M qRat) * g)) =
      φ.val (adelicHomeomorph F n g) := by
  let l := blockLeviInclusion F B
  let qP := (M).affinePointsTarget l (CommAlgCat.of F F) qRat
  have hq := (DFunLike.congr_fun (rational_naturality F M l) qRat).symm
  change map F M P l (rational F M qRat) = rational F P qP at hq
  rw [map_mul, map_comp_apply_of_hom, hq, adelicHomeomorph_map_rational_parabolic F B]
  exact AdelicBlockScalarSections.realizedSection_rational F B S φ _ (adelicHomeomorph F n g)

/-- The matrix scalar sections satisfy the actual scheme parabolic quotient invariance. -/
theorem realizedSection_isLeftInvariantUnder_parabolic
    (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
    (φ : AdelicBlockScalarSections.RealizedSections F B S) :
    IsLeftInvariantUnder F GLG (parabolicQuotientSubgroup F p
      (blockUnipotentInclusion F B) (blockLeviInclusion F B))
      (fun g => φ.val (adelicHomeomorph F n g)) := by
  change parabolicQuotientSubgroup F p (blockUnipotentInclusion F B) (blockLeviInclusion F B) ≤
    leftStabilizer (fun g : AdelicGroupPoints F GLG => φ.val (adelicHomeomorph F n g))
  refine sup_le ?_ ?_
  · rintro _ ⟨v, rfl⟩ g
    change φ.val (adelicHomeomorph F n
      (map F U GLG (blockUnipotentInclusion F B ≫ p) v * g)) = _
    rw [blockUnipotentInclusion_comp]
    exact realizedSection_unipotent F B S φ v g
  · rintro _ ⟨qRat, rfl⟩ g
    exact realizedSection_rationalLevi F B S φ qRat g

end Langlands.Global.AdelicBlockEisensteinGeometry
