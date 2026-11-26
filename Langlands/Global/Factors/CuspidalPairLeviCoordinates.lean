import Langlands.Global.AdelicBlockParabolicCharacters
import Langlands.Global.AdelicBlockEisensteinRoots
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.AdelicGLDeterminantNormOne
import Langlands.GroupScheme.Rational.BlockCharacterProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Matrix coordinates of the adelic block Levi -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockParabolic
open AdelicBlockDeterminantCharacter

variable (F : Type) [Field F] [NumberField F] {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "GLG" => groupScheme (Fin n) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "M" => blockLeviScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt
local notation "l" => blockLeviInclusion F B
local notation "mG" => blockLeviHom (Fin n) 𝕜 wt
local notation "A" => CommAlgCat.of F (Adeles F)

local instance blockLeviCoordinatesAffineHom : IsAffineHom (M).X.hom := (blockLevi_isConnectedReductive F B).isAffineHom
local instance blockLeviCoordinatesAffine : IsAffine (M).X.left := isAffine_of_isAffineHom (M).X.hom
local instance blockLeviCoordinatesFiniteType : LocallyOfFiniteType (M).X.hom :=
  have := (blockLevi_isConnectedReductive F B).smooth
  inferInstance

omit [NumberField F] in
/-- The affine scheme Levi points are the block diagonal matrix subgroup. -/
def blockLeviAffineEquiv (S : CommAlgCat 𝕜) : (M).affinePoints S ≃* B.Levi S :=
  ((isRepresentedBy_blockLevi (Fin n) 𝕜 wt).pointsEquiv ((algSpec 𝕜).obj (op S))).trans
    ((ofMatrixSubgroupsAffineEquiv
      (hH := fun f _ hg => map_mem_blockLeviSubgroup wt f.hom hg) 𝕜 S).trans
      ((MulEquiv.subgroupCongr (blockLeviSubgroup_blockShapeWeight B S)).trans
        (B.leviEquiv S).symm))

omit [NumberField F] in
theorem leviEmbedding_blockLeviAffineEquiv (S : CommAlgCat 𝕜) (m : (M).affinePoints S) :
    B.leviEmbedding S (blockLeviAffineEquiv F B S m) =
      affinePointsEquiv (Fin n) 𝕜 S ((M).affinePointsTarget mG S m) := by
  let e := (B.leviEquiv S)
  let m' : B.leviSubgroup S :=
    MulEquiv.subgroupCongr (blockLeviSubgroup_blockShapeWeight B S)
      (ofMatrixSubgroupsAffineEquiv (hH := fun f _ hg => map_mem_blockLeviSubgroup wt f.hom hg) 𝕜 S
        ((isRepresentedBy_blockLevi (Fin n) 𝕜 wt).pointsEquiv ((algSpec 𝕜).obj (op S)) m))
  exact congrArg Subtype.val (e.apply_symm_apply m')

/-- Adelic block coordinates of the Levi. -/
abbrev matrixLeviPoint : AdelicGroupPoints F M ≃* FullLevi F B := blockLeviAffineEquiv F B A

theorem adelicHomeomorph_map_blockLevi (m : AdelicGroupPoints F M) :
    adelicHomeomorph F n (map F P GLG p (map F M P l m)) =
      B.leviEmbedding (Adeles F) (matrixLeviPoint F B m) := by
  rw [← map_comp_apply_of_hom, blockLeviInclusion_comp]
  exact (leviEmbedding_blockLeviAffineEquiv F B A m).symm

omit [NumberField F] in
theorem blockParabolicPointsEquiv_blockLeviInclusion (S : CommAlgCat 𝕜) (m : (M).affinePoints S) :
    blockParabolicPointsEquiv F B S ((M).affinePointsTarget l S m) =
      B.leviInParabolic S (blockLeviAffineEquiv F B S m) := by
  apply Subtype.ext
  rw [blockParabolicPointsEquiv_val, B.leviInParabolic_val, leviEmbedding_blockLeviAffineEquiv]
  congr 1
  change (m ≫ (l).hom.hom) ≫ (p).hom.hom = m ≫ (mG).hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, blockLeviInclusion_comp]

omit [NumberField F] in
theorem blockLeviInclusion_comp_parabolicBlockHom (i : Fin B.length) :
    l ≫ parabolicBlockHom B 𝕜 i = blockProjectionHom B 𝕜 i := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv (Fin (B.size i)) 𝕜 T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_parabolicBlockHom,
    pointsEquiv_blockProjectionHom]
  apply Units.ext
  ext a b
  rw [B.leviProjection_apply, blockParabolicTestPointsEquiv_val, blockLeviPointsEquiv_entry,
    Category.assoc, ← Grp.comp_hom_hom, blockLeviInclusion_comp]

omit [NumberField F] in
theorem affinePointsEquiv_blockProjectionHom (S : CommAlgCat 𝕜) (m : (M).affinePoints S)
    (i : Fin B.length) :
    affinePointsEquiv (Fin (B.size i)) 𝕜 S (m ≫ (blockProjectionHom B 𝕜 i).hom.hom) =
      blockLeviAffineEquiv F B S m i := by
  have he := affinePointsEquiv_parabolicBlockHom F B i S ((M).affinePointsTarget l S m)
  rw [blockParabolicPointsEquiv_blockLeviInclusion, B.leviProjection_section] at he
  change affinePointsEquiv (Fin (B.size i)) 𝕜 S
    ((m ≫ (l).hom.hom) ≫ (parabolicBlockHom B 𝕜 i).hom.hom) = _ at he
  rw [Category.assoc, ← Grp.comp_hom_hom, blockLeviInclusion_comp_parabolicBlockHom] at he
  exact he

theorem determinantNorm_matrixLeviPoint_of_normOne {m : AdelicGroupPoints F M}
    (hm : m ∈ normOneSubgroup F M) (i : Fin B.length) :
    determinantNorm F (B.size i) (matrixLeviPoint F B m i) = 1 := by
  let f := blockProjectionHom B 𝕜 i
  let χ := (determinantCharacter (Fin (B.size i)) 𝕜).toMul
  have hn := (mem_normOneSubgroup F M m).mp hm (f ≫ χ)
  change characterNorm F M (f ≫ χ) m = 1 at hn
  rw [characterNorm_comp, characterNorm_determinantCharacter] at hn
  change determinantNorm F (B.size i) (affinePointsEquiv _ 𝕜 A (m ≫ f.hom.hom)) = 1 at hn
  rwa [affinePointsEquiv_blockProjectionHom] at hn

omit [NumberField F] in
private theorem isCentral_comp_blockProjectionHom {T : GroupScheme (Spec 𝕜)}
    {a : T ⟶ M} (ha : IsCentral a) (i : Fin B.length) :
    IsCentral (a ≫ blockProjectionHom B 𝕜 i) := by
  intro V x
  let f := blockProjectionHom B 𝕜 i
  have hf {V' : Over (Spec 𝕜)} (y : V' ⟶ (groupScheme (Fin (B.size i)) 𝕜).X) :
      (y ≫ (blockInclusionHom B 𝕜 i).hom.hom) ≫ f.hom.hom = y := by
    apply (pointsEquiv (Fin (B.size i)) 𝕜 V').injective
    rw [pointsEquiv_blockProjectionHom, blockLeviPointsEquiv_blockInclusionHom,
      Pi.mulSingle_eq_same]
  rw [mem_center]
  intro V' u y
  have hc := commute_of_mem_center (ha V' (u ≫ x)) (y ≫ (blockInclusionHom B 𝕜 i).hom.hom)
  have h := congrArg (fun z => z ≫ f.hom.hom) hc.eq
  rw [MonObj.mul_comp, MonObj.mul_comp, hf] at h
  show _ * _ = _ * _
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

omit [NumberField F] in
private theorem affinePointsEquiv_scalarTorus (b : ℕ) (S : CommAlgCat 𝕜)
    (x : (algSpec 𝕜).obj (op S) ⟶ (Gm (Spec 𝕜)).X) :
    affinePointsEquiv (Fin b) 𝕜 S (x ≫ (scalarTorus (Fin b) 𝕜).hom.hom) =
      Matrix.GeneralLinearGroup.scalar (Fin b)
        (Gm.affinePointsEquiv ((algSpec 𝕜).obj (op S)).hom x) := by
  let f := (Corepresented.affineSectionsIso S).inv.hom.toRingHom
  suffices h : Matrix.GeneralLinearGroup.map f
      (affinePointsEquiv (Fin b) 𝕜 S (x ≫ (scalarTorus (Fin b) 𝕜).hom.hom)) =
        Matrix.GeneralLinearGroup.map f
          (Matrix.GeneralLinearGroup.scalar (Fin b)
            (Gm.affinePointsEquiv ((algSpec 𝕜).obj (op S)).hom x)) by
    apply Units.ext
    ext i j
    apply (Corepresented.affineSectionsAlgEquiv S).symm.injective
    exact congrArg (fun g : GL (Fin b) Γ(((algSpec 𝕜).obj (op S)).left, ⊤) => g.val i j) h
  dsimp only [f]
  rw [← pointsEquiv_eq_affinePointsEquiv, map_scalar, pointsEquiv_scalarTorus,
    gm_pointsEquiv_eq_affinePointsEquiv]
  rfl

/-- Every block of a canonical split-component point is a positive real scalar idele. -/
theorem exists_matrixLeviPoint_eq_positiveScalar {m : AdelicGroupPoints F M}
    (hm : m ∈ RestrictionSplitCentre.canonicalSubgroup F M) (i : Fin B.length) :
    ∃ z : ℝ≥0ˣ, matrixLeviPoint F B m i = AdelicGL.scalar F (B.size i) (PositiveRealIdeles.full F z) := by
  let T := RestrictionSplitCentre.canonicalTorus F M
  let a := RestrictionSplitCentre.canonicalComponent F M
  have ha := RestrictionSplitCentre.isSplitComponent_canonicalComponent F M
  rw [RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  let f := blockProjectionHom B 𝕜 i
  have hn : Nonempty (Fin (B.size i)) := ⟨⟨0, B.positive i⟩⟩
  let : IsAffineHom (groupScheme (Fin (B.size i)) 𝕜).X.hom := isAffineHom_groupScheme _ _
  obtain ⟨χ, hχ⟩ := (scalarTorus_isSplitComponent (n := Fin (B.size i)) F).exists_factor
    ha.1.1.1 (isCentral_comp_blockProjectionHom F B ha.1.2 i)
  let χ' := (rationalCharacters.equivCharacterLattice T) (Additive.ofMul χ)
  obtain ⟨z, hz⟩ := (PositiveRealTorus.mem_intrinsicSubgroup_iff F T x).mp hx χ'
  change PositiveRealIdeles.full F z =
    Gm.affinePointsEquiv ((algSpec 𝕜).obj (op A)).hom (x ≫ χ.hom.hom) at hz
  refine ⟨z, ?_⟩
  rw [← affinePointsEquiv_blockProjectionHom F B A]
  change affinePointsEquiv (Fin (B.size i)) 𝕜 A ((x ≫ a.hom.hom) ≫ f.hom.hom) = _
  rw [Category.assoc, ← Grp.comp_hom_hom, ← hχ, Grp.comp_hom_hom, ← Category.assoc,
    affinePointsEquiv_scalarTorus, ← hz]
  rfl

end Langlands.Global.AdelicBlockEisensteinGeometry
