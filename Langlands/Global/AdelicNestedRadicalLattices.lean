import Langlands.Global.AdelicNestedRadicalSplit
import Langlands.Global.AdelicIntertwiningStabilizer
import Langlands.Global.AdelicSubgroupHaarNormalization
import Langlands.Global.EisensteinConstantTerm.Points

/-! # The split extension of adelic radicals and their principal lattices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) {J Q : StandardIndex F G fam.i fam.ν}

local notation "U(" A ")" => (fam.iU A ≫ fam.p A)
local notation "Pts(" f ")" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range f)
local notation "Rat(" f ")" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range f)

namespace NestedRadicalSplit

variable (d : NestedRadicalSplit fam J Q)

/-- The inclusion in the ambient group of the complementary radical. -/
def complementHom : d.W ⟶ G := d.sectionHom ≫ U(J)

omit [NumberField F] in
/-- The complementary radical is closed in the ambient group. -/
theorem complement_closed : IsClosedSubgroup (d.complementHom fam) :=
  d.section_closed.comp (fam.closedU J)

local notation "W₀" => (d.complementHom fam)

/-- This complementary radical has compact principal quotient. -/
theorem compactSpace_complementQuotient : CompactSpace (LeftCosetSpace Rat(W₀)) := by
  have hu := (fam.isUnipotentRadical J).1.isUnipotent
  let hcl := d.complement_closed fam
  let ha : IsAffineHom d.W.X.hom := hcl.isAffineHom
  let hft : LocallyOfFiniteType d.W.X.hom := hcl.locallyOfFiniteType
  let : IsAffine d.W.X.left := isAffine_of_isAffineHom d.W.X.hom
  let : LocallyOfFiniteType (fam.U J).X.hom :=
    (show IsClosedSubgroup U(J) from fam.closedU J).locallyOfFiniteType
  have hW : IsUnipotent d.W := unipotentClosedSubgroup F (fam.U J) d.W _ d.section_closed hu
  exact AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F W₀
    (affineCartierSmooth F d.W ha hft) (charZeroUnipotentConnected F d.W ha hft hW) hW

end NestedRadicalSplit

/-- The adelic splitting in the actual closed subgroup ranges. The lattices
are the principal subgroups of those same ranges. -/
structure NestedRadicalCoordinates (d : NestedRadicalSplit fam J Q) where
  normal : Pts(U(Q)) →* Pts(U(J))
  sectionHom : Pts((d.complementHom fam)) →* Pts(U(J))
  projection : Pts(U(J)) →* Pts((d.complementHom fam))
  normal_coe : ∀ x, (normal x).val = x.val
  section_coe : ∀ x, (sectionHom x).val = x.val
  normal_embedding : IsEmbedding normal
  section_continuous : Continuous sectionHom
  projection_continuous : Continuous projection
  section_projection : ∀ x, projection (sectionHom x) = x
  projection_normal : ∀ x, projection (normal x) = 1
  kernel : ∀ x, projection x = 1 → ∃ n, normal n = x
  normal_principal : (Rat(U(J))).comap normal = Rat(U(Q))
  section_principal : ∀ x ∈ Rat((d.complementHom fam)), sectionHom x ∈ Rat(U(J))
  projection_principal : ∀ x ∈ Rat(U(J)), projection x ∈ Rat((d.complementHom fam))

private def closedRangeEquiv {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsClosedSubgroup f) : AdelicGroupPoints F H ≃ₜ* Pts(f) := by
  let : IsAffine H.X.left := isAffine_left_of_isClosedSubgroup F f hf
  let : IsClosedImmersion f.hom.hom.left := hf
  exact rangeEquiv F f (isClosedEmbedding_map F H G f).isEmbedding

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem closedRangeEquiv_mem_rational
    {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsClosedSubgroup f) (x : AdelicGroupPoints F H) :
    closedRangeEquiv f hf x ∈ Rat(f) ↔ x ∈ rationalSubgroup F H := by
  rw [mem_rationalSubgroup_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (closedRangeEquiv f hf).injective (Subtype.ext hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem map_mem_principal {A B : GroupScheme (Spec (CommRingCat.of F))}
    (f : A ⟶ B) {x : AdelicGroupPoints F A} (hx : x ∈ rationalSubgroup F A) :
    map F A B f x ∈ rationalSubgroup F B := by
  obtain ⟨y, rfl⟩ := hx
  rw [map_rational]
  exact ⟨_, rfl⟩

/-- The split scheme maps give a split extension of adelic points and their
principal lattices. The normal and section maps are the ambient inclusions. -/
def NestedRadicalCoordinatesStatement (d : NestedRadicalSplit fam J Q) : Prop :=
  Nonempty (NestedRadicalCoordinates fam d)

set_option maxHeartbeats 2200000 in
/-- The three range equivalences identify the scheme splitting with the
actual adelic subgroup coordinates. -/
theorem nestedRadicalCoordinates (d : NestedRadicalSplit fam J Q) :
    NestedRadicalCoordinatesStatement fam d := by
  let hU : IsClosedSubgroup U(J) := fam.closedU J
  let hN : IsClosedSubgroup U(Q) := fam.closedU Q
  let hW := d.complement_closed fam
  let eU := closedRangeEquiv U(J) hU
  let eN := closedRangeEquiv U(Q) hN
  let eW := closedRangeEquiv (d.complementHom fam) hW
  let ni := map F (fam.U Q) (fam.U J) d.normal
  let sj := map F d.W (fam.U J) d.sectionHom
  let pr := map F (fam.U J) d.W d.projection
  let i := eU.toMonoidHom.comp (ni.toMonoidHom.comp eN.symm.toMonoidHom)
  let j := eU.toMonoidHom.comp (sj.toMonoidHom.comp eW.symm.toMonoidHom)
  let p := eW.toMonoidHom.comp (pr.toMonoidHom.comp eU.symm.toMonoidHom)
  have hi (x : Pts(U(Q))) : (i x).val = x.val := by
    change map F (fam.U J) G U(J) (ni (eN.symm x)) = x.val
    rw [← map_comp_apply_of_hom, d.normal_comp]
    exact congrArg Subtype.val (eN.apply_symm_apply x)
  have hj (x : Pts((d.complementHom fam))) : (j x).val = x.val := by
    change map F (fam.U J) G U(J) (sj (eW.symm x)) = x.val
    rw [← map_comp_apply_of_hom]
    exact congrArg Subtype.val (eW.apply_symm_apply x)
  refine ⟨⟨i, j, p, hi, hj, ?_, eU.continuous.comp (sj.continuous.comp eW.symm.continuous),
    eW.continuous.comp (pr.continuous.comp eU.symm.continuous), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply IsEmbedding.subtypeVal.of_comp_iff.mp
    change IsEmbedding (fun x => (i x).val)
    simpa only [hi] using (IsEmbedding.subtypeVal : IsEmbedding
      (Subtype.val : Pts(U(Q)) → AdelicGroupPoints F G))
  · intro x
    change eW (pr (eU.symm (eU (sj (eW.symm x))))) = x
    rw [eU.symm_apply_apply, ← map_comp_apply_of_hom, d.section_projection]
    exact eW.apply_symm_apply x
  · intro x
    have h : pr (ni (eN.symm x)) = 1 :=
      (d.kernel _ (ni (eN.symm x))).mpr ⟨eN.symm x, rfl⟩
    change eW (pr (eU.symm (eU (ni (eN.symm x))))) = 1
    rw [eU.symm_apply_apply, h, map_one]
  · intro x hx
    have h : pr (eU.symm x) = 1 := eW.injective (hx.trans (map_one eW).symm)
    obtain ⟨y, hy⟩ := (d.kernel _ (eU.symm x)).mp h
    refine ⟨eN y, ?_⟩
    change eU (ni (eN.symm (eN y))) = x
    rw [eN.symm_apply_apply, show ni y = eU.symm x from hy, eU.apply_symm_apply]
  · ext x
    change i x ∈ Rat(U(J)) ↔ x ∈ Rat(U(Q))
    rw [mem_rationalSubgroup_range_iff, hi, mem_rationalSubgroup_range_iff]
    constructor
    · rintro ⟨y, hy⟩
      let y₀ := (fam.U J).affinePointsTarget U(J) _ y
      have hy₀ : rational F G y₀ = x.val := (map_rational U(J) y).symm.trans hy
      have hmem : y₀ ∈ AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range U(Q)) :=
        (rational_mem_adelicPoints_range_iff hN y₀).mp (hy₀.symm ▸ x.property)
      obtain ⟨z, hz⟩ := hmem
      exact ⟨z, (map_rational U(Q) z).trans ((congrArg (rational F G) hz).trans hy₀)⟩
    · rintro ⟨y, hy⟩
      refine ⟨(fam.U Q).affinePointsTarget d.normal _ y, ?_⟩
      change map F (fam.U J) G U(J)
        (rational F (fam.U J) ((fam.U Q).affinePointsTarget d.normal _ y)) = x.val
      rw [map_rational_affinePointsTarget, d.normal_comp]
      exact hy
  · intro x hx
    apply (closedRangeEquiv_mem_rational U(J) hU _).mpr
    have hx' : eW (eW.symm x) ∈ Rat((d.complementHom fam)) := by
      rw [eW.apply_symm_apply]
      exact hx
    have h := (closedRangeEquiv_mem_rational (d.complementHom fam) hW (eW.symm x)).mp hx'
    exact map_mem_principal d.sectionHom h
  · intro x hx
    apply (closedRangeEquiv_mem_rational (d.complementHom fam) hW _).mpr
    have hx' : eU (eU.symm x) ∈ Rat(U(J)) := by
      rw [eU.apply_symm_apply]
      exact hx
    have h := (closedRangeEquiv_mem_rational U(J) hU (eU.symm x)).mp hx'
    exact map_mem_principal d.projection h

end Langlands.Global.StandardParabolicFamily
