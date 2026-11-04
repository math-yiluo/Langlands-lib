import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-! # The actual zero subgroup and the rational norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation k Γ₀) {G H D C : GroupScheme (Spec (CommRingCat.of k))}

/-- Character-valuation kernels are preserved by actual group-scheme homomorphisms. -/
theorem map_characterValuationKernel_le (f : H ⟶ G) :
    (characterValuationKernel v H).map (rationalPoints.map f) ≤
      characterValuationKernel v G := by
  rintro _ ⟨h, hh, rfl⟩
  change h ∈ characterValuationKernel v H at hh
  rw [mem_characterValuationKernel] at hh ⊢
  intro χ
  rw [← rationalCharacterEval_characterRestrict]
  exact hh _

/-- Every actual derived-cover point has character value one, before applying a valuation. -/
theorem rationalCharacterEval_simplyConnectedImage
    {d : D ⟶ G} {π : C ⟶ D} (h : IsSimplyConnectedDerivedCover d π)
    {g : rationalPoints G} (hg : g ∈ simplyConnectedImage d π)
    (χ : rationalCharacters G) : rationalCharacterEval χ g = 1 := by
  obtain ⟨c, rfl⟩ := hg
  change rationalCharacterEval χ (rationalPoints.map d (rationalPoints.map π c)) = 1
  rw [← rationalCharacterEval_characterRestrict, h.isDerivedSubgroup.characterRestrict_eq_zero,
    rationalCharacterEval_zero]

/-- The actual simply connected image lies in every character-valuation kernel. -/
theorem simplyConnectedImage_le_characterValuationKernel
    {d : D ⟶ G} {π : C ⟶ D} (h : IsSimplyConnectedDerivedCover d π) :
    simplyConnectedImage d π ≤ characterValuationKernel v G := by
  intro g hg
  rw [mem_characterValuationKernel]
  intro χ
  rw [rationalCharacterEval_simplyConnectedImage h hg, Units.val_one, map_one]

end Field

end Langlands.Geometry.Building

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- At the base field the rational and coefficient evaluations agree. -/
theorem rationalCharacterEval_coeff (χ : rationalCharacters G) (x : rationalPoints G) :
    rationalCharacterEval χ x =
      Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)
        (G.affinePointsTarget χ.toMul _ (rationalCoeffEquiv k G x)) := by
  rw [rationalCharacterEval_apply, ← GaloisPoint.gm_units_rationalCoeffEquiv]
  congr 1

/-- Base-changed rational-character evaluation is the same coefficient-point evaluation. -/
theorem rationalCharacterEval_baseChange (χ : rationalCharacters G)
    (x : rationalPoints (baseChanged k L G)) :
    rationalCharacterEval (rationalCharacters.baseChange (baseMap k L) χ) x =
      Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
        (G.affinePointsTarget χ.toMul _ (baseChangeCoeffEquiv k L G x)) := by
  apply Units.ext
  rw [rationalCharacterEval_val, rationalCharacters.characterEval_baseChange,
    characterEval_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom _ =
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom _
  congr 1

/-- Evaluation after extension is scalar extension of the original unit. -/
theorem rationalCharacterEval_extend (χ : rationalCharacters G) (x : rationalPoints G) :
    rationalCharacterEval (rationalCharacters.baseChange (baseMap k L) χ)
        (rationalExtend k L G x) =
      Units.map (algebraMap k L).toMonoidHom (rationalCharacterEval χ x) := by
  rw [rationalCharacterEval_baseChange, baseChangeCoeffEquiv_rationalExtend]
  have hn := DFunLike.congr_fun
    (G.affinePointsTarget_naturality χ.toMul
      (CommAlgCat.ofHom (Algebra.ofId k L))) (rationalCoeffEquiv k G x)
  change GaloisPoint.extend k L (Gm (Spec (CommRingCat.of k))).toGrp
      (G.affinePointsTarget χ.toMul _ (rationalCoeffEquiv k G x)) =
    G.affinePointsTarget χ.toMul _
      (GaloisPoint.extend k L G (rationalCoeffEquiv k G x)) at hn
  rw [← hn, GaloisPoint.gm_units_extend, rationalCharacterEval_coeff]

/-- A character from the base field commutes with Galois conjugation of points. -/
theorem rationalCharacterEval_conjugate (χ : rationalCharacters G) (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalCharacterEval (rationalCharacters.baseChange (baseMap k L) χ)
        (rationalConjugate k L G σ x) =
      Units.map σ.toMonoidHom
        (rationalCharacterEval (rationalCharacters.baseChange (baseMap k L) χ) x) := by
  rw [rationalCharacterEval_baseChange, baseChangeCoeffEquiv_rationalConjugate]
  have hn := DFunLike.congr_fun
    (G.affinePointsTarget_naturality χ.toMul (CommAlgCat.ofHom σ.toAlgHom))
      (baseChangeCoeffEquiv k L G x)
  change GaloisPoint.conjugate k L (Gm (Spec (CommRingCat.of k))).toGrp σ
      (G.affinePointsTarget χ.toMul _ (baseChangeCoeffEquiv k L G x)) =
    G.affinePointsTarget χ.toMul _
      (GaloisPoint.conjugate k L G σ (baseChangeCoeffEquiv k L G x)) at hn
  rw [← hn, GaloisPoint.gm_units_conjugate, rationalCharacterEval_baseChange]

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

open Langlands.GroupScheme.GaloisPointComparison

section Norm

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {Γk ΓL : Type*} [LinearOrderedCommGroupWithZero Γk]
  [LinearOrderedCommGroupWithZero ΓL]
  (vk : Valuation k Γk) (vL : Valuation L ΓL) [vk.HasExtension vL]

set_option backward.isDefEq.respectTransparency false in
/-- A norm of a point with unit character values again has unit character values. -/
theorem torusNormIwahori_le_characterValuationKernel
    [FiniteDimensional k L] [IsGalois k L]
    (hinv : ∀ (σ : L ≃ₐ[k] L) (z : L), vL (σ z) = vL z)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left] :
    torusNormIwahori k L vL T ≤ characterValuationKernel vk T.toGrp := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ characterValuationKernel vL
    ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp at hx
  rw [mem_characterValuationKernel] at hx ⊢
  intro χ
  apply (Valuation.HasExtension.val_map_eq_one_iff vk vL _).mp
  change vL (Units.map (algebraMap k L).toMonoidHom
    (rationalCharacterEval χ (rationalNorm k L T x)) : L) = 1
  rw [← rationalCharacterEval_extend, rationalExtend_norm]
  simp only [map_prod, Units.coe_prod]
  apply Finset.prod_eq_one
  intro σ _
  rw [rationalCharacterEval_conjugate]
  change vL (σ (rationalCharacterEval
    (rationalCharacters.baseChange (baseMap k L) χ) x : L)) = 1
  rw [hinv]
  exact hx _

/-- Unit character values descend through an extension of valuations. -/
theorem comap_characterValuationKernel_le
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (characterValuationKernel vL (baseChanged k L G)).comap
        (rationalExtend k L G) ≤ characterValuationKernel vk G := by
  intro g hg
  change rationalExtend k L G g ∈ characterValuationKernel vL (baseChanged k L G) at hg
  rw [mem_characterValuationKernel] at hg ⊢
  intro χ
  apply (Valuation.HasExtension.val_map_eq_one_iff vk vL _).mp
  have hχ := hg (rationalCharacters.baseChange (baseMap k L) χ)
  rw [rationalCharacterEval_extend] at hχ
  exact hχ

end Norm

section Local

open scoped NNReal

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The prescribed intermediate-field valuation extends the prescribed valuation of `K`. -/
instance intermediateValuation_extends_fixedField
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    (LocalGalois.Separable.fixedFieldValuation F).HasExtension
      (intermediateValuation F L) where
  val_isEquiv_comap _ _ := Iff.rfl

/-- Every automorphism over `K` preserves the prescribed intermediate-field valuation. -/
theorem intermediateValuation_conjugate
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (σ : L ≃ₐ[UnramifiedClosure F] L) (x : L) :
    intermediateValuation F L (σ x) = intermediateValuation F L x := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : IsScalarTower F L (SeparableClosure F) := IsScalarTower.of_algebraMap_eq' rfl
  apply NNReal.eq
  change spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) (σ x)) =
    spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) x)
  rw [← spectralNorm.eq_of_tower, ← spectralNorm.eq_of_tower]
  exact (spectralNorm_eq_of_equiv (σ.restrictScalars F) x).symm

namespace UnramifiedZeroDatum

variable {F} {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The entire actual zero subgroup over `K` has unit rational-character values. -/
theorem zeroPoints_le_characterValuationKernel :
    E.zeroPoints ≤
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) H := by
  apply sup_le
  · exact simplyConnectedImage_le_characterValuationKernel _
      E.isSimplyConnectedDerivedCover
  · have ht : E.torusIwahori ≤
        characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) E.T.toGrp := by
      let : (LocalGalois.Separable.fixedFieldValuation F).HasExtension
          (intermediateValuation F E.L) := intermediateValuation_extends_fixedField F E.L
      change torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T ≤ _
      exact torusNormIwahori_le_characterValuationKernel
        (k := UnramifiedClosure F) (L := E.L)
        (LocalGalois.Separable.fixedFieldValuation F) (intermediateValuation F E.L)
        (intermediateValuation_conjugate F E.L) E.T
    exact (Subgroup.map_mono ht).trans (map_characterValuationKernel_le _ E.i)

end UnramifiedZeroDatum

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The actual descended zero subgroup has unit rational-character values over `F`. -/
theorem anisotropicZeroPoints_le_characterValuationKernel
    {M : GroupScheme (Spec (CommRingCat.of F))}
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) M)) :
    anisotropicZeroPoints E ≤ characterValuationKernel (ValuativeRel.valuation F) M := by
  intro g hg
  apply comap_characterValuationKernel_le (k := F) (L := UnramifiedClosure F)
    (ValuativeRel.valuation F)
    (LocalGalois.Separable.fixedFieldValuation F) M
  exact E.zeroPoints_le_characterValuationKernel hg

/-- The normalized character norm and the canonical valuation have the same unit kernel. -/
theorem characterValuationKernel_eq_rationalCommonNormKernel
    (G : GroupScheme (Spec (CommRingCat.of F))) :
    characterValuationKernel (ValuativeRel.valuation F) G =
      Plancherel.rationalCommonNormKernel G := by
  ext g
  rw [mem_characterValuationKernel, Plancherel.mem_rationalCommonNormKernel]
  apply forall_congr'
  intro χ
  change _ ↔ rationalCharacterEval χ g ∈ (Plancherel.fieldNormUnits F).ker
  rw [Plancherel.fieldNormUnits_ker, FML.unitGroup, Valuation.mem_unitGroup_iff]

namespace ZeroSubgroupDatum

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- The actual full centralizer-zero factor lies in the canonical rational norm kernel. -/
theorem centralizerZero_le_rationalCommonNormKernel :
    E.centralizerZero ≤ Plancherel.rationalCommonNormKernel Z := by
  rw [← characterValuationKernel_eq_rationalCommonNormKernel]
  exact anisotropicZeroPoints_le_characterValuationKernel E.centralizerDatum

/-- The canonical inclusion of the actual centralizer-zero factor into the norm kernel. -/
def centralizerZeroNormKernelHom :
    E.centralizerZero →* Plancherel.rationalCommonNormKernel Z :=
  E.centralizerZero.subtype.codRestrict _
    (fun z => E.centralizerZero_le_rationalCommonNormKernel z.property)

@[simp] theorem centralizerZeroNormKernelHom_coe (z : E.centralizerZero) :
    (E.centralizerZeroNormKernelHom z : rationalPoints Z) = z := rfl

/-- The entire actual zero subgroup lies in the canonical rational norm kernel of `G`. -/
theorem zeroSubgroup_le_rationalCommonNormKernel :
    E.zeroSubgroup ≤ Plancherel.rationalCommonNormKernel G := by
  rw [← characterValuationKernel_eq_rationalCommonNormKernel]
  apply sup_le
  · exact simplyConnectedImage_le_characterValuationKernel _
      E.isSimplyConnectedDerivedCover
  · exact (Subgroup.map_mono
      (anisotropicZeroPoints_le_characterValuationKernel E.centralizerDatum)).trans
        (map_characterValuationKernel_le _ j)

end ZeroSubgroupDatum

end Local

end Langlands.Geometry.Building
