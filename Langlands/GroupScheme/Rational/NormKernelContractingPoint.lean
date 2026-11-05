import Langlands.GroupScheme.Rational.NormKernelStandardCocharacter
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Norm-kernel cocharacter points escaping every compact set -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G)

/-- Intrinsic torus evaluation followed by the inclusion is the dynamic
cocharacter point used in contraction. -/
theorem cocharPoint_comp_torus (ζ : cocharacterLattice T) (t : Fˣ) :
    cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t =
      rationalPoints.map i (CocharacterUniformizer.cocharacterPoints F T ζ t) := by
  rw [cocharPoint_eq]
  change _ ≫ _ ≫ _ = (_ ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

section NormKernel

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Vanishing pairings with all ambient characters put every cocharacter value
in the actual common norm kernel. -/
theorem cocharPoint_mem_rationalCommonNormKernel
    (ζ : cocharacterLattice T)
    (hζ : ∀ χ : rationalCharacters G, latticePairing T (torusCharacterRestrict i χ) ζ = 0)
    (t : Fˣ) :
    cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t ∈
      Plancherel.rationalCommonNormKernel G := by
  apply (Plancherel.mem_rationalCommonNormKernel G _).mpr
  intro χ
  rw [cocharPoint_comp_torus, ← rationalCharacterEval_characterRestrict]
  change Plancherel.fieldNormUnits F
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm
      (torusCharacterRestrict i χ))
        (CocharacterUniformizer.cocharacterPoints F T ζ t)) = 1
  rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints, hζ χ,
    zpow_zero, map_one]

end NormKernel

section Escape

variable [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [IsAffine G.X.left]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A positive character pairing makes powers of a cocharacter point leave
every ambient compact set whenever the parameter's field powers tend to zero. -/
theorem eventually_cocharPoint_pow_not_mem_compact
    (hi : IsClosedSubgroup i) (ζ : cocharacterLattice T)
    (α : characterLattice T) (hα : 0 < latticePairing T α ζ)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t ^ n ∉ C := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine T.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.X
  let χ : rationalCharacters T.toGrp := (rationalCharacters.equivCharacterLattice T).symm α
  let f : rationalPoints T.toGrp → F := fun x => (rationalCharacterEval χ x : F)
  have hf : Continuous f :=
    Units.continuous_val.comp (continuous_rationalCharacterEval T.toGrp χ)
  let D : Set (rationalPoints T.toGrp) := rationalPoints.map i ⁻¹' C
  have hD : IsCompact D :=
    (isClosedEmbedding_rationalPointMap F i.hom.hom).isCompact_preimage hC
  have hclosed : IsClosed (f '' D) := (hD.image hf).isClosed
  have hzero : (0 : F) ∉ f '' D := by
    rintro ⟨x, _, hx⟩
    exact (rationalCharacterEval χ x).ne_zero hx
  let p : ℕ := (latticePairing T α ζ).toNat
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hpair : (p : ℤ) = latticePairing T α ζ := Int.toNat_of_nonneg hα.le
  let c : ℕ → rationalPoints T.toGrp :=
    fun n => CocharacterUniformizer.cocharacterPoints F T ζ (t ^ n)
  have hval (n : ℕ) : f (c n) = ((t : F) ^ n) ^ p := by
    dsimp only [f, c, χ]
    rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
      ← hpair, zpow_natCast]
    rfl
  have hlim : Tendsto (fun n => f (c n)) atTop (𝓝 (0 : F)) := by
    simpa only [hval, zero_pow hp.ne'] using ht.pow p
  filter_upwards [hlim.eventually (hclosed.isOpen_compl.mem_nhds hzero)] with n hn
  intro hnC
  apply hn
  refine ⟨c n, ?_, rfl⟩
  change rationalPoints.map i (CocharacterUniformizer.cocharacterPoints F T ζ (t ^ n)) ∈ C
  rw [← cocharPoint_comp_torus, cocharPoint_pow]
  exact hnC

end Escape

section Corrected

variable [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- The actual point obtained by evaluating the integral Weyl correction. -/
def normKernelCocharacterPoint (ζ : cocharacterLattice T) (t : Fˣ) :
    rationalPoints G :=
  cocharPoint (CommGroupScheme.groupHom (normKernelCocharacter i ζ) ≫ i) t

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem normKernelCocharacterPoint_mem (ζ : cocharacterLattice T) (t : Fˣ) :
    normKernelCocharacterPoint i ζ t ∈ Plancherel.rationalCommonNormKernel G :=
  cocharPoint_mem_rationalCommonNormKernel i _
    (latticePairing_normKernelCocharacter_restrict i ζ) t

variable [IsAffineHom G.X.hom] [IsAffine G.X.left]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- The corrected standard cocharacter for a proper face escapes every compact set. -/
theorem eventually_normKernelCocharacterPoint_pow_not_mem_compact
    (hi : IsSplitSubtorus i) (hRoots : HasRelativeRootSystem i)
    (ν : cocharacterLattice T) {J : Set (characterLattice T)}
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν J ζ)
    (hJ : J ⊂ simpleRelativeRoots i ν)
    (t : Fˣ) (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, normKernelCocharacterPoint i ζ t ^ n ∉ C := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨α, hα, hαJ⟩ := Set.exists_of_ssubset hJ
  exact eventually_cocharPoint_pow_not_mem_compact i hi.2 _ α
    ((hζ.normKernelCocharacter_of_relativeRootSystem i hi.1 hRoots ν).2.2 α hα hαJ) t ht C hC

end Corrected

end Langlands.GroupScheme
