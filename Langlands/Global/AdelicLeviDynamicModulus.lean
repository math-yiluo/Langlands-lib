import Langlands.Global.AdelicParabolicModulusProof

/-! # Adelically measured dynamic radicals at Levi points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P Z U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
  (hZred : IsConnectedReductive Z)

include hZred in
/-- At a Levi point of a dynamic parabolic the modular character is its action modulus on the
radical. The Levi is reductive, and the ambient group and radical may be arbitrary. -/
theorem modularCharacter_levi_eq_dynamicModulus (m : AdelicGroupPoints F Z) :
    Measure.modularCharacter (map F Z P (Dynamic.centralizerToParabolic hP hZ) m) =
      (parabolicModulus F hP hU (map F Z P (Dynamic.centralizerToParabolic hP hZ) m) : ℝ≥0) := by
  have : IsAffine Z.X.left := isAffine_centralizer F hZ
  have : IsAffine U.X.left := isAffine_unipotent F hU
  have : LocallyOfFiniteType Z.X.hom := locallyOfFiniteType_centralizer F hZ
  have : LocallyOfFiniteType U.X.hom := locallyOfFiniteType_unipotent F hU
  have hPc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  have hZc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hZ
  have hUc := Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU
  have : IsClosedImmersion iP.hom.hom.left := hPc
  have : IsClosedImmersion iZ.hom.hom.left := hZc
  have : IsClosedImmersion iU.hom.hom.left := hUc
  -- the closed images
  let PG := (map F P G iP).toMonoidHom.range
  let ZG := (map F Z G iZ).toMonoidHom.range
  let UG := (map F U G iU).toMonoidHom.range
  have hclP : IsClosed (PG : Set (AdelicGroupPoints F G)) :=
    isClosed_range_map_of_isClosedSubgroup F iP hPc
  have hclZ : IsClosed (ZG : Set (AdelicGroupPoints F G)) :=
    isClosed_range_map_of_isClosedSubgroup F iZ hZc
  have hclU : IsClosed (UG : Set (AdelicGroupPoints F G)) := isClosed_range_map_unipotent F hU
  have : LocallyCompactSpace PG := hclP.locallyCompactSpace
  have : LocallyCompactSpace ZG := hclZ.locallyCompactSpace
  have : LocallyCompactSpace UG := hclU.locallyCompactSpace
  let eP := rangeEquiv F iP (isClosedEmbedding_map F P G iP).isEmbedding
  let eZ := rangeEquiv F iZ (isClosedEmbedding_map F Z G iZ).isEmbedding
  have hinjZ : Function.Injective (map F Z G iZ) := (isClosedEmbedding_map F Z G iZ).injective
  let ιZ := Dynamic.centralizerToParabolic hP hZ
  let ιU := Dynamic.unipotentToParabolic hP hU
  let lim := Dynamic.limitGroupHom hP hZ
  have hZP : ∀ m : AdelicGroupPoints F Z, map F P G iP (map F Z P ιZ m) = map F Z G iZ m := by
    intro m
    change (m ≫ ιZ.hom.hom) ≫ iP.hom.hom = m ≫ iZ.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, Dynamic.centralizerToParabolic_comp]
  have hUP : ∀ v : AdelicGroupPoints F U, map F P G iP (map F U P ιU v) = map F U G iU v := by
    intro v
    change (v ≫ ιU.hom.hom) ≫ iP.hom.hom = v ≫ iU.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, Dynamic.unipotentToParabolic_comp]
  have hMQ : ZG ≤ PG := by
    rintro _ ⟨m, rfl⟩
    exact ⟨map F Z P ιZ m, hZP m⟩
  have hUQ : UG ≤ PG := by
    rintro _ ⟨v, rfl⟩
    exact ⟨map F U P ιU v, hUP v⟩
  -- the Levi retraction `PG → ZG` induced by the limit homomorphism
  let f : PG →* AdelicGroupPoints F G :=
    ((map F Z G iZ).toMonoidHom.comp (map F P Z lim).toMonoidHom).comp
      eP.symm.toMulEquiv.toMonoidHom
  have hfc : Continuous f :=
    (map F Z G iZ).continuous.comp ((map F P Z lim).continuous.comp eP.symm.continuous)
  have hfM : ∀ q, f q ∈ ZG := fun q => ⟨_, rfl⟩
  have hfid : ∀ m (hm : m ∈ ZG), f ⟨m, hMQ hm⟩ = m := by
    rintro _ ⟨m, rfl⟩
    have he : eP.symm ⟨map F Z G iZ m, hMQ ⟨m, rfl⟩⟩ = map F Z P ιZ m := by
      apply eP.injective
      apply Subtype.ext
      rw [ContinuousMulEquiv.apply_symm_apply, rangeEquiv_apply_coe, hZP]
    change map F Z G iZ (map F P Z lim (eP.symm ⟨map F Z G iZ m, hMQ ⟨m, rfl⟩⟩)) = _
    rw [he]
    have hm : map F P Z lim (map F Z P ιZ m) = m := by
      change (m ≫ ιZ.hom.hom) ≫ lim.hom.hom = m
      rw [Category.assoc, ← Grp.comp_hom_hom, Dynamic.centralizerToParabolic_comp_limitGroupHom,
        Grp.id_hom_hom, Category.comp_id]
    rw [hm]
    rfl
  have hfker : ∀ q, f q = 1 ↔ (q : AdelicGroupPoints F G) ∈ UG := by
    intro q
    obtain ⟨p, rfl⟩ := eP.surjective q
    have hq : ((eP p : PG) : AdelicGroupPoints F G) = p ≫ iP.hom.hom := rfl
    change map F Z G iZ (map F P Z lim (eP.symm (eP p))) = 1 ↔ _
    rw [ContinuousMulEquiv.symm_apply_apply, hq]
    have h1 : map F Z G iZ (map F P Z lim p) = 1 ↔ map F P Z lim p = 1 :=
      ⟨fun h => hinjZ (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
    rw [h1]
    change p ≫ lim.hom.hom = 1 ↔ _
    rw [Dynamic.limitGroupHom_eq_one_iff χ hP hZ p, ← hU.2]
    exact SubgroupFunctor.mem_range
  have hsd := Aubert.General.IsSemidirectDecomposition.of_retraction hMQ hUQ f hfM hfid hfker
  have hp := Aubert.General.IsSemidirectDecomposition.continuous_of_retraction_projection
    hMQ hUQ f hfM hfid hfker hfc
  -- unimodularity of the Levi factor
  have hM : ∀ m : ZG, Measure.modularCharacter m = 1 := by
    intro m
    obtain ⟨m', rfl⟩ := eZ.surjective m
    rw [Aubert.General.modularCharacter_continuousMulEquiv eZ m']
    exact modularCharacter_eq_one_of_isConnectedReductive F Z hZred m'
  let mG := eZ m
  have hmod := hsd.modularCharacter_levi hp mG
  have hpM : eP (map F Z P ιZ m) = (⟨mG.val, hMQ mG.property⟩ : PG) := by
    apply Subtype.ext
    exact hZP m
  rw [← hpM, Aubert.General.modularCharacter_continuousMulEquiv eP, hM, one_mul] at hmod
  rw [parabolicModulus_apply, HaarModulus.closedNormalizerCharacter_eq]
  refine hmod.trans ?_
  change (HaarModulus.normalizerCharacter UG ⟨mG.val, hsd.levi_le_normalizer mG.property⟩ : ℝ≥0) = _
  have hsame : (⟨mG.val, hsd.levi_le_normalizer mG.property⟩ : Subgroup.normalizer (UG : Set _)) =
      ⟨map F P G iP (map F Z P ιZ m), map_parabolic_mem_normalizer F hP hU _⟩ :=
    Subtype.ext (hZP m).symm
  rw [hsame]

include hZred in
/-- The forward Haar modulus on a dynamic radical at an actual Levi point is the idele norm
of the conjugation determinant. Reductivity is used on the Levi. -/
theorem dynamicModulus_levi_eq_characterNorm [IsAffine Z.X.left] [LocallyOfFiniteType Z.X.hom]
    [IsAffineHom U.X.hom] (hPs : Smooth P.X.hom)
    {n : ℕ} (b : Lie.FiniteCoordinates U n) (m : AdelicGroupPoints F Z) :
    parabolicModulus F hP hU (map F Z P (Dynamic.centralizerToParabolic hP hZ) m) =
      characterNorm F Z ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter b).toMul m := by
  let f := Dynamic.centralizerToParabolic hP hZ
  have hchar := Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic hP hZ hU b
  rw [Lie.connectedReductiveAdjointDeterminant F Z hZred, add_zero] at hchar
  apply Units.ext
  change (parabolicModulus F hP hU (map F Z P f m) : ℝ≥0) = _
  rw [← modularCharacter_levi_eq_dynamicModulus hP hZ hU hZred m,
    modularCharacter_eq_characterNorm_of_local F P (Lie.adjointDeterminantCharacter P).toMul
      (PlaceGroupPoints.localModularCharacterAdjointDeterminant F P hPs), ← characterNorm_comp]
  change (characterNorm F Z (characterRestrict f (Lie.adjointDeterminantCharacter P)).toMul m : ℝ≥0) = _
  rw [hchar]

end Langlands.Global.AdelicGroupPoints
