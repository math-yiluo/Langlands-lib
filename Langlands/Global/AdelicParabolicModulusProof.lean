import Langlands.Global.AdelicParabolicModulusStatement
import Langlands.Global.AdelicLocalModularComparison
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof
import Langlands.Global.UnipotentRationalQuotientCompactProof
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Representation.Aubert.General.SemidirectModularCharacter
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition
import Langlands.GroupScheme.Dynamic.AdjointDeterminantCentralizerRestrictionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof

/-! # Proof of `AdelicParabolicModulusStatement`

The adelic modulus `δ_P` of a dynamic parabolic `P = P(χ)` of a connected reductive group is
the modular character of `P(𝔸_F)` and the idele norm of `det(Ad | Lie U)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]

section Compact

/-- If `H(F) \ H(𝔸_F)` is compact, the idele norm of every algebraic character of `H` is
trivial: it factors through the compact quotient by the product formula, and its image is a
compact subgroup of `ℝ≥0ˣ`. -/
theorem characterNorm_eq_one_of_compactSpace (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine H.X.left] [CompactSpace (RationalQuotient F H)] (χ : AlgebraicCharacter F H)
    (x : AdelicGroupPoints F H) : characterNorm F H χ x = 1 := by
  let φ := characterNorm F H χ
  have hφ : ∀ (r : rationalSubgroup F H) (y : AdelicGroupPoints F H),
      φ ((r : AdelicGroupPoints F H) * y) = φ y := by
    rintro ⟨_, ⟨z, rfl⟩⟩ y
    rw [map_mul]
    change characterNorm F H χ (rational F H z) * φ y = φ y
    rw [characterNorm_rational, one_mul]
  let ψ := LeftCosetSpace.lift (rationalSubgroup F H) φ hφ
  have hψ : Continuous ψ := LeftCosetSpace.continuous_lift _ φ hφ φ.continuous
  have hrange : ((φ.toMonoidHom.range : Subgroup ℝ≥0ˣ) : Set ℝ≥0ˣ) = Set.range ψ := by
    ext t
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨LeftCosetSpace.mk _ y, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective _ q
      exact ⟨y, rfl⟩
  have hK : IsCompact ((φ.toMonoidHom.range : Subgroup ℝ≥0ˣ) : Set ℝ≥0ˣ) := by
    rw [hrange]
    exact isCompact_range hψ
  exact continuousMonoidHom_eq_one_on_compactSubgroup (ContinuousMonoidHom.id ℝ≥0ˣ) _ hK
    ⟨x, rfl⟩

/-- A smooth affine group with compact rational quotient has unimodular adelic points. -/
theorem modularCharacter_eq_one_of_compactSpace (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] (hH : Smooth H.X.hom)
    [CompactSpace (RationalQuotient F H)] (x : AdelicGroupPoints F H) :
    Measure.modularCharacter x = 1 := by
  rw [modularCharacter_eq_characterNorm_of_local F H
    (Lie.adjointDeterminantCharacter H).toMul
    (PlaceGroupPoints.localModularCharacterAdjointDeterminant F H hH) x,
    characterNorm_eq_one_of_compactSpace, Units.val_one]

/-- A connected reductive group has unimodular adelic points. -/
theorem modularCharacter_eq_one_of_isConnectedReductive
    (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] (hH : IsConnectedReductive H) (x : AdelicGroupPoints F H) :
    Measure.modularCharacter x = 1 :=
  modularCharacter_eq_one_of_adjointDeterminant_eq_zero F H
    (modularCharacter_eq_characterNorm_of_local F H _
      (PlaceGroupPoints.localModularCharacterAdjointDeterminant F H hH.smooth))
    (Lie.connectedReductiveAdjointDeterminant F H hH) x

end Compact

section Parabolic

variable {G P Z U : GroupScheme (Spec (CommRingCat.of F))}
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hG : IsConnectedReductive G)
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

include hG hZ in
/-- **The modular character of `P(𝔸_F)` is `δ_P`.** The closed images of `P(𝔸_F)`, `Z(𝔸_F)`
and `U(𝔸_F)` in `G(𝔸_F)` form a continuous semidirect decomposition, with Levi projection
induced by the limit homomorphism `P ⟶ Z`; both factors are unimodular. -/
theorem modularCharacter_eq_parabolicModulus [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (p : AdelicGroupPoints F P) :
    Measure.modularCharacter p = (parabolicModulus F hP hU p : ℝ≥0) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
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
  let eU := rangeEquiv F iU (isClosedEmbedding_map F U G iU).isEmbedding
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
  have hZred : IsConnectedReductive Z := dynamicCentralizerReductive F G hG χ Z iZ hZc hZ
  have hM : ∀ m : ZG, Measure.modularCharacter m = 1 := by
    intro m
    obtain ⟨m', rfl⟩ := eZ.surjective m
    rw [Aubert.General.modularCharacter_continuousMulEquiv eZ m']
    exact modularCharacter_eq_one_of_isConnectedReductive F Z hZred m'
  -- unimodularity of the unipotent radical
  have hsmU : Smooth U.X.hom := (dynamicSmooth F G χ U iU).2.2 hU
  have : CompactSpace (RationalQuotient F U) :=
    unipotentRationalQuotientCompact F U hsmU ((dynamicConnected F G χ U iU).1 hU)
      (dynamicUnipotentUnipotence F G χ U iU hU)
  have hδU : ∀ v : UG, HaarModulus.normalizerCharacter UG
      ⟨v, Subgroup.le_normalizer v.property⟩ = 1 := by
    intro v
    apply Units.ext
    have he : Aubert.General.innerConjugation v =
        HaarModulus.normalizerConj UG ⟨v, Subgroup.le_normalizer v.property⟩ := by
      ext w
      rfl
    have hv := Aubert.General.modularCharacter_eq_innerConjugation v
    rw [he] at hv
    obtain ⟨v', rfl⟩ := eU.surjective v
    rw [Aubert.General.modularCharacter_continuousMulEquiv eU v',
      modularCharacter_eq_one_of_compactSpace F U hsmU v'] at hv
    exact hv.symm
  have key := hsd.modularCharacter_eq_restrictCharacter_of_unimodular hp hM hδU (eP p)
  rw [Aubert.General.modularCharacter_continuousMulEquiv eP p] at key
  exact key

include hG hZ in
/-- **`δ_P` is the idele norm of `det(Ad | Lie U)`.** By the previous theorem and the
all-place local formula, `δ_P` is the idele norm of the full adjoint determinant of `P`.
Write a point of `P(𝔸_F)` as a point of `U(𝔸_F)` times a point of `Z(𝔸_F)`. On `U(𝔸_F)` both
norms are trivial, because `U(F) \ U(𝔸_F)` is compact. On `Z(𝔸_F)` the two characters agree:
`Lie P = Lie U ⊕ Lie Z` and `det(Ad | Lie Z) = 0` for the connected reductive `Z`. -/
theorem parabolicModulus_eq_characterNorm [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left] {d : ℕ}
    (c : Lie.FiniteCoordinates U d) (p : AdelicGroupPoints F P) :
    parabolicModulus F hP hU p =
      characterNorm F P (Dynamic.adjointDeterminantCharacter hP hU c).toMul p := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine Z.X.left := isAffine_centralizer F hZ
  have : LocallyOfFiniteType Z.X.hom := locallyOfFiniteType_centralizer F hZ
  have : LocallyOfFiniteType U.X.hom := locallyOfFiniteType_unipotent F hU
  have hsmP : Smooth P.X.hom := (dynamicSmooth F G χ P iP).1 hP
  have hsmU : Smooth U.X.hom := (dynamicSmooth F G χ U iU).2.2 hU
  have : CompactSpace (RationalQuotient F U) :=
    unipotentRationalQuotientCompact F U hsmU ((dynamicConnected F G χ U iU).1 hU)
      (dynamicUnipotentUnipotence F G χ U iU hU)
  have hZred : IsConnectedReductive Z := dynamicCentralizerReductive F G hG χ Z iZ
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hZ) hZ
  apply Units.ext
  rw [← modularCharacter_eq_parabolicModulus F hG hP hZ hU p,
    modularCharacter_eq_characterNorm_of_local F P (Lie.adjointDeterminantCharacter P).toMul
      (PlaceGroupPoints.localModularCharacterAdjointDeterminant F P hsmP) p]
  congr 1
  let ιZ := Dynamic.centralizerToParabolic hP hZ
  let ιU := Dynamic.unipotentToParabolic hP hU
  obtain ⟨v, m, hvm⟩ := Dynamic.exists_eq_unipotent_mul_centralizer χ hP hZ hU p
  have hv : ∀ ψ : AlgebraicCharacter F P, characterNorm F P ψ (v ≫ ιU.hom.hom) = 1 :=
    fun ψ => (characterNorm_comp F U P ιU ψ v).symm.trans
      (characterNorm_eq_one_of_compactSpace F U (ιU ≫ ψ) v)
  have hchar : ιZ ≫ (Lie.adjointDeterminantCharacter P).toMul =
      ιZ ≫ (Dynamic.adjointDeterminantCharacter hP hU c).toMul := by
    have h1 := Dynamic.characterRestrict_adjointDeterminantCharacter_parabolic hP hZ hU c
    rw [Lie.connectedReductiveAdjointDeterminant F Z hZred, add_zero,
      ← Dynamic.adjointDeterminantCentralizerRestriction χ hP hZ hU c] at h1
    exact congrArg Additive.toMul h1
  have hm : characterNorm F P (Lie.adjointDeterminantCharacter P).toMul (m ≫ ιZ.hom.hom) =
      characterNorm F P (Dynamic.adjointDeterminantCharacter hP hU c).toMul
        (m ≫ ιZ.hom.hom) := by
    have e1 := characterNorm_comp F Z P ιZ (Lie.adjointDeterminantCharacter P).toMul m
    have e2 := characterNorm_comp F Z P ιZ (Dynamic.adjointDeterminantCharacter hP hU c).toMul m
    rw [hchar] at e1
    exact e1.symm.trans e2
  rw [hvm, map_mul, map_mul, hv, hv, hm]

end Parabolic

/-- **Proof of `AdelicParabolicModulusStatement`.** -/
theorem adelicParabolicModulus : AdelicParabolicModulusStatement.{u} := by
  intro F _ _ G hG χ P U iP iU hP hU
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine P.X.left := isAffine_parabolic F hP
  have : LocallyOfFiniteType P.X.hom := locallyOfFiniteType_parabolic F hP
  have : IsAffine U.X.left := isAffine_unipotent F hU
  intro d c
  exact ⟨fun p => parabolicModulus_eq_characterNorm F hG hP
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ) hU c p,
    fun p => modularCharacter_eq_parabolicModulus F hG hP
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ) hU p⟩

end Langlands.Global.AdelicGroupPoints
