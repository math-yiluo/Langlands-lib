import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicPositiveImageClosed
import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.Group.HaarModulus
import Langlands.Representation.Aubert.General.Conjugation

/-! # The adelic modulus `δ_P` of a dynamic parabolic and Haar probability on compact subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  {G P U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- The adelic image of a closed subgroup of an affine group scheme is closed. -/
theorem isClosed_range_map_of_isClosedSubgroup {H : GroupScheme (Spec (CommRingCat.of F))}
    (f : H ⟶ G) (hf : IsClosedSubgroup f) :
    IsClosed ((map F H G f).toMonoidHom.range : Set (AdelicGroupPoints F G)) := by
  have : IsClosedImmersion f.hom.hom.left := hf
  have : IsAffine H.X.left := isAffine_of_isAffineHom f.hom.hom.left
  rw [MonoidHom.coe_range]
  exact (isClosedEmbedding_map F H G f).isClosed_range

omit [NumberField F] in
/-- The source of a closed subgroup of an affine group scheme is affine. -/
theorem isAffine_left_of_isClosedSubgroup {H : GroupScheme (Spec (CommRingCat.of F))}
    (f : H ⟶ G) (hf : IsClosedSubgroup f) : IsAffine H.X.left := by
  have : IsClosedImmersion f.hom.hom.left := hf
  exact isAffine_of_isAffineHom f.hom.hom.left

/-- An injective embedding of adelic points is a topological group isomorphism onto its image. -/
def rangeEquiv {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsEmbedding (map F H G f)) :
    AdelicGroupPoints F H ≃ₜ* (map F H G f).toMonoidHom.range where
  toMulEquiv := MonoidHom.ofInjective (f := (map F H G f).toMonoidHom) hf.injective
  continuous_toFun := (map F H G f).continuous.subtype_mk _
  continuous_invFun := by
    refine hf.isInducing.continuous_iff.mpr ?_
    have h : ∀ x : (map F H G f).toMonoidHom.range,
        map F H G f ((MonoidHom.ofInjective (f := (map F H G f).toMonoidHom)
          hf.injective).symm x) = x :=
      fun x => MonoidHom.apply_ofInjective_symm hf.injective x
    simpa only [Function.comp_def, MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      MulEquiv.coe_toEquiv_symm, h] using continuous_subtype_val

omit [IsAffine G.X.left] in
@[simp] theorem rangeEquiv_apply_coe {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsEmbedding (map F H G f)) (x : AdelicGroupPoints F H) :
    (rangeEquiv F f hf x : AdelicGroupPoints F G) = map F H G f x := rfl

omit [IsAffine G.X.left] in
@[simp] theorem map_rangeEquiv_symm {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsEmbedding (map F H G f)) (x : (map F H G f).toMonoidHom.range) :
    map F H G f ((rangeEquiv F f hf).symm x) = x :=
  MonoidHom.apply_ofInjective_symm hf.injective x

section Image

variable [LocallyOfFiniteType G.X.hom] (iP : P ⟶ G) (iU : U ⟶ G)

/-- The Haar modulus of conjugation by the adelic image of `iP` on the closed adelic image of
`iU`, pulled back to `P(𝔸_F)`: its value at `p` is the factor `δ` with
`μ(g E g⁻¹) = δ μ(E)` for `g` the image of `p` and a Haar measure `μ` on the image of `iU`. -/
def imageModulus
    (hcl : IsClosed ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (hn : ∀ p : AdelicGroupPoints F P, map F P G iP p ∈
      Subgroup.normalizer ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G))) :
    AdelicGroupPoints F P →* ℝ≥0ˣ :=
  (HaarModulus.closedNormalizerCharacter _ hcl).comp
    ((map F P G iP).toMonoidHom.codRestrict _ hn)

@[simp] theorem imageModulus_apply
    (hcl : IsClosed ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (hn : ∀ p : AdelicGroupPoints F P, map F P G iP p ∈
      Subgroup.normalizer ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (p : AdelicGroupPoints F P) :
    imageModulus F iP iU hcl hn p =
      HaarModulus.closedNormalizerCharacter _ hcl ⟨map F P G iP p, hn p⟩ := rfl

-- `Regular` is not implied by `IsHaarMeasure`; it is needed for Haar scaling.
set_option linter.overlappingInstances false in
/-- **Defining integral identity of the image modulus on `U(𝔸_F)`.** For every Haar measure
`m` on the adelic points of `U` and every function `f` on `G(𝔸_F)`,
`∫ f(p⁻¹ u p) dm(u) = δ(p) ∫ f(u) dm(u)`, with `u` running through the image of `U(𝔸_F)`. -/
theorem integral_conj_imageModulus [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (hemb : IsEmbedding (map F U G iU))
    (hcl : IsClosed ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (hn : ∀ p : AdelicGroupPoints F P, map F P G iP p ∈
      Subgroup.normalizer ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (p : AdelicGroupPoints F P) (m : Measure (AdelicGroupPoints F U))
    [m.IsHaarMeasure] [m.Regular] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AdelicGroupPoints F G → E) :
    ∫ u, f ((map F P G iP p)⁻¹ * map F U G iU u * map F P G iP p) ∂m =
      (imageModulus F iP iU hcl hn p : ℝ≥0) • ∫ u, f (map F U G iU u) ∂m := by
  let H := (map F U G iU).toMonoidHom.range
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  have : LocallyCompactSpace H := hcl.locallyCompactSpace
  let e := rangeEquiv F iU hemb
  let g : Subgroup.normalizer (H : Set (AdelicGroupPoints F G)) := ⟨map F P G iP p, hn p⟩
  let ψ : AdelicGroupPoints F U ≃ₜ* AdelicGroupPoints F U :=
    (e.trans (HaarModulus.normalizerConj H g)).trans e.symm
  have hψ : ∀ u, map F U G iU (ψ.symm u) =
      (map F P G iP p)⁻¹ * map F U G iU u * map F P G iP p := by
    intro u
    change map F U G iU (e.symm ((HaarModulus.normalizerConj H g).symm (e u))) = _
    rw [map_rangeEquiv_symm, HaarModulus.normalizerConj_symm_apply]
    rfl
  have hchar : mulEquivHaarChar ψ = (imageModulus F iP iU hcl hn p : ℝ≥0) := by
    rw [imageModulus_apply, HaarModulus.closedNormalizerCharacter_eq,
      HaarModulus.normalizerCharacter_apply]
    exact Aubert.General.mulEquivHaarChar_trans_symm e _
  let f' : AdelicGroupPoints F U → E := fun u => f (map F U G iU u)
  have hlhs : (∫ u, f ((map F P G iP p)⁻¹ * map F U G iU u * map F P G iP p) ∂m) =
      ∫ u, f' (ψ.symm u) ∂m := by
    simp only [f', hψ]
  rw [hlhs, ← hchar]
  let e' := ψ.toHomeomorph.toMeasurableEquiv
  change (∫ u, f' (e'.symm u) ∂m) = _
  rw [← integral_map_equiv e'.symm, e'.map_symm]
  change (∫ u, f' u ∂(m.comap ψ)) = _
  rw [← mulEquivHaarChar_smul_eq_comap m ψ]
  exact integral_smul_nnreal_measure f' _

end Image

section Dynamic

variable {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

include hU in
/-- `U(χ)(𝔸_F)` is closed in `G(𝔸_F)`. -/
theorem isClosed_range_map_unipotent :
    IsClosed ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)) :=
  isClosed_range_map_of_isClosedSubgroup F iU
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU)

omit [IsAffine G.X.left] in
include hP hU in
/-- `P(χ)(𝔸_F)` normalizes `U(χ)(𝔸_F)` inside `G(𝔸_F)`. -/
theorem map_parabolic_mem_normalizer (p : AdelicGroupPoints F P) :
    map F P G iP p ∈
      Subgroup.normalizer ((map F U G iU).toMonoidHom.range : Set (AdelicGroupPoints F G)) := by
  have key : ∀ g ∈ (map F P G iP).toMonoidHom.range,
      ∀ x ∈ (map F U G iU).toMonoidHom.range,
        g * x * g⁻¹ ∈ (map F U G iU).toMonoidHom.range := fun g hg x hx =>
    Dynamic.range_unipotent_isNormalizedBy_range_parabolic hP hU _ g x hg hx
  have hg : map F P G iP p ∈ (map F P G iP).toMonoidHom.range := ⟨p, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key _ hg x
  · intro hx
    have h := key _ (inv_mem hg) _ hx
    simpa [mul_assoc] using h

variable [LocallyOfFiniteType G.X.hom]

/-- **The adelic modulus `δ_P` of the dynamic parabolic `P = P(χ)`.** Its value at
`p ∈ P(𝔸_F)` is the Haar modulus of conjugation by `p` on the closed subgroup `U(χ)(𝔸_F)`
of `G(𝔸_F)`: `μ(p E p⁻¹) = δ_P(p) μ(E)` for every Haar measure `μ` on `U(χ)(𝔸_F)`. -/
def parabolicModulus : AdelicGroupPoints F P →* ℝ≥0ˣ :=
  imageModulus F iP iU (isClosed_range_map_unipotent F hU) (map_parabolic_mem_normalizer F hP hU)

theorem parabolicModulus_apply (p : AdelicGroupPoints F P) :
    parabolicModulus F hP hU p =
      HaarModulus.closedNormalizerCharacter _ (isClosed_range_map_unipotent F hU)
        ⟨map F P G iP p, map_parabolic_mem_normalizer F hP hU p⟩ := rfl

include hU in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The representing scheme of `U(χ)` is affine. -/
theorem isAffine_unipotent : IsAffine U.X.left :=
  isAffine_left_of_isClosedSubgroup F iU
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU)

include hP in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The representing scheme of `P(χ)` is affine. -/
theorem isAffine_parabolic : IsAffine P.X.left :=
  isAffine_left_of_isClosedSubgroup F iP
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP)

include hU in
omit [NumberField F] in
/-- The representing scheme of `U(χ)` is locally of finite type. -/
theorem locallyOfFiniteType_unipotent : LocallyOfFiniteType U.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU).locallyOfFiniteType

include hP in
omit [NumberField F] in
/-- The representing scheme of `P(χ)` is locally of finite type. -/
theorem locallyOfFiniteType_parabolic : LocallyOfFiniteType P.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP).locallyOfFiniteType

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- The representing scheme of the centralizer `Z(χ)`, the Levi factor `M`, is affine. -/
theorem isAffine_centralizer {M : GroupScheme (Spec (CommRingCat.of F))} {iM : M ⟶ G}
    (hM : (Dynamic.centralizer χ).IsRepresentedBy iM) : IsAffine M.X.left :=
  isAffine_left_of_isClosedSubgroup F iM
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hM)

omit [NumberField F] in
/-- The representing scheme of the centralizer `Z(χ)` is locally of finite type. -/
theorem locallyOfFiniteType_centralizer {M : GroupScheme (Spec (CommRingCat.of F))}
    {iM : M ⟶ G} (hM : (Dynamic.centralizer χ).IsRepresentedBy iM) :
    LocallyOfFiniteType M.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hM).locallyOfFiniteType

include hU in
omit [LocallyOfFiniteType G.X.hom] in
/-- `U(χ)(𝔸_F) → G(𝔸_F)` is a closed embedding. -/
theorem isClosedEmbedding_map_unipotent :
    haveI := isAffine_unipotent F hU
    IsClosedEmbedding (map F U G iU) := by
  have := isAffine_unipotent F hU
  have : IsClosedImmersion iU.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent χ hU
  exact isClosedEmbedding_map F U G iU

set_option linter.overlappingInstances false in
/-- **Defining integral identity of `δ_P`.** For every Haar measure `m` on `U(χ)(𝔸_F)`, every
`p ∈ P(χ)(𝔸_F)` and every function `f` on `G(𝔸_F)`,
`∫ f(p⁻¹ u p) dm(u) = δ_P(p) ∫ f(u) dm(u)`. -/
theorem integral_conj_parabolicModulus [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom]
    (p : AdelicGroupPoints F P) (m : Measure (AdelicGroupPoints F U))
    [m.IsHaarMeasure] [m.Regular] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AdelicGroupPoints F G → E) :
    ∫ u, f ((map F P G iP p)⁻¹ * map F U G iU u * map F P G iP p) ∂m =
      (parabolicModulus F hP hU p : ℝ≥0) • ∫ u, f (map F U G iU u) ∂m :=
  integral_conj_imageModulus F iP iU (isClosedEmbedding_map_unipotent F hU).isEmbedding _ _ p m f

/-- If `δ_P` is the normalized idele norm of an algebraic character of `P`, as
`AdelicParabolicModulusStatement` asserts, the product formula makes `δ_P` trivial on `P(F)`. -/
theorem parabolicModulus_rational_of_eq (δ : AlgebraicCharacter F P)
    (h : ∀ p, parabolicModulus F hP hU p = characterNorm F P δ p)
    (γ : RationalGroupPoints F P) : parabolicModulus F hP hU (rational F P γ) = 1 := by
  rw [h, characterNorm_rational]

/-- Under the same comparison, `δ_P` is continuous. -/
theorem continuous_parabolicModulus_of_eq (δ : AlgebraicCharacter F P)
    (h : ∀ p, parabolicModulus F hP hU p = characterNorm F P δ p) :
    Continuous (parabolicModulus F hP hU) := by
  have hfun : (parabolicModulus F hP hU : AdelicGroupPoints F P → ℝ≥0ˣ) =
      characterNorm F P δ := funext h
  rw [hfun]
  exact (characterNorm F P δ).continuous

end Dynamic

section Compact

variable (G) [LocallyOfFiniteType G.X.hom]

/-- **The Haar probability measure on a compact subgroup `K` of `G(𝔸_F)`**, the Haar measure of
the compact group `K` normalized by `meas(K) = 1` (Mœglin–Waldspurger I.1.13). -/
def compactHaarProbability (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) : Measure K :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  Measure.haarMeasure ⊤

instance compactHaarProbability_isHaarMeasure (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) :
    (compactHaarProbability F G K hK).IsHaarMeasure := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  unfold compactHaarProbability
  infer_instance

instance compactHaarProbability_isProbabilityMeasure (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) :
    IsProbabilityMeasure (compactHaarProbability F G K hK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  constructor
  have h : Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
      ((⊤ : TopologicalSpace.PositiveCompacts K) : Set K) = 1 := Measure.haarMeasure_self
  simpa [compactHaarProbability] using h

/-- Every left Haar probability measure on `K` is `compactHaarProbability`. -/
theorem eq_compactHaarProbability (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) (m : Measure K) [m.IsHaarMeasure]
    [IsProbabilityMeasure m] : m = compactHaarProbability F G K hK := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hreg : m = Measure.haarScalarFactor m (compactHaarProbability F G K hK) •
      compactHaarProbability F G K hK :=
    Measure.isMulLeftInvariant_eq_smul_of_innerRegular _ _
  have hc := congrArg (fun ν : Measure K => ν Set.univ) hreg
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  have h1 : Measure.haarScalarFactor m (compactHaarProbability F G K hK) = 1 := by
    exact_mod_cast hc.symm
  rw [hreg, h1, one_smul]

end Compact

end Langlands.Global.AdelicGroupPoints
