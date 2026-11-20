import Langlands.Global.AdelicParabolicModulus
import Langlands.Global.AdelicIwasawaIntegrationStatement
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Proof of the Iwasawa integration formula on `G(𝔸_F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj NNReal CompactlySupported Pointwise

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Levi

variable (F : Type u) [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iM : M ⟶ G} {iU : U ⟶ G}

/-- The adelic image of a representing group scheme consists of the adelic points of the
represented subgroup functor. -/
theorem mem_range_map_iff_of_isRepresentedBy {H : GroupScheme (Spec (CommRingCat.of F))}
    {Φ : SubgroupFunctor G} {i : H ⟶ G} (hi : Φ.IsRepresentedBy i)
    (x : AdelicGroupPoints F G) :
    x ∈ (map F H G i).toMonoidHom.range ↔
      x ∈ Φ.carrier ((algSpec (CommRingCat.of F)).obj
        (Opposite.op (CommAlgCat.of F (AdeleRing (𝓞 F) F)))) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (hi.pointsEquiv _ y).2
  · intro hx
    exact ⟨(hi.pointsEquiv _).symm ⟨x, hx⟩, hi.pointsEquiv_symm_comp ⟨x, hx⟩⟩

omit [NumberField F] in
/-- In a separated group scheme, `(lim g)⁻¹ g` lies in `U(χ)` for every point `g` of `P(χ)`. -/
theorem inv_limit_mul_mem_unipotent [IsSeparated G.X.hom] {T : Over (Spec (CommRingCat.of F))}
    (g : (Dynamic.parabolic χ).carrier T) :
    (Dynamic.limit χ g)⁻¹ * (g : T ⟶ G.X) ∈ (Dynamic.unipotent χ).carrier T := by
  have hz : (Dynamic.limit χ g)⁻¹ ∈ (Dynamic.centralizer χ).carrier T :=
    inv_mem (Dynamic.limit_mem_centralizer χ g)
  have h := (Subgroup.mem_normalizer_iff.mp
    (Dynamic.centralizer_le_normalizer_unipotent χ T hz) _).mp
      (Dynamic.mul_inv_limit_mem_unipotent χ g)
  have e : (Dynamic.limit χ g)⁻¹ * ((g : T ⟶ G.X) * (Dynamic.limit χ g)⁻¹) *
      (Dynamic.limit χ g)⁻¹⁻¹ = (Dynamic.limit χ g)⁻¹ * (g : T ⟶ G.X) := by
    group
  rw [e] at h
  exact h

omit [NumberField F] in
/-- The limit of `z x` with `z ∈ Z(χ)` and `x ∈ U(χ)` is `z`. -/
theorem limit_centralizer_mul_unipotent [IsSeparated G.X.hom]
    {T : Over (Spec (CommRingCat.of F))} {z x : T ⟶ G.X}
    (hz : z ∈ (Dynamic.centralizer χ).carrier T) (hx : x ∈ (Dynamic.unipotent χ).carrier T)
    (h : z * x ∈ (Dynamic.parabolic χ).carrier T) :
    Dynamic.limit χ ⟨z * x, h⟩ = z := by
  apply Dynamic.limit_eq
  have := (Dynamic.hasLimit_of_mem_centralizer χ hz).mul χ ((Dynamic.mem_unipotent χ).1 hx)
  rwa [mul_one] at this

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left]
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

include hP in
/-- `P(χ)(𝔸_F) → G(𝔸_F)` is a closed embedding. -/
theorem isClosedEmbedding_map_parabolic : IsClosedEmbedding (map F P G iP) := by
  have : IsClosedImmersion iP.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  exact isClosedEmbedding_map F P G iP

include hM in
/-- `Z(χ)(𝔸_F) → G(𝔸_F)` is a closed embedding. -/
theorem isClosedEmbedding_map_centralizer : IsClosedEmbedding (map F M G iM) := by
  have : IsClosedImmersion iM.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hM
  exact isClosedEmbedding_map F M G iM

include hP hM in
omit [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left] in
theorem map_centralizer_mem_range (m : AdelicGroupPoints F M) :
    map F M G iM m ∈ (map F P G iP).toMonoidHom.range :=
  (mem_range_map_iff_of_isRepresentedBy F hP _).2
    (Dynamic.centralizer_le_parabolic χ _ ((mem_range_map_iff_of_isRepresentedBy F hM _).1
      ⟨m, rfl⟩))

include hP hU in
omit [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left] in
theorem map_unipotent_mem_range (x : AdelicGroupPoints F U) :
    map F U G iU x ∈ (map F P G iP).toMonoidHom.range :=
  (mem_range_map_iff_of_isRepresentedBy F hP _).2
    (Dynamic.unipotent_le_parabolic χ _ ((mem_range_map_iff_of_isRepresentedBy F hU _).1
      ⟨x, rfl⟩))

include hP hM in
omit [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left] in
/-- `iM = iP ∘ (Z(χ) ⟶ P(χ))` on adelic points. -/
theorem map_centralizerToParabolic (m : AdelicGroupPoints F M) :
    map F P G iP (map F M P (Dynamic.centralizerToParabolic hP hM) m) = map F M G iM m := by
  change (m ≫ (Dynamic.centralizerToParabolic hP hM).hom.hom) ≫ iP.hom.hom = m ≫ iM.hom.hom
  rw [Category.assoc, ← Dynamic.grp_comp_hom_hom, Dynamic.centralizerToParabolic_comp]

variable [IsSeparated G.X.hom]

/-- The Levi projection of the image of `P(χ)(𝔸_F)` in `G(𝔸_F)` to `Z(χ)(𝔸_F)`. -/
def leviProjection : (map F P G iP).toMonoidHom.range →* AdelicGroupPoints F M :=
  (map F P M (Dynamic.limitGroupHom hP hM)).toMonoidHom.comp
    (rangeEquiv F iP (isClosedEmbedding_map_parabolic F hP).isEmbedding).symm.toMonoidHom

omit [IsAffine M.X.left] in
theorem continuous_leviProjection : Continuous (leviProjection F hP hM) :=
  (map F P M (Dynamic.limitGroupHom hP hM)).continuous.comp
    (rangeEquiv F iP (isClosedEmbedding_map_parabolic F hP).isEmbedding).symm.continuous

omit [IsAffine M.X.left] in
/-- The Levi projection, mapped to `G(𝔸_F)`, is the dynamic limit. -/
theorem map_leviProjection (q : (map F P G iP).toMonoidHom.range) :
    map F M G iM (leviProjection F hP hM q) =
      Dynamic.limit χ ⟨(q : AdelicGroupPoints F G),
        (mem_range_map_iff_of_isRepresentedBy F hP _).1 q.2⟩ := by
  have h := Dynamic.limitGroupHom_comp hP hM
    ((rangeEquiv F iP (isClosedEmbedding_map_parabolic F hP).isEmbedding).symm q)
  have he : hP.pointsEquiv _
      ((rangeEquiv F iP (isClosedEmbedding_map_parabolic F hP).isEmbedding).symm q) =
      ⟨(q : AdelicGroupPoints F G), (mem_range_map_iff_of_isRepresentedBy F hP _).1 q.2⟩ :=
    Subtype.ext (map_rangeEquiv_symm F iP _ q)
  rw [he] at h
  exact h

include hU in
omit [IsAffine M.X.left] [IsAffine U.X.left] in
theorem inv_map_leviProjection_mul_mem (q : (map F P G iP).toMonoidHom.range) :
    (map F M G iM (leviProjection F hP hM q))⁻¹ * (q : AdelicGroupPoints F G) ∈
      (map F U G iU).toMonoidHom.range := by
  rw [map_leviProjection]
  exact (mem_range_map_iff_of_isRepresentedBy F hU _).2 (inv_limit_mul_mem_unipotent F _)

/-- Levi coordinates, forward map: `(m, u) ↦ m u`. -/
def leviMul (x : AdelicGroupPoints F M × AdelicGroupPoints F U) :
    (map F P G iP).toMonoidHom.range :=
  ⟨map F M G iM x.1 * map F U G iU x.2,
    mul_mem (map_centralizer_mem_range F hP hM x.1) (map_unipotent_mem_range F hP hU x.2)⟩

/-- Levi coordinates, inverse map: `q ↦ (lim q, (lim q)⁻¹ q)`. -/
def leviSplit (q : (map F P G iP).toMonoidHom.range) :
    AdelicGroupPoints F M × AdelicGroupPoints F U :=
  (leviProjection F hP hM q,
    (rangeEquiv F iU (isClosedEmbedding_map_unipotent F hU).isEmbedding).symm
      ⟨_, inv_map_leviProjection_mul_mem F hP hM hU q⟩)

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left]
  [IsSeparated G.X.hom] in
@[simp] theorem coe_leviMul (x : AdelicGroupPoints F M × AdelicGroupPoints F U) :
    (leviMul F hP hM hU x : AdelicGroupPoints F G) = map F M G iM x.1 * map F U G iU x.2 :=
  rfl

omit [IsAffine M.X.left] in
@[simp] theorem leviSplit_fst (q : (map F P G iP).toMonoidHom.range) :
    (leviSplit F hP hM hU q).1 = leviProjection F hP hM q :=
  rfl

omit [IsAffine M.X.left] in
theorem map_leviSplit_snd (q : (map F P G iP).toMonoidHom.range) :
    map F U G iU (leviSplit F hP hM hU q).2 =
      (map F M G iM (leviProjection F hP hM q))⁻¹ * (q : AdelicGroupPoints F G) :=
  map_rangeEquiv_symm F iU _ _

omit [IsAffine U.X.left] in
theorem leviProjection_leviMul (x : AdelicGroupPoints F M × AdelicGroupPoints F U) :
    leviProjection F hP hM (leviMul F hP hM hU x) = x.1 := by
  apply (isClosedEmbedding_map_centralizer F hM).injective
  rw [map_leviProjection]
  exact limit_centralizer_mul_unipotent F
    ((mem_range_map_iff_of_isRepresentedBy F hM _).1 ⟨x.1, rfl⟩)
    ((mem_range_map_iff_of_isRepresentedBy F hU _).1 ⟨x.2, rfl⟩) _

theorem leviSplit_leviMul (x : AdelicGroupPoints F M × AdelicGroupPoints F U) :
    leviSplit F hP hM hU (leviMul F hP hM hU x) = x := by
  refine Prod.ext (leviProjection_leviMul F hP hM hU x)
    ((isClosedEmbedding_map_unipotent F hU).injective ?_)
  rw [map_leviSplit_snd, leviProjection_leviMul, coe_leviMul, inv_mul_cancel_left]

omit [IsAffine M.X.left] in
theorem leviMul_leviSplit (q : (map F P G iP).toMonoidHom.range) :
    leviMul F hP hM hU (leviSplit F hP hM hU q) = q := by
  apply Subtype.ext
  rw [coe_leviMul, map_leviSplit_snd, leviSplit_fst, mul_inv_cancel_left]

omit [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left] [IsSeparated G.X.hom] in
theorem continuous_leviMul : Continuous (leviMul F hP hM hU) :=
  (((map F M G iM).continuous.comp continuous_fst).mul
    ((map F U G iU).continuous.comp continuous_snd)).subtype_mk _

omit [IsAffine M.X.left] in
theorem continuous_leviSplit : Continuous (leviSplit F hP hM hU) := by
  have hpr := continuous_leviProjection F hP hM
  refine hpr.prodMk ((rangeEquiv F iU
    (isClosedEmbedding_map_unipotent F hU).isEmbedding).symm.continuous.comp ?_)
  exact (((map F M G iM).continuous.comp hpr).inv.mul continuous_subtype_val).subtype_mk _

/-- **Levi coordinates on `P(χ)(𝔸_F)`.** Multiplication `(m, u) ↦ m u` is a homeomorphism from
`Z(χ)(𝔸_F) × U(χ)(𝔸_F)` onto the image of `P(χ)(𝔸_F)` in `G(𝔸_F)`. -/
def leviCoordinates :
    AdelicGroupPoints F M × AdelicGroupPoints F U ≃ₜ (map F P G iP).toMonoidHom.range where
  toFun := leviMul F hP hM hU
  invFun := leviSplit F hP hM hU
  left_inv := leviSplit_leviMul F hP hM hU
  right_inv := leviMul_leviSplit F hP hM hU
  continuous_toFun := continuous_leviMul F hP hM hU
  continuous_invFun := continuous_leviSplit F hP hM hU

/-- The `U`-coordinate correction of left multiplication in Levi coordinates. -/
def leviCorrection (q : (map F P G iP).toMonoidHom.range) (m : AdelicGroupPoints F M) :
    AdelicGroupPoints F U :=
  (leviSplit F hP hM hU (q * leviMul F hP hM hU (m, 1))).2

omit [IsAffine M.X.left] in
theorem continuous_leviCorrection (q : (map F P G iP).toMonoidHom.range) :
    Continuous (leviCorrection F hP hM hU q) :=
  continuous_snd.comp ((continuous_leviSplit F hP hM hU).comp
    (continuous_const.mul ((continuous_leviMul F hP hM hU).comp
      (continuous_id.prodMk continuous_const))))

/-- Left multiplication is triangular in Levi coordinates. -/
theorem leviSplit_mul_leviMul (q : (map F P G iP).toMonoidHom.range)
    (x : AdelicGroupPoints F M × AdelicGroupPoints F U) :
    leviSplit F hP hM hU (q * leviMul F hP hM hU x) =
      (leviProjection F hP hM q * x.1, leviCorrection F hP hM hU q x.1 * x.2) := by
  have h1 : ∀ y, leviProjection F hP hM (q * leviMul F hP hM hU y) =
      leviProjection F hP hM q * y.1 := fun y => by
    rw [map_mul, leviProjection_leviMul]
  refine Prod.ext (h1 x) ((isClosedEmbedding_map_unipotent F hU).injective ?_)
  change map F U G iU (leviSplit F hP hM hU (q * leviMul F hP hM hU x)).2 =
    map F U G iU (leviCorrection F hP hM hU q x.1 * x.2)
  rw [map_leviSplit_snd, map_mul (map F U G iU), leviCorrection, map_leviSplit_snd, h1, h1]
  simp only [Subgroup.coe_mul, coe_leviMul, map_one, mul_one, mul_assoc]

end Levi

section Measure

variable (F : Type u) [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {iP : P ⟶ G} {iM : M ⟶ G} {iU : U ⟶ G}
  [IsAffine G.X.left] [IsAffine P.X.left] [IsAffine M.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType M.X.hom] [LocallyOfFiniteType U.X.hom] [IsSeparated G.X.hom]
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

/-- Haar measure on the image of `P(χ)(𝔸_F)` in `G(𝔸_F)`: the image of `dm du` under Levi
coordinates. -/
def parabolicImageHaar : Measure (map F P G iP).toMonoidHom.range :=
  ((Measure.haar : Measure (AdelicGroupPoints F M)).prod
    (Measure.haar : Measure (AdelicGroupPoints F U))).map (leviCoordinates F hP hM hU)

/-- The image of `dm du` under Levi coordinates is a left Haar measure. -/
theorem parabolicImageHaar_isHaarMeasure : (parabolicImageHaar F hP hM hU).IsHaarMeasure := by
  have : BorelSpace (map F P G iP).toMonoidHom.range :=
    inferInstanceAs (BorelSpace ((map F P G iP).toMonoidHom.range : Set (AdelicGroupPoints F G)))
  let μM : Measure (AdelicGroupPoints F M) := Measure.haar
  let μU : Measure (AdelicGroupPoints F U) := Measure.haar
  let e := leviCoordinates F hP hM hU
  have he : Measurable (e : AdelicGroupPoints F M × AdelicGroupPoints F U →
      (map F P G iP).toMonoidHom.range) := e.continuous.measurable
  have : IsFiniteMeasureOnCompacts ((μM.prod μU).map e) :=
    Measure.IsFiniteMeasureOnCompacts.map (μM.prod μU) e
  have : Measure.IsOpenPosMeasure ((μM.prod μU).map e) :=
    e.continuous.isOpenPosMeasure_map e.surjective
  show ((μM.prod μU).map e).IsHaarMeasure
  refine { map_mul_left_eq_self := fun q => ?_ }
  have hc : Continuous (fun x : AdelicGroupPoints F M × AdelicGroupPoints F U =>
      leviCorrection F hP hM hU q x.1 * x.2) :=
    ((continuous_leviCorrection F hP hM hU q).comp continuous_fst).mul continuous_snd
  have ht : MeasurePreserving (fun x : AdelicGroupPoints F M × AdelicGroupPoints F U =>
      (leviProjection F hP hM q * x.1, leviCorrection F hP hM hU q x.1 * x.2))
      (μM.prod μU) (μM.prod μU) :=
    (measurePreserving_mul_left μM (leviProjection F hP hM q)).skew_product
      (g := fun m u => leviCorrection F hP hM hU q m * u) hc.measurable
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μU (leviCorrection F hP hM hU q m)).map_eq)
  have hm : Measurable (fun q' : (map F P G iP).toMonoidHom.range => q * q') :=
    (continuous_const.mul continuous_id).measurable
  change Measure.map (q * ·) ((μM.prod μU).map e) = (μM.prod μU).map e
  rw [Measure.map_map hm he]
  have heq : (fun q' => q * q') ∘ e = e ∘ (fun x : AdelicGroupPoints F M × AdelicGroupPoints F U =>
      (leviProjection F hP hM q * x.1, leviCorrection F hP hM hU q x.1 * x.2)) := by
    funext x
    apply e.symm.injective
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    exact leviSplit_mul_leviMul F hP hM hU q x
  rw [heq, ← Measure.map_map he ht.measurable, ht.map_eq]

/-- Integration against `parabolicImageHaar` of a right translate of `f ∈ C_c(G(𝔸_F))`, in the
coordinates `p = u m` with the factor `δ_P(m)⁻¹`. -/
theorem integral_parabolicImageHaar [LocallyOfFiniteType G.X.hom]
    (f : C_c(AdelicGroupPoints F G, ℂ)) (k : AdelicGroupPoints F G) :
    ∫ q, f ((q : AdelicGroupPoints F G) * k) ∂(parabolicImageHaar F hP hM hU) =
      ∫ m, ∫ u,
        ((parabolicModulus F hP hU
            (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
          f (map F U G iU u * map F M G iM m * k)
        ∂(Measure.haar : Measure (AdelicGroupPoints F U))
        ∂(Measure.haar : Measure (AdelicGroupPoints F M)) := by
  have hQ : IsClosed ((map F P G iP).toMonoidHom.range : Set (AdelicGroupPoints F G)) :=
    isClosed_range_map_of_isClosedSubgroup F iP
      (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP)
  have : BorelSpace (map F P G iP).toMonoidHom.range :=
    inferInstanceAs (BorelSpace ((map F P G iP).toMonoidHom.range : Set (AdelicGroupPoints F G)))
  let e := leviCoordinates F hP hM hU
  have hg : IsClosedEmbedding (fun x : AdelicGroupPoints F M × AdelicGroupPoints F U =>
      ((e x : (map F P G iP).toMonoidHom.range) : AdelicGroupPoints F G) * k) :=
    (Homeomorph.mulRight k).isClosedEmbedding.comp
      (hQ.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding)
  have hint : Integrable (fun x : AdelicGroupPoints F M × AdelicGroupPoints F U =>
      f (((e x : (map F P G iP).toMonoidHom.range) : AdelicGroupPoints F G) * k))
      ((Measure.haar : Measure (AdelicGroupPoints F M)).prod
        (Measure.haar : Measure (AdelicGroupPoints F U))) :=
    ((map_continuous f).comp hg.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_isClosedEmbedding hg)
  have hc : Continuous (fun q : (map F P G iP).toMonoidHom.range =>
      f ((q : AdelicGroupPoints F G) * k)) :=
    (map_continuous f).comp (continuous_subtype_val.mul continuous_const)
  rw [parabolicImageHaar, integral_map e.continuous.measurable.aemeasurable
    hc.aestronglyMeasurable, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  rw [integral_smul]
  change ∫ u, f (map F M G iM m * map F U G iU u * k) ∂(Measure.haar) = _
  have h := integral_conj_parabolicModulus F hP hU
    (map F M P (Dynamic.centralizerToParabolic hP hM) m⁻¹)
    (Measure.haar : Measure (AdelicGroupPoints F U)) (fun x => f (x * map F M G iM m * k))
  simp only [map_inv, map_centralizerToParabolic, inv_inv, inv_mul_cancel_right] at h
  rw [h]
  simp [NNReal.smul_def]

/-- **Iwasawa integration formula**, under the instances that the published statement installs. -/
theorem adelicIwasawaIntegration_of_isRepresentedBy [LocallyOfFiniteType G.X.hom]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
    (hPK : Set.range (map F P G iP) * (K : Set (AdelicGroupPoints F G)) = Set.univ) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : C_c(AdelicGroupPoints F G, ℂ),
      ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        (c : ℝ) • ∫ k, ∫ m, ∫ u,
          ((parabolicModulus F hP hU
              (map F M P (Dynamic.centralizerToParabolic hP hM) m) : ℝ≥0) : ℝ)⁻¹ •
            f (map F U G iU u * map F M G iM m * (k : AdelicGroupPoints F G))
          ∂(Measure.haar : Measure (AdelicGroupPoints F U))
          ∂(Measure.haar : Measure (AdelicGroupPoints F M))
          ∂(compactHaarProbability F G K hK) := by
  set Q := (map F P G iP).toMonoidHom.range with hQdef
  have hQ : IsClosed (Q : Set (AdelicGroupPoints F G)) :=
    isClosed_range_map_of_isClosedSubgroup F iP
      (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP)
  have hQK : ∀ g : AdelicGroupPoints F G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k := by
    intro g
    have hg : g ∈ Set.range (map F P G iP) * (K : Set (AdelicGroupPoints F G)) := by
      rw [hPK]; exact Set.mem_univ g
    obtain ⟨a, ⟨p, rfl⟩, k, hk, h⟩ := hg
    exact ⟨_, ⟨p, rfl⟩, k, hk, h.symm⟩
  have := parabolicImageHaar_isHaarMeasure F hP hM hU
  have : SFinite (parabolicImageHaar F hP hM hU) := by
    unfold parabolicImageHaar
    infer_instance
  obtain ⟨c, hc, hμ⟩ := CompactFactorization.exists_pos_eq_smul_map_mul_prod
    (Measure.haar : Measure (AdelicGroupPoints F G)) Q hQ K hK hQK
    (parabolicImageHaar F hP hM hU) (compactHaarProbability F G K hK)
  refine ⟨c, hc, fun f => ?_⟩
  have : BorelSpace Q := inferInstanceAs (BorelSpace (Q : Set (AdelicGroupPoints F G)))
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set (AdelicGroupPoints F G)))
  have : SecondCountableTopology Q :=
    inferInstanceAs (SecondCountableTopology (Q : Set (AdelicGroupPoints F G)))
  have : SecondCountableTopology K :=
    inferInstanceAs (SecondCountableTopology (K : Set (AdelicGroupPoints F G)))
  have hΨ : Continuous (fun p : Q × K => (p.1 : AdelicGroupPoints F G) * p.2) :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfμ : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
  have hfν : Integrable f (Measure.map (fun p : Q × K => (p.1 : AdelicGroupPoints F G) * p.2)
      ((parabolicImageHaar F hP hM hU).prod (compactHaarProbability F G K hK))) := by
    have h1 := hfμ
    rw [hμ] at h1
    have h2 := h1.smul_measure_nnreal (c := c⁻¹)
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h2
  have hint : Integrable (fun p : Q × K => f ((p.1 : AdelicGroupPoints F G) * p.2))
      ((parabolicImageHaar F hP hM hU).prod (compactHaarProbability F G K hK)) :=
    (integrable_map_measure (map_continuous f).aestronglyMeasurable hΨ.measurable.aemeasurable).1 hfν
  rw [hμ, integral_smul_nnreal_measure, integral_map hΨ.measurable.aemeasurable
    (map_continuous f).aestronglyMeasurable, integral_prod_symm _ hint, NNReal.smul_def]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact integral_parabolicImageHaar F hP hM hU f k

end Measure

/-- **Iwasawa integration formula on `G(𝔸_F)`** (Mœglin–Waldspurger I.1.13). -/
theorem adelicIwasawaIntegration : AdelicIwasawaIntegrationStatement.{u} := by
  intro F _ _ G hG χ P M U iP iM iU hP hM hU
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isAffine_parabolic F hP
  have := isAffine_centralizer F hM
  have := locallyOfFiniteType_centralizer F hM
  have := isAffine_unipotent F hU
  have := locallyOfFiniteType_unipotent F hU
  intro K hK hPK
  exact adelicIwasawaIntegration_of_isRepresentedBy F hP hM hU K hK hPK

end Langlands.Global.AdelicGroupPoints
