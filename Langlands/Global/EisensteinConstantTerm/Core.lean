import Langlands.Global.EisensteinConstantTerm.Bruhat
import Langlands.Global.EisensteinConstantTerm.QuotientUnfolding
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingStatement

/-! # The unfolding computation behind the constant-term formula

For a function `Φ` on `G(𝔸)` that is continuous and left `P(F)`-invariant, and whose series
`∑_{γ ∈ P(F) \ G(F)} |Φ(γ v g)|` is bounded on `V(𝔸) g`, the constant term along `V` of
`x ↦ ∑_{γ ∈ P(F) \ G(F)} Φ(γ x)` is computed: the series is decomposed along the double cosets
`Q(F) w_i P(F)`, the constant term is exchanged with the sums, the conjugation by `γ ∈ Q(F)` is
removed by the invariance of the Haar measure of `V(𝔸)`, and the sum over
`(V(F) ∩ w_i P(F) w_i⁻¹) \ V(F)` is unfolded. The resulting integrals over
`(V(F) ∩ w_iP(F)w_i⁻¹) \ V(𝔸)` are left as the input of an abstract identification `hB`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.EisensteinConstantTerm

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]

section Conj

variable {G Q V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] (q : Q ⟶ G)
  (iV : V ⟶ Q)

/-- Conjugation `v ↦ x v x⁻¹` of `V(𝔸)` by a point `x ∈ Q(𝔸)`, for `V` normal in `Q`. -/
def conjAdelic (hN : (SubgroupFunctor.range iV).IsNormal) (x : AdelicGroupPoints F Q) :
    AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) ≃ₜ*
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) where
  toFun v := ⟨map F Q G q x * v * (map F Q G q x)⁻¹, conj_mem_adelicPoints_range q iV hN x v.2⟩
  invFun v := ⟨map F Q G q x⁻¹ * v * (map F Q G q x⁻¹)⁻¹,
    conj_mem_adelicPoints_range q iV hN x⁻¹ v.2⟩
  left_inv v := Subtype.ext (by simp [map_inv, mul_assoc])
  right_inv v := Subtype.ext (by simp [map_inv, mul_assoc])
  map_mul' a b := Subtype.ext (by
    change map F Q G q x * ((a : AdelicGroupPoints F G) * b) * (map F Q G q x)⁻¹ =
      map F Q G q x * a * (map F Q G q x)⁻¹ * (map F Q G q x * b * (map F Q G q x)⁻¹)
    group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem conjAdelic_coe (hN : (SubgroupFunctor.range iV).IsNormal) (x : AdelicGroupPoints F Q)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
    ((conjAdelic q iV hN x v : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) =
      map F Q G q x * v * (map F Q G q x)⁻¹ := rfl

/-- Conjugation by a rational point of `Q` preserves `V(F)`. -/
theorem conjAdelic_mem_rationalSubgroup_iff (hN : (SubgroupFunctor.range iV).IsNormal)
    (x₀ : RationalGroupPoints F Q)
    (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
    conjAdelic q iV hN (rational F Q x₀) v ∈
        AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)) ↔
      v ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)) := by
  rw [mem_rationalSubgroup_range_iff, mem_rationalSubgroup_range_iff, conjAdelic_coe]
  have hx : map F Q G q (rational F Q x₀) ∈ rationalImage F q := ⟨x₀, rfl⟩
  constructor
  · intro h
    have := conj_mem_rationalImage q iV hN ((rationalImage F q).inv_mem hx) h
    simpa [mul_assoc] using this
  · intro h
    exact conj_mem_rationalImage q iV hN hx h

end Conj

section Setup

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : SubgroupFunctor G)
  [hU : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))]

/-- A closed adelic subgroup is locally compact. -/
instance instLocallyCompactSpaceAdelicPoints :
    LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G U) :=
  hU.locallyCompactSpace

/-- Push-forward identity for the mass-normalized measures: the Library's
`normalizedRationalQuotientHaarMeasure` on `U(F) \ U(𝔸)` is the push-forward of
`normalizedHaarMeasure` restricted to the chosen fundamental domain. Both measures are scaled by
the same factor `quotientMassNormalizer`, the reciprocal of the total Haar mass of `U(F) \ U(𝔸)`.
No finiteness is assumed; the quotient measure is a probability measure only when that mass is
finite, for instance when `U(F) \ U(𝔸)` is compact. -/
theorem normalizedRationalQuotientHaarMeasure_eq_quotientMeasure :
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U =
      LeftCosetSpace.quotientMeasure (AdelicSubgroupPoints.rationalSubgroup F G U)
        (AdelicSubgroupPoints.normalizedHaarMeasure F G U)
        (LeftCosetSpace.fundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F G U)
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U)) := by
  rw [AdelicSubgroupPoints.normalizedHaarMeasure, LeftCosetSpace.quotientMeasure_smul]
  rfl

theorem haar_fundamentalDomain_eq :
    (Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G U))
        (LeftCosetSpace.fundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F G U)
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U)) =
      AdelicSubgroupPoints.rationalQuotientHaarMeasure F G U univ := by
  rw [AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure_univ]

theorem haar_fundamentalDomain_ne_zero :
    (Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G U))
        (LeftCosetSpace.fundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F G U)
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U)) ≠ 0 := by
  rw [haar_fundamentalDomain_eq]
  exact Measure.measure_univ_ne_zero.mpr
    (AdelicSubgroupPoints.rationalQuotientHaarMeasure_ne_zero F G U)

theorem haar_fundamentalDomain_ne_top
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)] :
    (Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G U))
        (LeftCosetSpace.fundamentalDomain (AdelicSubgroupPoints.rationalSubgroup F G U)
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U)) ≠ ∞ := by
  rw [haar_fundamentalDomain_eq]
  let := AdelicSubgroupPoints.rationalQuotientHaarMeasure_isFiniteMeasure F G U
  exact measure_ne_top _ _

omit hU in
theorem countable_rationalSubgroup :
    Countable (AdelicSubgroupPoints.rationalSubgroup F G U) :=
  LeftCosetSpace.countable_of_isDiscrete _ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U)

end Setup


section Unfold

variable {G P Q V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine V.X.left] {p : P ⟶ G} {q : Q ⟶ G} {iV : V ⟶ Q}
  [IsClosedImmersion (iV ≫ q).hom.hom.left]

instance instIsClosedAdelicPointsRange :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) :
      Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)

theorem normalizedHaarMeasure_isMulLeftInvariant (U : SubgroupFunctor G)
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))] :
    (AdelicSubgroupPoints.normalizedHaarMeasure F G U).IsMulLeftInvariant := by
  unfold AdelicSubgroupPoints.normalizedHaarMeasure
  infer_instance

/-- Removing the conjugation by `gq = q(x₀) ∈ Q(F)` and unfolding the sum over representatives
`ρ'` of `(V(F) ∩ wP(F)w⁻¹) \ V(F)`: lower integrals, and integrals under finiteness. -/
theorem unfold_conj (hN : (SubgroupFunctor.range iV).IsNormal)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iV ≫ q)))]
    (wv : AdelicGroupPoints F G) (x₀ : RationalGroupPoints F Q) (gq : AdelicGroupPoints F G)
    (hgq : map F Q G q (rational F Q x₀) = gq) {Jν : Type*} [Countable Jν]
    (ρ' : Jν → AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
    (hρΓ : ∀ ν, ρ' ν ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
    (hρ : ∀ δ ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)),
      ∃! ν, δ * (ρ' ν)⁻¹ ∈ stabilizerRationalSubgroup F p (iV ≫ q) wv)
    {Φ : AdelicGroupPoints F G → ℂ} (hΦc : Continuous Φ)
    (hΦP : ∀ z ∈ rationalImage F p, ∀ x, Φ (z * x) = Φ x) (g : AdelicGroupPoints F G) :
    (∫⁻ x, ‖Φ (wv⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * (gq * g))‖ₑ
        ∂stabilizerMeasure F p (iV ≫ q) wv =
      ∫⁻ v in LeftCosetSpace.fundamentalDomain
          (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _),
        ∑' ν, ‖Φ (wv⁻¹ * (ρ' ν : AdelicGroupPoints F G) * gq * ((v : AdelicGroupPoints F G) * g))‖ₑ
        ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) ∧
    ((∫⁻ v in LeftCosetSpace.fundamentalDomain
          (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
          (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _),
        ∑' ν, ‖Φ (wv⁻¹ * (ρ' ν : AdelicGroupPoints F G) * gq * ((v : AdelicGroupPoints F G) * g))‖ₑ
        ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) ≠ ∞ →
      ∫ x, Φ (wv⁻¹ * ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * (gq * g))
          ∂stabilizerMeasure F p (iV ≫ q) wv =
        ∫ v in LeftCosetSpace.fundamentalDomain
            (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)))
            (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _),
          ∑' ν, Φ (wv⁻¹ * (ρ' ν : AdelicGroupPoints F G) * gq * ((v : AdelicGroupPoints F G) * g))
          ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))) := by
  classical
  set Γ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)) with hΓdef
  have hΓ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q))
  have : Countable Γ := countable_rationalSubgroup _
  set mV := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))
    with hmVdef
  have : mV.IsMulLeftInvariant := normalizedHaarMeasure_isMulLeftInvariant _
  set s := LeftCosetSpace.fundamentalDomain Γ hΓ with hsdef
  have hsm : MeasurableSet s := LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ
  have hs := LeftCosetSpace.fundamentalDomain_unique Γ hΓ
  set α := conjAdelic q iV hN (rational F Q x₀) with hαdef
  have hα : ∀ v, α v ∈ Γ ↔ v ∈ Γ := conjAdelic_mem_rationalSubgroup_iff q iV hN x₀
  have hαs : ∀ v, α.symm v ∈ Γ ↔ v ∈ Γ := fun v => by rw [← hα, α.apply_symm_apply]
  set t := α.symm ⁻¹' s with htdef
  have htm : MeasurableSet t := α.symm.continuous.measurable hsm
  have ht : ∀ x, ∃! δ : Γ, (δ : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q))) * x ∈ t :=
    existsUnique_mem_preimage Γ hs α.symm.toMulEquiv hαs
  have hmp : MeasurePreserving α mV mV :=
    measurePreserving_of_preserves Γ hsm hs α hα Measure.haar
      (haar_fundamentalDomain_ne_zero _) (haar_fundamentalDomain_ne_top _) _
  have hemb : MeasurableEmbedding α := α.toHomeomorph.measurableEmbedding
  have hpre : α ⁻¹' t = s := by
    ext v
    simp [t]
  set f : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) → ℂ :=
    fun v => Φ (wv⁻¹ * (v : AdelicGroupPoints F G) * (gq * g)) with hfdef
  have hfm : Measurable f :=
    (hΦc.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)).measurable
  have hf : ∀ (l : stabilizerRationalSubgroup F p (iV ≫ q) wv)
      (x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))),
      f ((l : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) * x) =
        f x := by
    intro l x
    have hl := (mem_stabilizerRationalSubgroup_iff F p (iV ≫ q) wv l).mp l.2
    have : wv⁻¹ * (((l : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q))) * x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * (gq * g) =
        (wv⁻¹ * ((l : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * wv) *
          (wv⁻¹ * (x : AdelicGroupPoints F G) * (gq * g)) := by
      simp only [Subgroup.coe_mul]
      group
    simp only [f]
    rw [this, hΦP _ hl.2]
  have hkey : ∀ v ν, f (ρ' ν * α v) =
      Φ (wv⁻¹ * (ρ' ν : AdelicGroupPoints F G) * gq * ((v : AdelicGroupPoints F G) * g)) := by
    intro v ν
    simp only [f]
    congr 1
    rw [Subgroup.coe_mul, hαdef, conjAdelic_coe, hgq]
    group
  have hfd := isFundamentalDomain_iUnion_smul
    (Λ := stabilizerRationalSubgroup F p (iV ≫ q) wv) inf_le_left htm ht ρ' hρΓ hρ mV
  have hstab : stabilizerMeasure F p (iV ≫ q) wv =
      LeftCosetSpace.quotientMeasure _ mV (⋃ ν, ρ' ν • t) :=
    LeftCosetSpace.discreteQuotientMeasure_eq _ _ mV hfd
  have hL : ∫⁻ v in t, ∑' ν, ‖f (ρ' ν * v)‖ₑ ∂mV =
      ∫⁻ v in s, ∑' ν, ‖Φ (wv⁻¹ * (ρ' ν : AdelicGroupPoints F G) * gq *
        ((v : AdelicGroupPoints F G) * g))‖ₑ ∂mV := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb, hpre]
    congr 1
    funext v
    exact tsum_congr fun ν => by rw [hkey]
  refine ⟨?_, fun hfin => ?_⟩
  · rw [hstab]
    change ∫⁻ x, ‖f (Quotient.out x)‖ₑ ∂_ = _
    rw [lintegral_unfold mV htm ht ρ' hρΓ hρ hfm hf, hL]
  · rw [hstab]
    change ∫ x, f (Quotient.out x) ∂_ = _
    obtain ⟨-, -, heq⟩ := integral_unfold mV htm ht ρ' hρΓ hρ hfm hf (by rw [hL]; exact hfin)
    rw [heq, ← hmp.setIntegral_preimage_emb hemb, hpre]
    congr 1
    funext v
    exact tsum_congr fun ν => by rw [hkey]

end Unfold

section Main

variable {G P Q V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine V.X.left] {p : P ⟶ G}
  [IsClosedImmersion p.hom.hom.left] {q : Q ⟶ G} {iV : V ⟶ Q}
  [IsClosedImmersion (iV ≫ q).hom.hom.left]

/-- The rational subgroup `G(F)` is countable. -/
theorem countable_rationalSubgroup_ambient : Countable (rationalSubgroup F G) :=
  LeftCosetSpace.countable_of_isDiscrete _ (AdelicGroupPoints.isDiscrete_rationalSubgroup F G)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- **The constant-term computation.** For `Φ` continuous and left `P(F)`-invariant whose
series of absolute values is bounded on `V(𝔸) g`, and an identification `hB` of the unfolded
integrals over `(V(F) ∩ w_iP(F)w_i⁻¹) \ V(𝔸)` with given numbers `R i y` (with side conditions
`Int i y`), the constant term along `V` of `x ↦ ∑_{γ ∈ P(F) \ G(F)} Φ(γ x)` at `g` is
`∑_i ∑_{c ∈ Q'_i \ Q(F)} R i (γ_c g)`, every `Int i (γ_c g)` holds and the inner sums are
summable. -/
theorem constantTerm_series_eq {I : Type*} [Fintype I]
    {w : I → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)}
    (hw : IsDoubleCosetRepresentatives F q p w)
    (Q' : I → Subgroup (AdelicGroupPoints F G))
    (hQ' : ∀ i, Q' i = (rationalImage F q ⊓ (rationalImage F p).map
      (MulAut.conj (innerAdelicPoint F G (w i))).toMonoidHom) ⊔ rationalImage F (iV ≫ q))
    (hN : (SubgroupFunctor.range iV).IsNormal)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (iV ≫ q)))]
    {Φ : AdelicGroupPoints F G → ℂ} (hΦc : Continuous Φ)
    (hΦP : ∀ z ∈ rationalImage F p, ∀ x, Φ (z * x) = Φ x)
    (g : AdelicGroupPoints F G) (B₀ : ℝ≥0∞) (hB₀ : B₀ ≠ ∞)
    (hS : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
      ∑' c : ParabolicRationalCosets F p,
        ‖Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g))‖ₑ ≤ B₀)
    (R : I → AdelicGroupPoints F G → ℂ) (Int : I → AdelicGroupPoints F G → Prop)
    (hB : ∀ i y, ∫⁻ x, ‖Φ ((innerAdelicPoint F G (w i))⁻¹ *
        ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)‖ₑ
        ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G (w i)) < ∞ →
      Int i y ∧ R i y = ∫ x, Φ ((innerAdelicPoint F G (w i))⁻¹ *
        ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * y)
        ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G (w i))) :
    (∀ i (c : OuterCosets (rationalImage F q) (Q' i)),
      Int i (((c.out : rationalImage F q) : AdelicGroupPoints F G) * g)) ∧
    (∀ i, Summable fun c : OuterCosets (rationalImage F q) (Q' i) =>
      R i (((c.out : rationalImage F q) : AdelicGroupPoints F G) * g)) ∧
    subgroupConstantTerm F (iV ≫ q) (fun x => ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)) g =
      ∑ i, ∑' c : OuterCosets (rationalImage F q) (Q' i),
        R i (((c.out : rationalImage F q) : AdelicGroupPoints F G) * g) := by
  classical
  -- the subgroups of `G(𝔸)`
  set Gr := rationalSubgroup F G with hGr
  set Pm := (rationalSubgroup F P).map (map F P G p).toMonoidHom with hPmdef
  have hPm : rationalImage F p = Pm := rationalImage_eq_map p
  set Qr := rationalImage F q with hQr
  set Vr := rationalImage F (iV ≫ q) with hVr
  set wv : I → AdelicGroupPoints F G := fun i => innerAdelicPoint F G (w i) with hwv
  have hBD : BruhatData Gr Pm Qr Vr wv :=
    { P_le := hPm ▸ rationalImage_le_rationalSubgroup p
      Q_le := rationalImage_le_rationalSubgroup q
      V_le := rationalImage_comp_le iV q
      w_mem := fun i => ⟨_, (innerAdelicPoint_eq_rational F G (w i)).symm⟩
      normal := fun _ hg _ hv => conj_mem_rationalImage q iV hN hg hv
      unique := fun z hz => by rw [← hPm]; exact hw z hz }
  have hQ'm : ∀ i, Q' i = (Qr ⊓ Pm.map (MulAut.conj (wv i)).toMonoidHom) ⊔ Vr := by
    intro i
    rw [hQ' i, hPm]
  have hΦPm : ∀ z ∈ Pm, ∀ x, Φ (z * x) = Φ x := by
    rw [← hPm]
    exact hΦP
  have hnPm : ∀ z ∈ Pm, ∀ x, ‖Φ (z * x)‖ₑ = ‖Φ x‖ₑ := fun z hz x => by rw [hΦPm z hz x]
  -- countability
  have : Countable Gr := countable_rationalSubgroup_ambient
  have hVG : Vr ≤ Gr := hBD.V_le.trans hBD.Q_le
  have : Countable Vr := (Subgroup.inclusion_injective hVG).countable
  have : Countable Qr := (Subgroup.inclusion_injective hBD.Q_le).countable
  -- the group `V(𝔸)`, its rational points, a fundamental domain and the normalized Haar measure
  set Γ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)) with hΓdef
  have hΓ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q))
  have : Countable Γ := countable_rationalSubgroup _
  set mV := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iV ≫ q))
    with hmVdef
  set s := LeftCosetSpace.fundamentalDomain Γ hΓ with hsdef
  have hsm : MeasurableSet s := LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ
  have hmVs : mV s ≠ ∞ := by
    rw [hmVdef, AdelicSubgroupPoints.normalizedHaarMeasure, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G _)
      (haar_fundamentalDomain_ne_top _)
  -- representatives of the inner cosets `Δ_i \ V(F)`, inside `V(𝔸)`
  let ρ' : ∀ i, InnerCosets Pm Vr (wv i) →
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) :=
    fun i ν => ⟨((ν.out : Vr) : AdelicGroupPoints F G),
      rationalImage_le_adelicPoints (iV ≫ q) (ν.out).2⟩
  have hρΓ : ∀ i ν, ρ' i ν ∈ Γ := fun i ν =>
    (mem_rationalSubgroup_range_iff (iV ≫ q) _).mpr (ν.out).2
  have htr : ∀ i (x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))),
      x ∈ stabilizerRationalSubgroup F p (iV ≫ q) (wv i) ↔
        (x : AdelicGroupPoints F G) ∈ bruhatStabilizer Pm Vr (wv i) := by
    intro i x
    rw [mem_stabilizerRationalSubgroup_iff, mem_bruhatStabilizer_iff,
      mem_rationalSubgroup_range_iff, hPm]
  have hρ : ∀ i, ∀ δ ∈ Γ, ∃! ν, δ * (ρ' i ν)⁻¹ ∈ stabilizerRationalSubgroup F p (iV ≫ q) (wv i) := by
    intro i δ hδ
    have hδV : (δ : AdelicGroupPoints F G) ∈ Vr := (mem_rationalSubgroup_range_iff _ δ).mp hδ
    obtain ⟨ν, hν, huniq⟩ := RankinSelbergGlobal.Unfolding.existsUnique_cosetRep
      (bruhatStabilizer Pm Vr (wv i)) Vr (δ : AdelicGroupPoints F G) hδV
    refine ⟨ν, (htr i _).mpr hν, fun ν' h' => huniq ν' ((htr i _).mp h')⟩
  -- the point `γ_c` and a rational preimage
  let gq : OuterIndex Qr Q' → AdelicGroupPoints F G := fun j => ((j.2.out : Qr) : AdelicGroupPoints F G)
  have hx₀ : ∀ j, ∃ x₀ : RationalGroupPoints F Q, map F Q G q (rational F Q x₀) = gq j :=
    fun j => (j.2.out).2
  -- the unfolded functions
  let Lfun : OuterIndex Qr Q' →
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) → ℝ≥0∞ :=
    fun j v => ∑' ν, ‖Φ ((wv j.1)⁻¹ * (ρ' j.1 ν : AdelicGroupPoints F G) * gq j *
      ((v : AdelicGroupPoints F G) * g))‖ₑ
  let Gfun : OuterIndex Qr Q' →
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) → ℂ :=
    fun j v => ∑' ν, Φ ((wv j.1)⁻¹ * (ρ' j.1 ν : AdelicGroupPoints F G) * gq j *
      ((v : AdelicGroupPoints F G) * g))
  have hterm_cont : ∀ (j : OuterIndex Qr Q') (ν : InnerCosets Pm Vr (wv j.1)),
      Continuous fun v : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (iV ≫ q)) =>
        Φ ((wv j.1)⁻¹ * (ρ' j.1 ν : AdelicGroupPoints F G) * gq j *
          ((v : AdelicGroupPoints F G) * g)) := fun j ν =>
    hΦc.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hLm : ∀ j, Measurable (Lfun j) := fun j =>
    Measurable.tsum fun ν => (hterm_cont j ν).measurable.enorm
  have hGm : ∀ j, Measurable (Gfun j) := fun j =>
    Measurable.tsum fun ν => (hterm_cont j ν).measurable
  have hUC := fun j : OuterIndex Qr Q' => unfold_conj hN (wv j.1) (hx₀ j).choose (gq j)
    (hx₀ j).choose_spec (ρ' j.1) (hρΓ j.1) (hρ j.1) hΦc hΦP g
  -- decomposition of the series of absolute values
  have hdecL : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
      ∑' c : ParabolicRationalCosets F p,
        ‖Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g))‖ₑ = ∑' j, Lfun j v := by
    intro v
    have h := tsum_out_eq_tsum_bruhat hBD Q' hQ'm (g := fun z => ‖Φ z‖ₑ) hnPm
      ((v : AdelicGroupPoints F G) * g)
    exact h.trans (ENNReal.tsum_sigma' _)
  have hLsum_le : ∀ v, ∑' j, Lfun j v ≤ B₀ := fun v => (hdecL v).symm ▸ hS v
  -- the lower integrals
  have hLint : ∑' j, ∫⁻ v in s, Lfun j v ∂mV ≤ B₀ * mV s := by
    rw [← lintegral_tsum fun j => (hLm j).aemeasurable]
    calc ∫⁻ v in s, ∑' j, Lfun j v ∂mV ≤ ∫⁻ _ in s, B₀ ∂mV := lintegral_mono hLsum_le
      _ = B₀ * mV s := setLIntegral_const s B₀
  have hLfin : ∑' j, ∫⁻ v in s, Lfun j v ∂mV ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hB₀ hmVs) hLint
  have hLj : ∀ j, ∫⁻ v in s, Lfun j v ∂mV ≠ ∞ := fun j =>
    ne_top_of_le_ne_top hLfin (ENNReal.le_tsum (f := fun j => ∫⁻ v in s, Lfun j v ∂mV) j)
  -- the identification
  have hBj : ∀ j : OuterIndex Qr Q', Int j.1 (gq j * g) ∧
      R j.1 (gq j * g) = ∫ v in s, Gfun j v ∂mV := by
    intro j
    obtain ⟨hlow, hint⟩ := hUC j
    have hfin : ∫⁻ x, ‖Φ ((innerAdelicPoint F G (w j.1))⁻¹ *
        ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) * (gq j * g))‖ₑ
        ∂stabilizerMeasure F p (iV ≫ q) (innerAdelicPoint F G (w j.1)) < ∞ := by
      rw [hlow]
      exact (hLj j).lt_top
    obtain ⟨hI, hR⟩ := hB j.1 (gq j * g) hfin
    exact ⟨hI, hR.trans (hint (hLj j))⟩
  have hnorm : ∀ j : OuterIndex Qr Q', ‖R j.1 (gq j * g)‖ₑ ≤ ∫⁻ v in s, Lfun j v ∂mV := by
    intro j
    rw [(hBj j).2]
    exact (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono fun v => enorm_tsum_le_tsum_enorm)
  have hsumm : Summable fun j : OuterIndex Qr Q' => R j.1 (gq j * g) := by
    have h1 : ∑' j : OuterIndex Qr Q', ‖R j.1 (gq j * g)‖ₑ ≠ ∞ :=
      ne_top_of_le_ne_top hLfin (ENNReal.tsum_le_tsum hnorm)
    have h2 : Summable fun j : OuterIndex Qr Q' => ‖R j.1 (gq j * g)‖₊ := by
      apply ENNReal.tsum_coe_ne_top_iff_summable.mp
      simpa [enorm_eq_nnnorm] using h1
    exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h2)
  refine ⟨fun i c => (hBj ⟨i, c⟩).1, fun i => hsumm.sigma_factor i, ?_⟩
  -- the constant term
  have hEm : Measurable fun v : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q)) => ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g)) :=
    Measurable.tsum fun c =>
      (hΦc.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const))).measurable
  have hEinv : ∀ (δ : Γ) (v : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (iV ≫ q))),
      ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((((δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) * v :
            AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
              AdelicGroupPoints F G) * g)) =
      ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g)) := by
    intro δ v
    have hδ : ((δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
        AdelicGroupPoints F G) ∈ Gr :=
      hVG ((mem_rationalSubgroup_range_iff _ _).mp δ.2)
    have h := tsum_out_mul_left (P := Pm) hΦPm hδ ((v : AdelicGroupPoints F G) * g)
    rw [show (((δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) * v :
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
          AdelicGroupPoints F G) * g = ((δ : AdelicSubgroupPoints.adelicPoints F G
            (SubgroupFunctor.range (iV ≫ q))) : AdelicGroupPoints F G) *
              ((v : AdelicGroupPoints F G) * g) by simp [mul_assoc]]
    exact h
  have hdec : ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
      ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g)) = ∑' j, Gfun j v := by
    intro v
    have h := tsum_out_eq_tsum_bruhat hBD Q' hQ'm (g := Φ) hΦPm ((v : AdelicGroupPoints F G) * g)
    have hL := tsum_out_eq_tsum_bruhat hBD Q' hQ'm (g := fun z => ‖Φ z‖ₑ) hnPm
      ((v : AdelicGroupPoints F G) * g)
    have hfin : ∑' t : BruhatIndex Pm Qr Vr Q' wv,
        ‖Φ (bruhatPoint Q' t * ((v : AdelicGroupPoints F G) * g))‖ₑ ≠ ∞ := by
      rw [← hL]
      exact ne_top_of_le_ne_top hB₀ (hS v)
    have hsum : Summable fun t : BruhatIndex Pm Qr Vr Q' wv =>
        Φ (bruhatPoint Q' t * ((v : AdelicGroupPoints F G) * g)) := by
      have h2 : Summable fun t : BruhatIndex Pm Qr Vr Q' wv =>
          ‖Φ (bruhatPoint Q' t * ((v : AdelicGroupPoints F G) * g))‖₊ := by
        apply ENNReal.tsum_coe_ne_top_iff_summable.mp
        simpa [enorm_eq_nnnorm] using hfin
      exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h2)
    exact h.trans hsum.tsum_sigma
  -- assemble
  have hLHS : subgroupConstantTerm F (iV ≫ q) (fun x => ∑' c : ParabolicRationalCosets F p,
      Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)) g =
      ∫ v in s, ∑' c : ParabolicRationalCosets F p,
        Φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) *
          ((v : AdelicGroupPoints F G) * g)) ∂mV := by
    unfold subgroupConstantTerm
    rw [normalizedRationalQuotientHaarMeasure_eq_quotientMeasure]
    exact RankinSelbergGlobal.Unfolding.integral_out_eq Γ hEm hEinv mV s
  rw [hLHS, setIntegral_congr_fun hsm (fun v _ => hdec v)]
  rw [integral_tsum (fun j => (hGm j).aestronglyMeasurable)
    (ne_top_of_le_ne_top hLfin (ENNReal.tsum_le_tsum fun j =>
      lintegral_mono fun v => enorm_tsum_le_tsum_enorm))]
  rw [← tsum_congr fun j => (hBj j).2, hsumm.tsum_sigma, tsum_fintype]

end Main

end Langlands.Global.EisensteinConstantTerm
