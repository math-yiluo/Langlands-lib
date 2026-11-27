import Langlands.Global.CuspidalTestExpansion.CosetTransfer
import Langlands.Global.AdelicProperEisensteinTestVanishing
import Langlands.Global.AdelicStandardNestedLeviParabolic
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicEisensteinBruhatAbsoluteBound
import Langlands.GroupScheme.Rational.NestedParabolicContainment

/-! # Pieces of the constant term with a proper target parabolic have zero cuspidal tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily.NestedLeviParabolic

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {J₁ J : StandardIndex F G fam.i fam.ν}
  (t : NestedLeviParabolic fam J₁ J)

local notation "ι" => map F (fam.M J) G (fam.l J ≫ fam.p J)

omit [NumberField F] in
theorem section_projection_hom :
    (fam.l J).hom.hom ≫ t.projection.hom.hom = 𝟙 _ := by
  rw [← Grp.comp_hom_hom, t.section_projection, Grp.id_hom_hom]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rational_comp (H H' : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ H')
    (x : RationalGroupPoints F H) :
    rational F H x ≫ f.hom.hom = rational F H' (x ≫ f.hom.hom) := by
  simp only [rational, GroupScheme.affinePointMap_apply, Category.assoc]

/-- A rational point of the Levi `M_J` lies in the rational points of the smaller standard
parabolic `P_{J₁}` exactly when it lies in the rational points of the inner parabolic of `M_J`. -/
theorem leviRational_mem_iff (q : RationalGroupPoints F (fam.M J)) :
    ι (rational F (fam.M J) q) ∈ rationalImage F (t.inclusion ≫ fam.p J) ↔
      rational F (fam.M J) q ∈ rationalImage F t.p := by
  have hsec := t.section_projection_hom
  constructor
  · rintro ⟨z₁, hz₁⟩
    have : Mono (fam.p J).hom.hom := (fam.isCompatible J).parabolic.isClosedSubgroup.mono_overHom
    change map F _ G (t.inclusion ≫ fam.p J) (rational F _ z₁) = ι (rational F (fam.M J) q) at hz₁
    have h1 : rational F _ z₁ ≫ t.inclusion.hom.hom =
        rational F (fam.M J) q ≫ (fam.l J).hom.hom := by
      apply (cancel_mono (fam.p J).hom.hom).mp
      simpa only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
        Category.assoc] using hz₁
    have h2 : z₁ ≫ t.inclusion.hom.hom ∈ (SubgroupFunctor.range t.inclusion).carrier _ :=
      ⟨z₁, rfl⟩
    rw [t.pullback_eq, SubgroupFunctor.mem_comap] at h2
    obtain ⟨z', hz'⟩ := SubgroupFunctor.mem_range.mp h2
    refine ⟨z', ?_⟩
    change rational F _ z' ≫ t.p.hom.hom = rational F (fam.M J) q
    rw [rational_comp, hz', ← rational_comp, ← rational_comp, h1, Category.assoc, hsec,
      Category.comp_id]
  · rintro ⟨z', hz'⟩
    change rational F _ z' ≫ t.p.hom.hom = rational F (fam.M J) q at hz'
    have h2 : (z' ≫ t.p.hom.hom) ≫ (fam.l J).hom.hom ∈
        (SubgroupFunctor.range t.inclusion).carrier _ := by
      rw [t.pullback_eq, SubgroupFunctor.mem_comap]
      refine SubgroupFunctor.mem_range.mpr ⟨z', ?_⟩
      rw [Category.assoc, Category.assoc, hsec, Category.comp_id]
    obtain ⟨z₁, hz₁⟩ := SubgroupFunctor.mem_range.mp h2
    refine ⟨z₁, ?_⟩
    change rational F _ z₁ ≫ (t.inclusion ≫ fam.p J).hom.hom =
      rational F (fam.M J) q ≫ (fam.l J ≫ fam.p J).hom.hom
    rw [← hz', Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, rational_comp, hz₁,
      ← rational_comp, ← rational_comp]
    simp only [Category.assoc]

/-- Every rational point of `P_J` is a rational point of `P_{J₁}` times a rational point of the
Levi `M_J`. -/
theorem exists_mul_leviRational (b : AdelicGroupPoints F G)
    (hb : b ∈ rationalImage F (fam.p J)) :
    ∃ a ∈ rationalImage F (t.inclusion ≫ fam.p J), ∃ q : RationalGroupPoints F (fam.M J),
      b = a * ι (rational F (fam.M J) q) := by
  have hsec := t.section_projection_hom
  obtain ⟨y, rfl⟩ := hb
  let m : RationalGroupPoints F (fam.M J) :=
    (fam.P J).affinePointsTarget t.projection _ y
  let k : RationalGroupPoints F (fam.P J) :=
    y * ((fam.M J).affinePointsTarget (fam.l J) _ m)⁻¹
  have hm : (fam.M J).affinePointsTarget (fam.l J) _ m ≫ t.projection.hom.hom = m := by
    rw [GroupScheme.affinePointsTarget_apply, Category.assoc, hsec, Category.comp_id]
  have hk : k ∈ (SubgroupFunctor.range t.inclusion).carrier _ := by
    rw [t.pullback_eq, SubgroupFunctor.mem_comap]
    have h1 : k ≫ t.projection.hom.hom = 1 := by
      change (fam.P J).affinePointsTarget t.projection _ k = 1
      simp only [k, map_mul, map_inv]
      change m * ((fam.M J).affinePointsTarget (fam.l J) _ m ≫ t.projection.hom.hom)⁻¹ = 1
      rw [hm, mul_inv_cancel]
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨z₁, hz₁⟩ := SubgroupFunctor.mem_range.mp hk
  refine ⟨_, ⟨z₁, rfl⟩, m, ?_⟩
  change _ = map F _ G (t.inclusion ≫ fam.p J) (rational F _ z₁) * ι (rational F _ m)
  have hy : y = (fam.P J₁).affinePointsTarget t.inclusion _ z₁ *
      (fam.M J).affinePointsTarget (fam.l J) _ m := by
    rw [GroupScheme.affinePointsTarget_apply, hz₁]
    simp only [k, inv_mul_cancel_right]
  change map F _ G (fam.p J) (rational F _ y) = _
  rw [hy, map_mul, map_mul, map_rational_affinePointsTarget t.inclusion (fam.p J),
    map_rational_affinePointsTarget (fam.l J) (fam.p J)]

/-- The adelic points of the radical of the inner parabolic of `M_J` lie in the adelic points of
the radical of `P_{J₁}`. -/
theorem radical_map_mem (u : AdelicGroupPoints F (fam.M J))
    (hu : u ∈ parabolicUnipotentImage F t.p t.iU) :
    ι u ∈ AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (fam.iU J₁ ≫ t.inclusion ≫ fam.p J)) := by
  obtain ⟨y, rfl⟩ := hu
  have h : ι (map F t.U (fam.M J) (t.iU ≫ t.p) y) ∈ AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (t.iU ≫ t.p ≫ fam.l J ≫ fam.p J)) :=
    SubgroupFunctor.mem_range.mpr ⟨y, by simp only [map_apply,
      GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]⟩
  rw [t.inclusion_comp]
  exact t.radical_le _ h


/-- Coset sums over `P_{J₁}(F) \ P_J(F)` of a function left invariant under `P_{J₁}(F)` are coset
sums over `P'(F) \ M_J(F)` for the inner parabolic `P'` of `M_J`. -/
theorem tsum_ambientCosets_eq {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [IsAffine t.P.X.left] [LocallyOfFiniteType t.P.X.hom] [IsClosedImmersion t.p.hom.hom.left]
    (f : AdelicGroupPoints F G → E)
    (hf : ∀ a ∈ rationalImage F (t.inclusion ≫ fam.p J), ∀ y, f (a * y) = f y)
    (y : AdelicGroupPoints F G) :
    ∑' c : EisensteinConstantTerm.AmbientCosets (rationalNormOneSubgroup F (fam.M J))
        (parabolicRationalNormOneSubgroup t.p),
        f (ι ((c.out : rationalNormOneSubgroup F (fam.M J)) : normOneSubgroup F (fam.M J)).val *
          y) =
      ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
        f ((c.out : AdelicGroupPoints F G) * y) := by
  classical
  let φ : rationalNormOneSubgroup F (fam.M J) →* AdelicGroupPoints F G :=
    (ι).toMonoidHom.comp
      ((normOneSubgroup F (fam.M J)).subtype.comp (rationalNormOneSubgroup F (fam.M J)).subtype)
  have hφ : ∀ x : rationalNormOneSubgroup F (fam.M J), ∃ q : RationalGroupPoints F (fam.M J),
      ((x : normOneSubgroup F (fam.M J)) : AdelicGroupPoints F (fam.M J)) =
        rational F (fam.M J) q ∧ φ x = ι (rational F (fam.M J) q) := by
    rintro ⟨_, ⟨q, rfl⟩⟩
    exact ⟨q, rfl, rfl⟩
  have hφB : ∀ x, φ x ∈ rationalImage F (fam.p J) := by
    intro x
    obtain ⟨q, -, hq⟩ := hφ x
    rw [hq]
    exact rationalImage_comp_le (fam.l J) (fam.p J) ⟨q, rfl⟩
  have hpre : ∀ x, φ x ∈ rationalImage F (t.inclusion ≫ fam.p J) ↔
      x ∈ (parabolicRationalNormOneSubgroup t.p).subgroupOf (rationalNormOneSubgroup F (fam.M J)) := by
    intro x
    obtain ⟨q, hxq, hq⟩ := hφ x
    rw [hq, t.leviRational_mem_iff, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨z', hz'⟩
      refine ⟨rationalNormOne F _ z', ⟨z', rfl⟩, Subtype.ext ?_⟩
      change map F t.P (fam.M J) t.p (rational F t.P z') = _
      rw [hxq]
      exact hz'
    · rintro ⟨_, ⟨z', rfl⟩, hz⟩
      refine ⟨z', ?_⟩
      have h : map F t.P (fam.M J) t.p (rational F t.P z') =
          ((x : normOneSubgroup F (fam.M J)) : AdelicGroupPoints F (fam.M J)) :=
        congrArg Subtype.val hz
      rw [hxq] at h
      exact h
  have hsurj : ∀ b ∈ rationalImage F (fam.p J), ∃ a ∈ rationalImage F (t.inclusion ≫ fam.p J),
      ∃ x, b = a * φ x := by
    intro b hb
    obtain ⟨a, ha, q, rfl⟩ := t.exists_mul_leviRational b hb
    exact ⟨a, ha, ⟨rationalNormOne F _ q, ⟨q, rfl⟩⟩, rfl⟩
  exact CosetTransfer.tsum_cosetEquiv φ _ _ _ hφB hpre hsurj f hf y

set_option maxHeartbeats 1600000 in
/-- A Bruhat piece series with proper target parabolic `P_{J₁} ⊊ P_J` has zero pairing with every
cusp form on `M_J`, and the pairing integrand is integrable: the series is a proper parabolic
Eisenstein-type sum on `M_J` for the inner parabolic `P'`, so `properEisensteinTestVanishing`
applies, with the absolute bound obtained from the polynomial bound of the absolute series and the
rapid decay of the cusp form. -/
theorem properPiece_pairing (hlt : J₁ < J) {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (Pint : AdelicGroupPoints F G → ℂ) (hc : Continuous Pint)
    (hrat : IsLeftInvariantUnder F G (rationalImage F (t.inclusion ≫ fam.p J)) Pint)
    (hrad : ∀ u ∈ AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (fam.iU J₁ ≫ t.inclusion ≫ fam.p J)), ∀ y, Pint (u * y) = Pint y)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAbs : ∀ y, ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
      ‖Pint ((c.out : AdelicGroupPoints F G) * y)‖ₑ ≤
        ENNReal.ofReal (C * adelicHeight F G rho y ^ D))
    (ψ : AdelicGroupPoints F (fam.M J) → ℂ) (hψ : fam.IsLeviCuspForm Kinf rho J ψ)
    (B₀ : ℝ) (hdecay : ∀ x : NormOneRationalQuotient F (fam.M J),
      ∃ m : normOneSubgroup F (fam.M J),
        LeftCosetSpace.mk (rationalNormOneSubgroup F (fam.M J)) m = x ∧
          adelicHeight F G rho (ι m.val) ^ D * ‖ψ m.val‖ ≤ B₀)
    (g : AdelicGroupPoints F G) :
    Integrable (fam.leviPairingIntegrand J (fun y =>
        ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
          Pint ((c.out : AdelicGroupPoints F G) * y)) g ψ)
        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      fam.leviPairing J (fun y =>
        ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
          Pint ((c.out : AdelicGroupPoints F G) * y)) g ψ = 0 := by
  classical
  have hJ := fam.isCompatible J
  have hM : IsConnectedReductive (fam.M J) := hJ.levi.isConnectedReductive
  have : Smooth (fam.M J).X.hom := hM.smooth
  have : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
  have : ConnectedSpace (fam.M J).X.left := hM.connectedSpace
  have : IsClosedImmersion t.p.hom.hom.left := t.parabolic.isClosedSubgroup
  have : IsAffine t.P.X.left := isAffine_of_isAffineHom t.p.hom.hom.left
  have : LocallyOfFiniteType t.P.X.hom := by rw [← Over.w t.p.hom.hom]; infer_instance
  have : IsClosedImmersion t.l.hom.hom.left := t.levi.isClosedSubgroup
  have : IsAffine t.M.X.left := isAffine_of_isAffineHom t.l.hom.hom.left
  have : LocallyOfFiniteType t.M.X.hom := by rw [← Over.w t.l.hom.hom]; infer_instance
  have : IsClosedImmersion t.iU.hom.hom.left := t.unipotentRadical.1.isClosedSubgroup
  have : IsAffine t.U.X.left := isAffine_of_isAffineHom t.iU.hom.hom.left
  have : LocallyOfFiniteType t.U.X.hom := by rw [← Over.w t.iU.hom.hom]; infer_instance
  have : IsClosedImmersion (t.iU ≫ t.p).hom.hom.left := by
    rw [Grp.comp_hom_hom, Over.comp_left]; infer_instance
  have hGfin : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F (fam.M J)) :=
    connectedReductiveFiniteVolume F (fam.M J) hM
  have hPfin : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F t.P) :=
    normOneRationalQuotientFiniteVolume F t.P t.parabolic.smooth t.levi.connectedSpace
  have hLfin : IsFiniteMeasure (normOneRationalQuotientHaarMeasure F t.M) :=
    connectedReductiveFiniteVolume F t.M t.levi.isConnectedReductive
  set S : AdelicGroupPoints F G → ℂ := fun y =>
    ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
      Pint ((c.out : AdelicGroupPoints F G) * y) with hS
  let f : AdelicGroupPoints F (fam.M J) → ℂ := fun z => Pint (ι z * g)
  have hfc : Continuous f :=
    hc.comp ((map F (fam.M J) G (fam.l J ≫ fam.p J)).continuous.mul continuous_const)
  have hψc : Continuous ψ := hψ.1.2.1.1
  have hfP : IsLeftInvariantUnder F (fam.M J) (rationalImage F t.p) f := by
    intro z hz0 x
    obtain ⟨z', rfl⟩ := hz0
    have hz : map F t.P (fam.M J) t.p (rational F t.P z') =
        rational F (fam.M J) (t.P.affinePointsTarget t.p _ z') := map_rational t.p z'
    have hmem : ι (map F t.P (fam.M J) t.p (rational F t.P z')) ∈
        rationalImage F (t.inclusion ≫ fam.p J) := by
      rw [hz, t.leviRational_mem_iff, ← hz]
      exact ⟨z', rfl⟩
    change Pint (ι (map F t.P (fam.M J) t.p (rational F t.P z') * x) * g) = Pint (ι x * g)
    rw [map_mul, mul_assoc, hrat _ hmem]
  have hfU : IsLeftInvariantUnder F (fam.M J) (parabolicUnipotentImage F t.p t.iU) f := by
    intro z hz x
    change Pint (ι (z * x) * g) = Pint (ι x * g)
    rw [map_mul, mul_assoc, hrad _ (t.radical_map_mem z hz)]
  have hψG : IsLeftInvariantUnder F (fam.M J) (rationalSubgroup F (fam.M J)) ψ := hψ.1.1
  have hψ0 : subgroupConstantTerm F (t.iU ≫ t.p) ψ = 0 :=
    hψ.2 t.P t.U t.p t.iU t.parabolic t.unipotentRadical (t.proper hlt)
  have hkey (m : normOneSubgroup F (fam.M J)) :
      ∑' c : EisensteinConstantTerm.AmbientCosets (rationalNormOneSubgroup F (fam.M J))
          (parabolicRationalNormOneSubgroup t.p),
        f (((c.out : rationalNormOneSubgroup F (fam.M J)) : normOneSubgroup F (fam.M J)) * m).val =
        S (ι m.val * g) := by
    show _ = ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
      Pint ((c.out : AdelicGroupPoints F G) * (ι m.val * g))
    rw [← t.tsum_ambientCosets_eq Pint hrat]
    refine tsum_congr fun c => ?_
    change Pint (ι (_ * m.val) * g) = _
    rw [map_mul, mul_assoc]
  have hkeyAbs (m : normOneSubgroup F (fam.M J)) :
      ∑' c : EisensteinConstantTerm.AmbientCosets (rationalNormOneSubgroup F (fam.M J))
          (parabolicRationalNormOneSubgroup t.p),
        ‖f (((c.out : rationalNormOneSubgroup F (fam.M J)) : normOneSubgroup F (fam.M J)) *
          m).val‖ₑ =
        ∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
          ‖Pint ((c.out : AdelicGroupPoints F G) * (ι m.val * g))‖ₑ := by
    rw [← t.tsum_ambientCosets_eq (fun z => ‖Pint z‖ₑ)
      (fun a ha y => by simp only [hrat a ha y])]
    refine tsum_congr fun c => ?_
    change ‖Pint (ι (_ * m.val) * g)‖ₑ = _
    rw [map_mul, mul_assoc]
  have hconj (z : ℂ) : ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
  have hHg : 0 ≤ adelicHeight F G rho g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hbound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ q : NormOneRationalQuotient F (fam.M J),
      ∃ m : normOneSubgroup F (fam.M J),
        LeftCosetSpace.mk (rationalNormOneSubgroup F (fam.M J)) m = q ∧
          properEisensteinTestAbsoluteSum t.p f ψ m ≤ B := by
    refine ⟨ENNReal.ofReal (C * adelicHeight F G rho g ^ D * B₀), ENNReal.ofReal_ne_top,
      fun x => ?_⟩
    obtain ⟨m, hm, hmB⟩ := hdecay x
    refine ⟨m, hm, ?_⟩
    unfold properEisensteinTestAbsoluteSum
    simp_rw [enorm_mul, hconj]
    rw [ENNReal.tsum_mul_right, hkeyAbs m]
    have hHm : 0 ≤ adelicHeight F G rho (ι m.val) :=
      zero_le_one.trans (one_le_adelicHeight F G rho hN _)
    have hHmg : 0 ≤ adelicHeight F G rho (ι m.val * g) :=
      zero_le_one.trans (one_le_adelicHeight F G rho hN _)
    have h1 : adelicHeight F G rho (ι m.val * g) ^ D ≤
        adelicHeight F G rho (ι m.val) ^ D * adelicHeight F G rho g ^ D := by
      rw [← Real.mul_rpow hHm hHg]
      exact Real.rpow_le_rpow hHmg (adelicHeight_mul_le F G rho hN _ _) hD
    calc (∑' c : RelativeRationalCosets F (t.inclusion ≫ fam.p J) (fam.p J),
          ‖Pint ((c.out : AdelicGroupPoints F G) * (ι m.val * g))‖ₑ) * ‖ψ m.val‖ₑ
        ≤ ENNReal.ofReal (C * adelicHeight F G rho (ι m.val * g) ^ D) *
            ENNReal.ofReal ‖ψ m.val‖ := by
          rw [ofReal_norm]
          gcongr
          exact hAbs _
      _ = ENNReal.ofReal (C * adelicHeight F G rho (ι m.val * g) ^ D * ‖ψ m.val‖) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hHmg _))]
      _ ≤ ENNReal.ofReal (C * adelicHeight F G rho g ^ D * B₀) := by
          apply ENNReal.ofReal_le_ofReal
          calc C * adelicHeight F G rho (ι m.val * g) ^ D * ‖ψ m.val‖
              ≤ C * (adelicHeight F G rho (ι m.val) ^ D * adelicHeight F G rho g ^ D) *
                  ‖ψ m.val‖ := by gcongr
            _ = C * adelicHeight F G rho g ^ D *
                  (adelicHeight F G rho (ι m.val) ^ D * ‖ψ m.val‖) := by ring
            _ ≤ C * adelicHeight F G rho g ^ D * B₀ := by
                have : 0 ≤ C * adelicHeight F G rho g ^ D :=
                  mul_nonneg hC (Real.rpow_nonneg hHg _)
                gcongr
  obtain ⟨hint, hzero⟩ := properEisensteinTestVanishing t.p t.l t.iU t.unipotentRadical
    t.leviSplit hGfin hPfin hLfin f ψ hfc hψc hfP hfU hψG hψ0 hbound
  have hpair : fam.leviPairingIntegrand J S g ψ =
      fun q => properEisensteinTestSum t.p f ψ q.out := by
    funext x
    unfold StandardParabolicFamily.leviPairingIntegrand properEisensteinTestSum
    rw [hkey]
  refine ⟨hpair ▸ hint, ?_⟩
  unfold StandardParabolicFamily.leviPairing
  rw [hpair]
  exact hzero

end Langlands.Global.StandardParabolicFamily.NestedLeviParabolic
