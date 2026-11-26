import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Transfer of the inducing \(L^2\) condition between compact subgroups -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

private theorem integrable_of_compact_cosets {K L : Subgroup (AdelicGroupPoints F G)}
    (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
    (hL : IsCompact (L : Set (AdelicGroupPoints F G)))
    (hKL : IsOpen {k : K | k.val ∈ L}) (hLK : IsOpen {l : L | l.val ∈ K})
    {Q : Type} [MeasurableSpace Q] (ν : Measure Q) [SFinite ν]
    {f : K × Q → ℝ} {g : L × Q → ℝ}
    (hf : Integrable f ((compactHaarProbability F G K hK).prod ν))
    (hchange : ∀ t : L, ∃ (k : K) (r : Q → Q) (a : ℝ), MeasurePreserving r ν ν ∧
      ∀ (h : K.subgroupOf L) (q : Q),
        g (t * h.val, q) = a * f (k * ⟨h.val.val, h.property⟩, r q)) :
    Integrable g ((compactHaarProbability F G L hL).prod ν) := by
  classical
  let mK := compactHaarProbability F G K hK
  let mL := compactHaarProbability F G L hL
  let H := K.subgroupOf L
  let i : H →* K :=
    { toFun := fun h => ⟨h.val.val, h.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j : H →* L := Subgroup.subtype H
  have hj : IsOpenEmbedding j := hLK.isOpenEmbedding_subtypeVal
  have hi : IsOpenEmbedding i := by
    have hcomp : IsEmbedding ((Subtype.val : K → AdelicGroupPoints F G) ∘ i) := by
      change IsEmbedding ((Subtype.val : L → AdelicGroupPoints F G) ∘ (Subtype.val : H → L))
      exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    refine ⟨IsEmbedding.subtypeVal.of_comp_iff.mp hcomp, ?_⟩
    have hrange : range i = {k : K | k.val ∈ L} := by
      ext k
      constructor
      · rintro ⟨y, rfl⟩
        exact y.val.property
      · intro hk
        exact ⟨⟨⟨k.val, hk⟩, k.property⟩, rfl⟩
    rwa [hrange]
  let mKH := mK.comap i
  let mLH := mL.comap j
  let : IsHaarMeasure mKH := IsHaarMeasure.comap (mH := inferInstance) mK hi
  let : IsHaarMeasure mLH := IsHaarMeasure.comap (mH := inferInstance) mL hj
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let : CompactSpace H := isCompact_iff_compactSpace.mp
    ((H.isClosed_of_isOpen hLK).isCompact : IsCompact (H : Set L))
  have hscalar : mLH = haarScalarFactor mLH mKH • mKH :=
    isMulLeftInvariant_eq_smul_of_innerRegular mLH mKH
  have hlocal (t : L) : IntegrableOn g (range (fun h : H => t * j h) ×ˢ (univ : Set Q))
      (mL.prod ν) := by
    obtain ⟨k, r, a, hr, hEq⟩ := hchange t
    let mapK : H → K := fun h => k * i h
    let mapL : H → L := fun h => t * j h
    have hKmap : IsOpenEmbedding mapK := (Homeomorph.mulLeft k).isOpenEmbedding.comp hi
    have hLmap : IsOpenEmbedding mapL := (Homeomorph.mulLeft t).isOpenEmbedding.comp hj
    have hcomapK : mK.comap mapK = mKH := by
      ext s hs
      rw [hKmap.measurableEmbedding.comap_apply, hi.measurableEmbedding.comap_apply]
      rw [show mapK = (fun z : K => k * z) ∘ i from rfl, image_comp]
      exact measure_smul mK k (i '' s)
    have hcomapL : mL.comap mapL = mLH := by
      ext s hs
      rw [hLmap.measurableEmbedding.comap_apply, hj.measurableEmbedding.comap_apply]
      rw [show mapL = (fun z : L => t * z) ∘ j from rfl, image_comp]
      exact measure_smul mL t (j '' s)
    have hmapK : (mKH.map mapK).prod (ν.map r) ≤ mK.prod ν := by
      rw [← hcomapK, hKmap.measurableEmbedding.map_comap, hr.map_eq]
      exact Measure.prod_mono Measure.restrict_le_self le_rfl
    have hKcomp : Integrable (f ∘ Prod.map mapK r) (mKH.prod ν) := by
      have hp := hf.mono_measure hmapK
      rw [Measure.map_prod_map _ _ hKmap.continuous.measurable hr.measurable] at hp
      exact hp.comp_aemeasurable (hKmap.continuous.measurable.prodMap hr.measurable).aemeasurable
    have hc : Integrable (g ∘ Prod.map mapL id) (mLH.prod ν) := by
      rw [hscalar, Measure.prod_smul_left]
      have heq : g ∘ Prod.map mapL id = fun z => a * (f ∘ Prod.map mapK r) z := by
        funext z
        exact hEq z.1 z.2
      rw [heq]
      exact (hKcomp.const_mul a).smul_measure_nnreal
    have hprod : MeasurableEmbedding (Prod.map mapL (id : Q → Q)) :=
      hLmap.measurableEmbedding.prodMap MeasurableEmbedding.id
    have hd := hprod.integrable_map_iff.mpr hc
    rw [← Measure.map_prod_map _ _ hLmap.continuous.measurable measurable_id,
      Measure.map_id, ← hcomapL, hLmap.measurableEmbedding.map_comap,
      Measure.restrict_prod_eq_prod_univ] at hd
    exact hd
  let : DiscreteTopology (L ⧸ H) := QuotientGroup.discreteTopology hLK
  let : Finite (L ⧸ H) := finite_of_compact_of_discrete
  have hcover : (⋃ t : L ⧸ H, range (fun h : H => t.out * j h) ×ˢ (univ : Set Q)) = univ := by
    apply Set.eq_univ_of_forall
    intro z
    have ht := QuotientGroup.mk_out_eq_mul (s := H) z.1
    obtain ⟨l, hl⟩ := ht
    refine mem_iUnion.mpr ⟨QuotientGroup.mk z.1, ⟨⟨l⁻¹, ?_⟩, mem_univ _⟩⟩
    change (QuotientGroup.mk z.1 : L ⧸ H).out * l.val⁻¹ = z.1
    rw [hl, mul_inv_cancel_right]
  rw [← integrableOn_univ, ← hcover]
  exact integrableOn_finite_iUnion.mpr (fun t => hlocal t.out)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints InducedInnerProductIntegrable Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

variable {K L : Subgroup (AdelicGroupPoints F G)}
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Changing the finite part of the Iwasawa compact while keeping the infinite projection
preserves membership in `A²_P`. The weight on each coset of the compact intersection changes
by a fixed modulus and the corresponding Levi quotient coordinate is right translated. -/
theorem isSquareIntegrableInducedForm_of_compact_change
    (hK : IsIwasawaCompact (fam.p J) K) (hLc : IsCompact (L : Set (AdelicGroupPoints F G)))
    (hKmax : IsMaximalCompactSubgroup F G K) (hLmax : IsMaximalCompactSubgroup F G L)
    (hinf : K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) φ) :
    IsSquareIntegrableInducedForm L hLc rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ := by
  have hKinf : K.comap (ofInfinite F G).toMonoidHom = L.comap (ofInfinite F G).toMonoidHom := by
    ext x
    change ofInfinite F G x ∈ K ↔ ofInfinite F G x ∈ L
    conv_lhs => rw [IsMaximalCompactSubgroup.eq_comap_prod F G K hKmax]
    conv_rhs => rw [IsMaximalCompactSubgroup.eq_comap_prod F G L hLmax]
    change (infinite F G (ofInfinite F G x) ∈ K.map (infinite F G).toMonoidHom ∧
        finite F G (ofInfinite F G x) ∈ K.map (finite F G).toMonoidHom) ↔
      (infinite F G (ofInfinite F G x) ∈ L.map (infinite F G).toMonoidHom ∧
        finite F G (ofInfinite F G x) ∈ L.map (finite F G).toMonoidHom)
    rw [hinf, finite_ofInfinite]
    simp only [one_mem, and_true]
  refine ⟨hKinf ▸ hφ.1, hφ.2.1, ?_⟩
  let P := fam.P J
  let M := fam.M J
  let U := fam.U J
  let ml := map F M P (fam.l J)
  let pg := map F P G (fam.p J)
  let up := map F U P (fam.iU J)
  let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
  let measureM := RestrictionSplitCentre.canonicalMeasure F M
  let : SFinite measureM := by
    dsimp only [measureM, RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure]
    infer_instance
  let δ := modulusParameter F P
  let weight (k : AdelicGroupPoints F G) (m : AdelicGroupPoints F M) :=
    ‖parameterPower F P (-δ) (ml m)‖ * ‖φ (pg (ml m) * k)‖ ^ 2
  have hinv (k : AdelicGroupPoints F G) : ∀ a ∈ Γ, ∀ m, weight k (a * m) = weight k m := by
    apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
      (Δ := rationalSubgroup F M)
    · intro a ha m
      have hcancel : ‖parameterPower F P (-δ) (ml a)‖ *
          ‖parameterPower F P (halfModulusParameter F P) (ml a)‖ ^ 2 = 1 := by
        rw [pow_two, ← mul_assoc, ← norm_mul, ← parameterPower_add, ← norm_mul, ← parameterPower_add,
          neg_modulus_add_half_add_half, parameterPower_zero, norm_one]
      dsimp only [weight]
      rw [form_canonical_mul hφ.2.1 ha, map_mul, parameterPower_mul, norm_mul, norm_mul, mul_pow,
        mul_mul_mul_comm, hcancel, one_mul]
    · intro a ha m
      dsimp only [weight]
      rw [parameterPower_map_mul_left _ (fam.l J) (rationalSubgroup_le_normOneSubgroup F M ha),
        form_rational_mul hφ.1.1 ha]
  let e : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  let : IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication e fam.connectedReductive
      (fam.isUnipotentRadical J)
  refine integrable_of_compact_cosets hK.isCompact hLc
    (IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K L hLmax hinf)
    (IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G L K hKmax hinf.symm)
    measureM (f := fun z => weight z.1.val z.2.out) hφ.2.2 ?_
  intro t
  obtain ⟨q, k, hk, ht⟩ := hK.exists_eq t.val
  let m₀ := leviComponent (fam.l J) (fam.iU J) q
  let u := radicalComponent (fam.l J) (fam.iU J) q
  let r := LeftCosetSpace.rightTranslate Γ m₀
  have hsplit : ml m₀ * up u = q :=
    leviComponent_mul_radicalComponent (fam.l J) (fam.iU J) q
  refine ⟨⟨k, hk⟩, r, ‖parameterPower F P δ (ml m₀)‖, ?_, ?_⟩
  · exact RestrictionSplitCentre.canonicalMeasure_rightInvariant F M centralSplitTorusCharacter
      (fam.isCompatible J).levi.isConnectedReductive m₀
  · intro h z
    let m := z.out
    have hz : r z = LeftCosetSpace.mk Γ (m * m₀) := by
      change LeftCosetSpace.rightTranslate Γ m₀ z = _
      rw [← Quotient.out_eq z]
      rfl
    have hU : ml (m * m₀) * up u * (ml (m * m₀))⁻¹ ∈
        (SubgroupFunctor.range (fam.iU J)).carrier _ :=
      (fam.isUnipotentRadical J).1.isNormal _ _ _ trivial ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hU
    have hvP : up v = ml (m * m₀) * up u * (ml (m * m₀))⁻¹ := hv
    have hprod : ml m * q = up v * ml (m * m₀) := by
      rw [hvP, inv_mul_cancel_right, ← hsplit, map_mul, mul_assoc]
    have hvG : map F U G (fam.iU J ≫ fam.p J) v ∈
        parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J) :=
      Subgroup.mem_sup_left ⟨v, rfl⟩
    have hvalue : φ (pg (ml m) * (t.val * h.val.val)) =
        φ (pg (ml (m * m₀)) * (k * h.val.val)) := by
      have ht' : pg q * k = t.val := ht
      have hmul : pg (ml m) * (t.val * h.val.val) =
          map F U G (fam.iU J ≫ fam.p J) v * (pg (ml (m * m₀)) * (k * h.val.val)) := by
        calc
          _ = pg (ml m * q) * (k * h.val.val) := by rw [← ht', map_mul, mul_assoc, mul_assoc]
          _ = _ := by rw [hprod, map_mul, mul_assoc, map_comp_apply_of_hom]
      rw [hmul]
      exact hφ.1.1 _ hvG _
    change weight (t.val * h.val.val) m =
      ‖parameterPower F P δ (ml m₀)‖ * weight (k * h.val.val) (r z).out
    rw [hz, LeftCosetSpace.out_mk_of_invariant Γ _ (hinv _)]
    dsimp only [weight]
    rw [hvalue, map_mul ml m m₀, parameterPower_mul, norm_mul]
    have hmod : ‖parameterPower F P δ (ml m₀)‖ * ‖parameterPower F P (-δ) (ml m₀)‖ = 1 := by
      rw [← norm_mul, ← parameterPower_add, add_neg_cancel, parameterPower_zero, norm_one]
    calc
      _ = ‖parameterPower F P (-δ) (ml m)‖ *
          (‖parameterPower F P δ (ml m₀)‖ * ‖parameterPower F P (-δ) (ml m₀)‖) *
          ‖φ (pg (ml m * ml m₀) * (k * h.val.val))‖ ^ 2 := by rw [hmod, mul_one]
      _ = _ := by ring

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- For Iwasawa compacts with the same archimedean projection, the space `A²_P`
of a standard parabolic is independent of the finite compact. -/
def AdelicSquareIntegrableInducedCompactChangeStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (K L : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (fam.p J) K) (hL : IsIwasawaCompact (fam.p J) L),
    IsMaximalCompactSubgroup F G K → IsMaximalCompactSubgroup F G L →
    K.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (φ : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ ↔
        IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J) φ

theorem adelicSquareIntegrableInducedCompactChange :
    AdelicSquareIntegrableInducedCompactChangeStatement := by
  intro F _ _ G _ _ _ fam J K L hK hL hKmax hLmax hinf N d rho hsmooth hcalc φ
  exact ⟨fam.isSquareIntegrableInducedForm_of_compact_change J rho hsmooth hcalc
    hK hL.isCompact hKmax hLmax hinf,
    fam.isSquareIntegrableInducedForm_of_compact_change J rho hsmooth hcalc
      hL hK.isCompact hLmax hKmax hinf.symm⟩

end Langlands.Global
