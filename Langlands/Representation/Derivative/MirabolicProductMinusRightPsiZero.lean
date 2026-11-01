import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary

/-!
# The `Ψ⁻` clause of BZ77 Proposition 4.13(c) for source `P_1`
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV

/-! ## The explicit rank cast of the general linear group -/

section GeneralLinearCast

variable {R : Type*} [CommRing R]

/-- The identity `GL_b → GL_a` along a rank equality `a = b`. -/
def generalLinearCastHom {a b : ℕ} (h : a = b) : GeneralLinear b R →* GeneralLinear a R := by
  subst h
  exact MonoidHom.id _

theorem generalLinearCastHom_apply {a b : ℕ} (h : a = b) (x : GeneralLinear b R)
    (i j : Fin a) :
    (generalLinearCastHom h x).val i j = x.val (Fin.cast h i) (Fin.cast h j) := by
  subst h
  rfl

theorem continuous_generalLinearCastHom [TopologicalSpace R] {a b : ℕ} (h : a = b) :
    Continuous (generalLinearCastHom (R := R) h) := by
  subst h
  exact continuous_id

/-- For a zero first rank, the rank-zero model's reindexing undoes the cast. -/
theorem reindex_generalLinearCastHom_zero (m : ℕ) (g : GeneralLinear (m + 0) R) :
    reindex (R := R) (finCongr (by omega : 0 + m = m))
        (generalLinearCastHom (Nat.add_comm 0 m) g) = g := by
  apply Units.ext
  ext i j
  change (generalLinearCastHom (Nat.add_comm 0 m) g).val _ _ = g.val i j
  rw [generalLinearCastHom_apply]
  rfl

end GeneralLinearCast

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual general linear rank transport is pullback along the explicit cast. -/
def generalLinearRankCastIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    generalLinearRankCast.{uF, uV} T h ≅
      Mirabolic.continuousPullbackFunctor (generalLinearCastHom h)
        (continuous_generalLinearCastHom h) := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-! ## The target side at `r = 0` -/

section Target

/-- The target functor at `r = 0`, with the rank-zero model of the binary product
and the rank cast replaced by the explicit pullback. -/
abbrev rightPsiZeroTarget (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((k + 1) + 0) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T 0).prod (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
    T.binaryLeftZeroTensorFunctor (a := 0) (b := k + 1) rfl ⋙
      Mirabolic.continuousPullbackFunctor (generalLinearCastHom (Nat.add_comm 0 (k + 1)))
        (continuous_generalLinearCastHom (Nat.add_comm 0 (k + 1)))

/-- The carrier of `Ψ⁻τ × ρ` at `r = 0`: remove the lift and the trivial
`V_1`-quotient of `τ`. -/
def rightPsiZeroTargetEquiv (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    (rightPsiZeroTarget.{uF, uV} T k).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  ULift.moduleEquiv.trans
    (TensorProduct.congr
      (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
        (psiMinus_zero_trivial T X.1))
      (LinearEquiv.refl ℂ X.2))

/-- The identification turns the action of `g ∈ GL_(k+1)` into `1 ⊗ ρ(g)`. -/
theorem rightPsiZeroTargetEquiv_action (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (g : GeneralLinear ((k + 1) + 0) F.Carrier)
    (x : letI := T.topology; (rightPsiZeroTarget.{uF, uV} T k).obj X) :
    letI := T.topology
    rightPsiZeroTargetEquiv T k X (((rightPsiZeroTarget.{uF, uV} T k).obj X).representation g x) =
      TensorProduct.map LinearMap.id (X.2.representation g) (rightPsiZeroTargetEquiv T k X x) := by
  let := T.topology
  let eX := TensorProduct.congr
    (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
      (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)
  have key : eX.toLinearMap ∘ₗ
        LinearMap.lTensor (Jacquet.Localization.Coinvariants X.1.representation
          (radical 0 F.Carrier) 1) (X.2.representation g) =
      TensorProduct.map LinearMap.id (X.2.representation g) ∘ₗ eX.toLinearMap :=
    TensorProduct.ext' fun _ _ => rfl
  have hg := reindex_generalLinearCastHom_zero (R := F.Carrier) (k + 1) g
  have h1 : rightPsiZeroTargetEquiv T k X
      (((rightPsiZeroTarget.{uF, uV} T k).obj X).representation g x) =
      eX (LinearMap.lTensor (Jacquet.Localization.Coinvariants X.1.representation
          (radical 0 F.Carrier) 1)
        (X.2.representation (reindex (R := F.Carrier) (finCongr (by omega : 0 + (k + 1) = k + 1))
          (generalLinearCastHom (Nat.add_comm 0 (k + 1)) g))) x.down) := rfl
  rw [h1, hg]
  exact LinearMap.congr_fun key x.down

/-- The identification is natural in both inputs. -/
theorem rightPsiZeroTargetEquiv_natural (T : F.TopologicalData) (k : ℕ)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y)
    (x : letI := T.topology; (rightPsiZeroTarget.{uF, uV} T k).obj X) :
    letI := T.topology
    rightPsiZeroTargetEquiv T k Y (SmoothRep.hom ((rightPsiZeroTarget.{uF, uV} T k).map φ) x) =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
        (rightPsiZeroTargetEquiv T k X x) := by
  let := T.topology
  have key : (TensorProduct.congr
        (localizationTrivialEquiv Y.1.representation (radical 0 F.Carrier) 1
          (psiMinus_zero_trivial T Y.1)) (LinearEquiv.refl ℂ Y.2)).toLinearMap ∘ₗ
        TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T 0).map φ.1)).toLinearMap
          (SmoothRep.hom φ.2).toLinearMap =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap ∘ₗ
        (TensorProduct.congr
          (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
            (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ a
    rfl
  exact LinearMap.congr_fun key x.down

end Target

/-! ## The `Ψ⁻` clause at `r = 0` -/

section Zero

open Induction

set_option maxHeartbeats 400000 in
/-- BZ77 4.13(c), `Ψ⁻` clause, at source rank one: `Ψ⁻(τ × ρ) ≅ Ψ⁻τ × ρ`
naturally, for `τ` on `P_1` and `ρ` on `GL_(k+1)`, with the full `GL_0` input. -/
theorem rightPsiCompatibility_zero (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    Nonempty
      (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙ Mirabolic.psiMinus T ((k + 1) + 0) ≅
        (Mirabolic.psiMinus T 0).prod
            (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
          T.binaryNormalizedProductFunctor 0 (k + 1) ⋙
            generalLinearRankCast T (Nat.add_comm 0 (k + 1))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + 1 + 0 + 1)
  let := T.generalLinearLocallyCompactSpace (k + 1 + 0 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + 1 + 0) (F := F.Carrier)
  -- The split group data: `G = P_(k+2)`, `r = projection`, `s = levi`, `H` of case (III).
  let r := projection (n := k + 1 + 0) (F := F.Carrier)
  let s := levi (n := k + 1 + 0) (F := F.Carrier)
  let H := rightSubgroup (k + 1) 0 F.Carrier
  have hrs : ∀ l, r (s l) = l := projection_levi
  have hr : Continuous r := GeneralLinear.Mirabolic.continuous_projection
  have hs : Continuous s := continuous_levi
  have hH : IsClosed (H : Set (mirabolic (k + 1 + 0) F.Carrier)) := rightSubgroup_isClosed
  have hsH : ∀ l, s l ∈ H := levi_mem_rightSubgroup_zero
  have hNr : r.ker = radical (k + 1 + 0) F.Carrier := ker_projection
  let θ : SmoothCharacter ℂ r.ker :=
    { toMonoidHom := 1
      isOpen_ker := by
        rw [MonoidHom.ker_one, Subgroup.coe_top]
        exact isOpen_univ }
  have hI : ∀ i : H.comap r.ker.subtype, i = 1 := fun i =>
    Subtype.ext (Subtype.ext (eq_one_of_mem_rightSubgroup_zero (m := k + 1) i.2 i.1.2))
  -- Measures on the kernel, the trivial intersection and the quotient.
  have hNc : IsClosed (r.ker : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  let : LocallyCompactSpace r.ker := hNc.locallyCompactSpace
  have hIc : IsClosed ((H.comap r.ker.subtype : Subgroup r.ker) : Set r.ker) :=
    hH.preimage continuous_subtype_val
  let : LocallyCompactSpace (H.comap r.ker.subtype) := hIc.locallyCompactSpace
  let : MeasurableSpace r.ker := borel _
  have : BorelSpace r.ker := ⟨rfl⟩
  let : MeasurableSpace (H.comap r.ker.subtype) := borel _
  have : BorelSpace (H.comap r.ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := ⟨rfl⟩
  have hBasis := compactOpenBasis_congr hNr.symm (radical_compactOpenBasis T (k + 0))
  have hCover := compactOpenCover_congr hNr.symm (radical_compactOpenCover T (k + 0))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure r.ker := haar
  let μI : Measure (H.comap r.ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The Levi Haar modulus; the trivial character is invariant.
  have hHaar : ∀ l : GeneralLinear (k + 1 + 0) F.Carrier,
      mulEquivHaarChar (splitKernelConjugation r s l) =
        (T.determinantNorm (k + 1 + 0) l : ℝ≥0)⁻¹ := by
    intro l
    let : LocallyCompactSpace (radical (k + 1 + 0) F.Carrier) :=
      radical_isClosed.locallyCompactSpace
    let : MeasurableSpace (radical (k + 1 + 0) F.Carrier) := borel _
    have : BorelSpace (radical (k + 1 + 0) F.Carrier) := ⟨rfl⟩
    have hl : (levi l)⁻¹ ∈ Subgroup.normalizer
        (radical (k + 1 + 0) F.Carrier : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
      rw [← hNr]
      simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
    exact (mulEquivHaarChar_normalizerConj_congr hNr ((levi l)⁻¹)
      (by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]) hl).trans
      (mulEquivHaarChar_conj_levi_inv T (k + 1 + 0) l hl)
  have hθl : ∀ (l : GeneralLinear (k + 1 + 0) F.Carrier) (n : r.ker),
      θ.toMonoidHom (splitKernelConjugation r s l n) = θ.toMonoidHom n := fun _ _ => rfl
  -- The source identification.
  let σ := fun X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) =>
    twist (T.rightCharacter (k + 1) 0).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)
  have hσ : ∀ X, IsSmooth (σ X) := fun X =>
    (isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) 0).isOpen_ker).mpr
      (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth)
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
        Mirabolic.psiMinus T ((k + 1) + 0)).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 := fun X =>
    (Submodule.quotEquivOfEq _ _ (relations_congr (compactInduced H (σ X)) hNr.symm
      1 θ.toMonoidHom fun _ => rfl)).trans
      (trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν)
  have hE : ∀ X (g : GeneralLinear ((k + 1) + 0) F.Carrier)
      (v : (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
        Mirabolic.psiMinus T ((k + 1) + 0)).obj X),
      E X (((T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
        Mirabolic.psiMinus T ((k + 1) + 0)).obj X).representation g v) =
        TensorProduct.map LinearMap.id (X.2.representation g) (E X v) := by
    intro X g v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T ((k + 1) + 0) A v
    let w := trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
      (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom f)
    have h1 : E X (((T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
          Mirabolic.psiMinus T ((k + 1) + 0)).obj X).representation g
          (Mirabolic.psiMinusQuotient T ((k + 1) + 0) A f)) =
        ((realPowerCharacter (T.determinantNorm ((k + 1) + 0)) (-(1 / 2 : ℝ)) g : ℂ)) •
          trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
            (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom
              (compactInduced H (σ X) (s g) f)) :=
      map_smul (E X) _ _
    have h2 := trivialSplitKernelEquiv_section r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν
      hBasis μN μI hν g (hθl g) f
    have h3 : σ X ⟨s g, hsH g⟩ w =
        ((((T.determinantNorm (k + 1) g : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
          TensorProduct.map LinearMap.id (X.2.representation g) w :=
      twist_rightInducing_levi_zero T (k + 1) X.1.representation X.2.representation g w
    have hc : ((realPowerCharacter (T.determinantNorm ((k + 1) + 0)) (-(1 / 2 : ℝ)) g : ℂ)) *
        ((((mulEquivHaarChar (splitKernelConjugation r s g))⁻¹ : ℝ≥0) : ℝ) : ℂ) *
          ((((T.determinantNorm (k + 1) g : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [hHaar g, coe_realPowerCharacter]
      exact half_mul_inv_inv_mul_half (T.determinantNorm (k + 1) g)
    have hw : E X (Mirabolic.psiMinusQuotient T ((k + 1) + 0) A f) = w := rfl
    refine h1.trans ?_
    rw [h2, h3, hw]
    exact smul_smul_smul_of_mul_eq_one _ _ _ _ hc
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (v : (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
        Mirabolic.psiMinus T ((k + 1) + 0)).obj X),
      E Y (SmoothRep.hom ((T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
        Mirabolic.psiMinus T ((k + 1) + 0)).map φ) v) =
        TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
          (E X v) := by
    intro X Y φ v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T ((k + 1) + 0) A v
    exact trivialSplitKernelEquiv_natural r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis
      μN μI hν (hσ Y) (twistIntertwining (T.rightCharacter (k + 1) 0).toMonoidHom
        (MixedProductTensor.pullbackMap rightProjection
          (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))) f
  -- Assemble the natural isomorphism.
  let iso0 : T.rightMixedProductFunctor.{uF, uV} (k + 1) 0 ⋙
      Mirabolic.psiMinus T ((k + 1) + 0) ≅ rightPsiZeroTarget.{uF, uV} T k :=
    NatIso.ofComponents
      (fun X => SmoothRep.mkIso (equivOfCommonModel
        (fun g => TensorProduct.map LinearMap.id (X.2.representation g)) (E X)
        (rightPsiZeroTargetEquiv T k X) (hE X) (rightPsiZeroTargetEquiv_action T k X)))
      (fun φ => MixedProductTensor.smoothRep_hom_ext fun v =>
        symm_comp_natural _ _ _ _ _ _ _ (hEnat φ) (rightPsiZeroTargetEquiv_natural T k φ) v)
  exact ⟨iso0 ≪≫ Functor.isoWhiskerLeft
    ((Mirabolic.psiMinus T 0).prod
        (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
      T.binaryLeftZeroTensorFunctor.{uF, uV} (a := 0) (b := k + 1) rfl)
    (generalLinearRankCastIso.{uF, max uF uV} T (Nat.add_comm 0 (k + 1))).symm⟩

end Zero

end Langlands.Derivative.MirabolicProductMinus
