import Langlands.Global.AdelicInducedPairingCompactChange
import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Global.AdelicWavePacketChamberDecayReduction

/-! # Finite cutoffs for a change of the Iwasawa compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.WavePacketCompactChange

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints
open InducedInnerProductIntegrable InducedPairingCompactChange

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P}
  [IsClosedImmersion (iU ≫ p).hom.hom.left] {l : M ⟶ P}
  {K L : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hL : IsIwasawaCompact p L)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "H" => (RealCharacterDual F P)

/-- The source height after right translation, minus the target height. -/
def heightDifference (s g : Gₐ) : H := hK.height (g * s) - hL.height g

open Classical in
/-- The translate of an inducing form restricted to a single height-difference fibre. -/
def cutoff (s : Gₐ) (u : H) (φ : Gₐ → ℂ) (g : Gₐ) : ℂ :=
  if heightDifference hK hL s g = u then φ (g * s) else 0

/-- The exponential coefficient on the fibre of a given height difference. -/
def coefficient (u : H) (lam : ComplexCharacterParameter F P) : ℂ :=
  Complex.exp (complexParameterPairing F P lam u)

private theorem heightDifference_map_mul (s : Gₐ) (x : AdelicGroupPoints F P) (g : Gₐ) :
    heightDifference hK hL s (map F P G p x * g) = heightDifference hK hL s g := by
  unfold heightDifference
  rw [mul_assoc, hK.height_map_mul, hL.height_map_mul]
  abel

private theorem heightDifference_eq_conjugate (s : Gₐ)
    (hC : IsIwasawaCompact p (K.map (MulAut.conj s).toMonoidHom)) (g : Gₐ) :
    heightDifference hK hL s g = hC.height g - hL.height g + hK.height s := by
  obtain ⟨x, k, hk, rfl⟩ := hC.exists_eq g
  obtain ⟨c, hc, rfl⟩ := hk
  have he : (MulAut.conj s c) * s = s * c := by
    change (s * c * s⁻¹) * s = _
    group
  unfold heightDifference
  simp only [MulEquiv.coe_toMonoidHom]
  rw [mul_assoc, he, ← mul_assoc, hK.height_mul_right _ hc, hK.height_map_mul,
    hC.height_eq (show MulAut.conj s c ∈ K.map (MulAut.conj s).toMonoidHom from ⟨c, hc, rfl⟩) rfl]
  abel

set_option maxHeartbeats 950000 in
/-- Conjugating the infinite compact and then changing the finite compact gives a common
finite, injectively indexed family of height fibres. Cutting a translated automorphic form
along any of these fibres preserves its automorphy for the target compact. -/
theorem exists_cutoff_family (b : InfiniteAdelicGroupPoints F G)
    (hKmax : IsMaximalCompactSubgroup F G K) (hLmax : IsMaximalCompactSubgroup F G L)
    (hinf : (K.comap (ofInfinite F G).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.comap (ofInfinite F G).toMonoidHom)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    let s := ofInfinite F G b
    ∃ (q : ℕ) (u : Fin q → H), Function.Injective u ∧
      (∀ g : Gₐ, ∃ i, heightDifference hK hL s g = u i) ∧
      ∀ {φ : Gₐ → ℂ}, IsAutomorphicFunctionOn F G hsmooth hcalc
          (parabolicQuotientSubgroup F p iU l) (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (L.comap (ofInfinite F G).toMonoidHom) rho (cutoff hK hL s (u i) φ) := by
  classical
  intro s
  let C := K.map (MulAut.conj s).toMonoidHom
  have hC : IsIwasawaCompact p C := by
    simpa only [inv_inv] using hK.conjInv s⁻¹
  have hCmax : IsMaximalCompactSubgroup F G C := hKmax.map_conj s
  have hCL : C.map (infinite F G).toMonoidHom = L.map (infinite F G).toMonoidHom := by
    change (K.map (MulAut.conj (ofInfinite F G b)).toMonoidHom).map (infinite F G).toMonoidHom = _
    rw [map_infinite_map_conj_ofInfinite, ← hKmax.comap_ofInfinite_eq_map_infinite, hinf,
      hLmax.comap_ofInfinite_eq_map_infinite]
  let Δ := heightDifference hK hL s
  have hΔ (g : Gₐ) : Δ g = hC.height g - hL.height g + hK.height s :=
    heightDifference_eq_conjugate hK hL s hC g
  have hfinite : (range Δ).Finite := by
    refine ((hC.finite_range_height_sub hL (IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G C L
      hLmax hCL)).image (fun u => u + hK.height s)).subset ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨_, mem_range_self g, (hΔ g).symm⟩
  let : Fintype (range Δ) := hfinite.fintype
  let e := Fintype.equivFin (range Δ)
  let u := fun i => (e.symm i).val
  refine ⟨_, u, fun i j hij => e.symm.injective (Subtype.ext hij), ?_, ?_⟩
  · intro g
    let z : range Δ := ⟨Δ g, mem_range_self g⟩
    refine ⟨e z, ?_⟩
    change z.val = (e.symm (e z)).val
    rw [e.symm_apply_apply]
  intro φ hφ i
  let δ := fun x : FiniteAdelicGroupPoints F G => Δ (ofFinite F G x)
  have hfiniteCoord (g : Gₐ) : Δ g = δ (finite F G g) := by
    rw [show δ (finite F G g) = Δ (ofFinite F G (finite F G g)) from rfl, hΔ, hΔ]
    congr 1
    simpa only [pair_projections] using hC.height_sub_pair_eq_of_infinite_eq hL hCmax hLmax hCL
      (infinite F G g) (finite F G g)
  let S : Set (FiniteAdelicGroupPoints F G) := {x | δ x = u i}
  have hcont : Continuous Δ := (hK.continuous_height.comp (continuous_id.mul_const s)).sub hL.continuous_height
  have hfibre : IsClopen {g | Δ g = u i} := by
    refine ⟨isClosed_singleton.preimage hcont, ?_⟩
    have heq : {g | Δ g = u i} = (Δ ⁻¹' (range Δ \ {u i}))ᶜ := by
      ext g
      simp only [mem_ofPred_eq, mem_compl_iff, mem_preimage, mem_sdiff, mem_singleton_iff,
        mem_range_self, true_and, not_not]
    rw [heq]
    exact ((hfinite.subset sdiff_subset).isClosed.preimage hcont).isOpen_compl
  have hS : IsClopen S := hfibre.preimage (ofFinite F G).continuous
  have hleft (x : Gₐ) (hx : x ∈ parabolicQuotientSubgroup F p iU l) (g : Gₐ) :
      finite F G (x * g) ∈ S ↔ finite F G g ∈ S := by
    have hrange : parabolicQuotientSubgroup F p iU l ≤ (map F P G p).toMonoidHom.range := by
      apply sup_le
      · rintro _ ⟨a, rfl⟩
        exact ⟨map F U P iU a, (map_comp_apply_of_hom iU a).symm⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨map F M P l (rational F M a), (map_comp_apply_of_hom l _).symm⟩
    obtain ⟨a, rfl⟩ := hrange hx
    change δ (finite F G (map F P G p a * g)) = u i ↔ δ (finite F G g) = u i
    rw [← hfiniteCoord, ← hfiniteCoord]
    change heightDifference hK hL s (map F P G p a * g) = u i ↔ heightDifference hK hL s g = u i
    rw [heightDifference_map_mul]
  let J : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
    ⟨C.map (finite F G).toMonoidHom ⊓ L.map (finite F G).toMonoidHom,
      (hCmax.isOpen_finite F G C).inter (hLmax.isOpen_finite F G L)⟩
  have hright (x : FiniteAdelicGroupPoints F G) (hx : x ∈ J) (y : FiniteAdelicGroupPoints F G) :
      y * x ∈ S ↔ y ∈ S := by
    have hm {B : Subgroup Gₐ} (hB : IsMaximalCompactSubgroup F G B)
        (hxB : x ∈ B.map (finite F G).toMonoidHom) : ofFinite F G x ∈ B := by
      rw [IsMaximalCompactSubgroup.eq_comap_prod F G B hB]
      change infinite F G (ofFinite F G x) ∈ B.map (infinite F G).toMonoidHom ∧
        finite F G (ofFinite F G x) ∈ B.map (finite F G).toMonoidHom
      rw [infinite_ofFinite, finite_ofFinite]
      exact ⟨one_mem _, hxB⟩
    have hxC := hm hCmax hx.1
    have hxL := hm hLmax hx.2
    change Δ (ofFinite F G (y * x)) = u i ↔ Δ (ofFinite F G y) = u i
    rw [map_mul, hΔ, hΔ, hC.height_mul_right _ hxC, hL.height_mul_right _ hxL]
  have hφs := hφ.infiniteRightTranslate hcalc b
  rw [hinf] at hφs
  convert hφs.indicator_finite S hS hleft J hright using 1
  funext g
  simp only [cutoff, indicator, mem_preimage, S, mem_ofPred_eq, ← hfiniteCoord]
  rfl

/-- The height difference converts a translated twist into a finite sum of twists for the
new compact. -/
theorem parameterTwist_cutoff {q : ℕ} {u : Fin q → H} {s : Gₐ}
    (hu : Function.Injective u) (hcover : ∀ g, ∃ i, heightDifference hK hL s g = u i)
    (φ : Gₐ → ℂ) (lam : ComplexCharacterParameter F P) (g : Gₐ) :
    hK.parameterTwist φ lam (g * s) =
      ∑ i, coefficient (u i) lam * hL.parameterTwist (cutoff hK hL s (u i) φ) lam g := by
  classical
  obtain ⟨i, hi⟩ := hcover g
  rw [Finset.sum_eq_single i]
  · have hheight : hK.height (g * s) = u i + hL.height g := (sub_eq_iff_eq_add.mp hi)
    simp only [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower,
      cutoff, hi, ite_true, coefficient]
    conv_lhs => rw [hheight, map_add, Complex.exp_add]
    ring
  · intro j _ hj
    have hj' : heightDifference hK hL s g ≠ u j := fun h => hj (hu (h.symm.trans hi))
    simp [cutoff, hj', IsIwasawaCompact.parameterTwist]
  · simp

theorem heightCoordinates_eq_of_difference {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {s g : Gₐ} {u : H}
    (hu : heightDifference hK hL s g = u) :
    hK.heightCoordinates e (g * s) = hL.heightCoordinates e g + parameterCoordinates F P e u := by
  have hh : hK.height (g * s) = u + hL.height g := sub_eq_iff_eq_add.mp hu
  simp only [IsIwasawaCompact.heightCoordinates, hh, parameterCoordinates_add]
  exact add_comm _ _

/-- Evaluating an invariant function on the translated coset can use any representative
of the original coset followed by the same right translation. -/
theorem rightTranslate_out_of_invariant {Γ : Subgroup Gₐ} {f : Gₐ → ℂ}
    (hf : IsLeftInvariantUnder F G Γ f) (s : Gₐ) (x : LeftCosetSpace Γ) :
    f (LeftCosetSpace.rightTranslate Γ s x).out = f (x.out * s) := by
  have hx : LeftCosetSpace.rightTranslate Γ s x = LeftCosetSpace.mk Γ (x.out * s) := by
    rw [← LeftCosetSpace.rightTranslate_mk, LeftCosetSpace.mk_out]
  rw [hx]
  exact LeftCosetSpace.out_mk_of_invariant Γ f hf _

section Measure

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ M}
  {π : P ⟶ M}
  [IsIso (subgroupMultiplication l iU)]
  (hG : IsConnectedReductive G) (hl : IsRationalLeviSubgroup l)
  (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (ha : IsSplitComponent a) (hA : IsSplitTorus A.toGrp) (hlπ : l ≫ π = 𝟙 M)
  (μK μL : Measure (AdelicGroupPoints F M)) [μK.IsHaarMeasure] [μL.IsHaarMeasure]
  (hμK : IsIwasawaCompatibleMeasure K hK.isCompact p iU l μK)
  (hμL : IsIwasawaCompatibleMeasure L hL.isCompact p iU l μL)
  {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {β : (Fin n → ℝ) → ℝ}
  (hβc : Continuous β) (hβs : HasCompactSupport β)
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}

local notation "Γ" => (principalParabolic p)
local notation "mΓ" => (principalParabolicMeasure p)
local notation "A₂K" => (IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l)
local notation "A₂L" => (IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc p iU l)

private theorem mem_parabolicQuotient_of_mem_principal (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {x : Gₐ} (hx : x ∈ Γ) : x ∈ parabolicQuotientSubgroup F p iU l :=
  mem_parabolicQuotientSubgroup_of_rational_range (p := p) iU l hU hx.1 hx.2

private theorem squareIntegrable_cutoff_equivariant {s : Gₐ} {u : H} {φ : Gₐ → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ) :
    IsSplitComponentEquivariant p l (cutoff hK hL s u φ) := by
  classical
  intro a ha g
  simp only [cutoff, heightDifference_map_mul, mul_assoc, hφ a ha]
  split <;> simp_all

include hG hl hU ha hA hlπ hμK hμL e hβc hβs in
set_option maxHeartbeats 1150000 in
/-- The cutoffs belong to the target inducing space. On each fibre, translating the old
weight by the negative height difference gives the weighted square for the new compact. -/
theorem squareIntegrable_cutoff (hβne : ∃ y, β y ≠ 0) {s : Gₐ} {u : H} {φ : Gₐ → ℂ}
    (hφ : A₂K φ)
    (hcut : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (L.comap (ofInfinite F G).toMonoidHom) rho (cutoff hK hL s u φ)) :
    A₂L (cutoff hK hL s u φ) := by
  classical
  let φ₀ := cutoff hK hL s u φ
  have heq : IsSplitComponentEquivariant p l φ₀ := squareIntegrable_cutoff_equivariant hK hL hφ.2.1
  refine ⟨hcut, heq, ?_⟩
  let v := parameterCoordinates F P e u
  let β₁ : (Fin n → ℝ) → ℝ := fun y => β (y - v)
  have hβ₁c : Continuous β₁ := hβc.comp (continuous_id.sub continuous_const)
  have hβ₁s : HasCompactSupport β₁ := hβs.comp_homeomorph (Homeomorph.addRight (-v))
  have hIK := integrable_inducedInnerProduct_integrand e hl.isConnectedReductive ha hA hlπ
    μK hβ₁c hβ₁s hφ hφ
  have hfK := (quotient_weightedProduct p iU l μK hK e β₁ hU hμK hβ₁c
    hφ.1.2.1.1 hφ.1.2.1.1 hφ.1.1 hφ.1.1).1.mpr hIK
  let : (Measure.haar : Measure Gₐ).IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  let r := LeftCosetSpace.rightTranslate Γ s
  have hr : MeasurePreserving r mΓ mΓ := LeftCosetSpace.measurePreserving_rightTranslate_discrete
    Γ (principalParabolic_discrete p) Measure.haar s
  let f₁ := weightedProduct p hK e β₁ φ φ
  let f₀ := weightedProduct p hL e β φ₀ φ₀
  have hf₁ (x : LeftCosetSpace Γ) : f₁ (r x).out = f₁ (x.out * s) :=
    rightTranslate_out_of_invariant (fun a ha g =>
      weightedProduct_leftInvariant p iU l hK e β₁ hU.1.isUnipotent hφ.1.1 hφ.1.1 a
        (mem_parabolicQuotient_of_mem_principal hU ha) g) s x
  have hfc : Continuous f₀ := continuous_weightedProduct p hL e β hβc hcut.2.1.1 hcut.2.1.1
  have hf₀ : Integrable (fun x : LeftCosetSpace Γ => f₀ x.out) mΓ := by
    refine (hr.integrable_comp_of_integrable hfK).mono ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (LeftCosetSpace.measurable_out_of_invariant Γ hfc.measurable fun a ha g =>
        weightedProduct_leftInvariant p iU l hL e β hU.1.isUnipotent hcut.1 hcut.1 a
          (mem_parabolicQuotient_of_mem_principal hU ha) g).aestronglyMeasurable
    change ‖f₀ x.out‖ ≤ ‖f₁ (r x).out‖
    rw [hf₁]
    by_cases hx : heightDifference hK hL s x.out = u
    · simp only [f₀, f₁, φ₀, weightedProduct, cutoff, hx, ite_true,
        heightCoordinates_eq_of_difference hK hL e hx, β₁, add_sub_cancel_right, v]
      exact le_rfl
    · simp only [f₀, φ₀, weightedProduct, cutoff, hx, ite_false, mul_zero, zero_mul, norm_zero]
      exact norm_nonneg _
  have hIL := (quotient_weightedProduct p iU l μL hL e β hU hμL hβc
    hcut.2.1.1 hcut.2.1.1 hcut.1 hcut.1).1.mp hf₀
  exact integrable_normWeight_of_integrable_kernel p iU l hL.isCompact μL e hl hlπ hβc hβs hβne
    hcut.2.1.1 hcut.1 heq hIL

include hG hl hU ha hA hlπ hμK hμL hβc hβs in
set_option maxHeartbeats 1150000 in
/-- Adding the pairings of corresponding cut pieces recovers the original pairing. Each
fibre requires a single shift of the target height weight, absorbed by the central Levi. -/
theorem inducedInnerProduct_eq_sum_cutoff {q : ℕ} {u : Fin q → H} {s : Gₐ}
    (hu : Function.Injective u) (hcover : ∀ g, ∃ i, heightDifference hK hL s g = u i)
    {φ ψ : Gₐ → ℂ} (hφ : A₂K φ) (hψ : A₂K ψ)
    (hφ₀ : ∀ i, A₂L (cutoff hK hL s (u i) φ)) (hψ₀ : ∀ i, A₂L (cutoff hK hL s (u i) ψ)) :
    inducedInnerProduct K hK.isCompact p l μK e β φ ψ =
      ∑ i, inducedInnerProduct L hL.isCompact p l μL e β
        (cutoff hK hL s (u i) φ) (cutoff hK hL s (u i) ψ) := by
  classical
  let f := weightedProduct p hK e β φ ψ
  let β₀ (i : Fin q) (y : Fin n → ℝ) := β (y + parameterCoordinates F P e (u i))
  let f₀ (i : Fin q) := weightedProduct p hL e (β₀ i) (cutoff hK hL s (u i) φ)
    (cutoff hK hL s (u i) ψ)
  have hI := integrable_inducedInnerProduct_integrand e hl.isConnectedReductive ha hA hlπ
    μK hβc hβs hφ hψ
  have hf := (quotient_weightedProduct p iU l μK hK e β hU hμK hβc
    hφ.1.2.1.1 hψ.1.2.1.1 hφ.1.1 hψ.1.1).2 hI
  have hβ₀c (i : Fin q) : Continuous (β₀ i) := hβc.comp (continuous_id.add_const _)
  have hβ₀s (i : Fin q) : HasCompactSupport (β₀ i) := hβs.comp_homeomorph (Homeomorph.addRight _)
  have hI₀ (i : Fin q) := integrable_inducedInnerProduct_integrand e hl.isConnectedReductive ha hA hlπ
    μL (hβ₀c i) (hβ₀s i) (hφ₀ i) (hψ₀ i)
  have hQ (i : Fin q) := quotient_weightedProduct p iU l μL hL e (β₀ i) hU hμL (hβ₀c i)
    (hφ₀ i).1.2.1.1 (hψ₀ i).1.2.1.1 (hφ₀ i).1.1 (hψ₀ i).1.1
  let : (Measure.haar : Measure Gₐ).IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  let r := LeftCosetSpace.rightTranslate Γ s
  have hr : MeasurePreserving r mΓ mΓ := LeftCosetSpace.measurePreserving_rightTranslate_discrete
    Γ (principalParabolic_discrete p) Measure.haar s
  let : BorelSpace (LeftCosetSpace Γ) :=
    LeftCosetSpace.discreteQuotientBorelSpace Γ (principalParabolic_discrete p)
  have hf₀ (x : LeftCosetSpace Γ) : f (r x).out = ∑ i, f₀ i x.out := by
    have hx := rightTranslate_out_of_invariant (f := f) (fun a ha g =>
      weightedProduct_leftInvariant p iU l hK e β hU.1.isUnipotent hφ.1.1 hψ.1.1 a
        (mem_parabolicQuotient_of_mem_principal hU ha) g) s x
    change f (r x).out = f (x.out * s) at hx
    rw [hx]
    obtain ⟨i, hi⟩ := hcover x.out
    rw [Finset.sum_eq_single i]
    · simp only [f, f₀, weightedProduct, cutoff, hi, ite_true,
        heightCoordinates_eq_of_difference hK hL e hi, β₀]
    · intro j _ hj
      have hj' : heightDifference hK hL s x.out ≠ u j := fun h => hj (hu (h.symm.trans hi))
      simp only [f₀, weightedProduct, cutoff, hj', ite_false, mul_zero, zero_mul]
    · simp
  calc
    _ = ∫ x : LeftCosetSpace Γ, f x.out ∂mΓ := hf
    _ = ∫ x : LeftCosetSpace Γ, f (r x).out ∂mΓ :=
      (hr.integral_comp (LeftCosetSpace.rightTranslateHomeomorph Γ s).toMeasurableEquiv.measurableEmbedding
        (fun x => f x.out)).symm
    _ = ∫ x : LeftCosetSpace Γ, ∑ i, f₀ i x.out ∂mΓ := integral_congr_ae (Filter.Eventually.of_forall hf₀)
    _ = ∑ i, ∫ x : LeftCosetSpace Γ, f₀ i x.out ∂mΓ :=
      integral_finsetSum _ fun i _ => (hQ i).1.mpr (hI₀ i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← (hQ i).2 (hI₀ i)]
      exact inducedInnerProduct_shift p iU l hL.isCompact μL e hl β
        (parameterCoordinates F P e (u i)) (hφ₀ i).1.1 (hψ₀ i).1.1 (hφ₀ i).2.1 (hψ₀ i).2.1

end Measure

/-- Distinct cut pieces have disjoint support in the inducing pairing. -/
theorem inducedInnerProduct_cutoff_ne (μL : Measure (AdelicGroupPoints F M))
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)
    {s : Gₐ} {u v : H} (huv : u ≠ v) (φ ψ : Gₐ → ℂ) :
    inducedInnerProduct L hL.isCompact p l μL e β (cutoff hK hL s u φ) (cutoff hK hL s v ψ) = 0 := by
  classical
  unfold inducedInnerProduct
  apply integral_eq_zero_of_ae
  filter_upwards with k
  apply integral_eq_zero_of_ae
  filter_upwards with x
  let g := map F P G p (map F M P l x.out) * (k : Gₐ)
  change _ * cutoff hK hL s u φ g * starRingEnd ℂ (cutoff hK hL s v ψ g) = 0
  by_cases hx : heightDifference hK hL s g = u
  · have hx' : heightDifference hK hL s g ≠ v := hx ▸ huv
    simp only [cutoff, hx', ite_false, map_zero, mul_zero]
  · simp only [cutoff, hx, ite_false, mul_zero, zero_mul]

/-- The exponential height factor is unitary at an imaginary parameter. -/
theorem coefficient_mul_star_of_imaginary (u : H) (x : RealCharacterParameter F P) :
    coefficient u (imaginaryParameter F P x) * starRingEnd ℂ (coefficient u (imaginaryParameter F P x)) = 1 := by
  simp only [coefficient, ChamberDecay.complexParameterPairing_imaginaryParameter, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

end Langlands.Global.WavePacketCompactChange
