import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupPolish
import Langlands.GroupScheme.Rational.CharacterRestrictionProof

/-! # Integrability of the integrand of the inner product on `A^2_P`

For `φ, ψ ∈ A^2_P` and a continuous compactly supported weight `β`, the integrand of
`inducedInnerProduct` is integrable on `K × M(F) \ M(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Topology
open scoped CategoryTheory.MonObj TensorProduct ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

namespace LeftCosetSpace

section Generic

variable {H : Type} [Group H] (Γ : Subgroup H)

/-- A representative of the class of `m` differs from `m` by a left factor in `Γ`. -/
theorem exists_out_mk (m : H) : ∃ g₀ ∈ Γ, (mk Γ m).out = g₀ * m := by
  have h : mk Γ (mk Γ m).out = mk Γ m := Quotient.out_eq _
  refine ⟨(mk Γ m).out * m⁻¹, ((mk_eq_mk_iff Γ _ _).mp h.symm), ?_⟩
  simp

/-- Evaluation at a quotient representative of a left `Γ`-invariant function. -/
theorem out_mk_of_invariant {E : Type} (f : H → E) (hinv : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m)
    (m : H) : f (mk Γ m).out = f m := by
  obtain ⟨g₀, hg₀, hout⟩ := exists_out_mk Γ m
  rw [hout, hinv g₀ hg₀ m]

/-- Invariance under two subgroups gives invariance under their join. -/
theorem invariant_sup {E : Type} {Δ : Subgroup H} (f : H → E)
    (h₁ : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m) (h₂ : ∀ g₀ ∈ Δ, ∀ m, f (g₀ * m) = f m) :
    ∀ g₀ ∈ Γ ⊔ Δ, ∀ m, f (g₀ * m) = f m := by
  intro g₀ hg₀
  let S : Subgroup H :=
    { carrier := {x | ∀ m, f (x * m) = f m}
      mul_mem' := fun {x y} hx hy m => by
        rw [mul_assoc, hx, hy]
      one_mem' := fun m => by
        change f (1 * m) = f m
        rw [one_mul]
      inv_mem' := fun {x} hx m => by
        rw [← hx (x⁻¹ * m), mul_inv_cancel_left] }
  exact (sup_le (fun x hx => h₁ x hx) (fun x hx => h₂ x hx) : Γ ⊔ Δ ≤ S) hg₀

/-- A function on `X × H` that is left `Γ`-invariant in the second variable, evaluated at
quotient representatives, is continuous when the function is. -/
theorem continuous_out_of_invariant [TopologicalSpace H] [IsTopologicalGroup H]
    {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
    (f : X → H → E) (hf : Continuous (fun z : X × H => f z.1 z.2))
    (hinv : ∀ x, ∀ g₀ ∈ Γ, ∀ m, f x (g₀ * m) = f x m) :
    Continuous (fun z : X × LeftCosetSpace Γ => f z.1 z.2.out) := by
  have hq : IsOpenQuotientMap (Prod.map (id : X → X) (mk Γ)) :=
    IsOpenQuotientMap.prodMap IsOpenQuotientMap.id (isOpenQuotientMap_mk Γ)
  apply hq.isQuotientMap.continuous_iff.mpr
  have heq : ((fun z : X × LeftCosetSpace Γ => f z.1 z.2.out) ∘ Prod.map id (mk Γ)) =
      fun z : X × H => f z.1 z.2 := by
    funext z
    exact out_mk_of_invariant Γ (f z.1) (hinv z.1) z.2
  rw [heq]
  exact hf

/-- Evaluation at representatives of an invariant measurable function is measurable for the
quotient sigma algebra. -/
theorem measurable_out_of_invariant [MeasurableSpace H] {E : Type} [MeasurableSpace E]
    {f : H → E} (hf : Measurable f) (hinv : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m) :
    Measurable (fun q : LeftCosetSpace Γ => f q.out) := by
  apply measurable_from_quotient.mpr
  have h : (fun q : LeftCosetSpace Γ => f q.out) ∘ Quotient.mk'' = f :=
    funext fun m => out_mk_of_invariant Γ f hinv m
  rw [h]
  exact hf

/-- Integration over `Γ \ H` of an invariant function is integration over the chosen
fundamental domain. -/
theorem lintegral_discreteQuotientMeasure [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) {f : H → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ g₀ ∈ Γ, ∀ m, f (g₀ * m) = f m) :
    ∫⁻ q, f q.out ∂(discreteQuotientMeasure Γ hΓ ν) =
      ∫⁻ m in fundamentalDomain Γ hΓ, f m ∂ν := by
  rw [discreteQuotientMeasure, quotientMeasure,
    lintegral_map (measurable_out_of_invariant Γ hf hinv) (measurable_mk Γ)]
  exact lintegral_congr fun m => out_mk_of_invariant Γ f hinv m

end Generic

end LeftCosetSpace

namespace InducedInnerProductIntegrable

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]

section Algebra

/-- The adelic-point map of a composite is the composite of the adelic-point maps. -/
theorem map_comp_apply {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of F))} (f : H₁ ⟶ H₂)
    (g : H₂ ⟶ H₃) (x : AdelicGroupPoints F H₁) :
    map F H₁ H₃ (f ≫ g) x = map F H₂ H₃ g (map F H₁ H₂ f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

variable {P M : GroupScheme (Spec (CommRingCat.of F))}

/-- Norm-one points of `M(𝔸)` have trivial logarithm in `P` after the Levi embedding. -/
theorem characterLog_map_of_mem_normOne (l : M ⟶ P) {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) : characterLog F P (map F M P l x) = 0 := by
  rw [characterLog_map, (characterLog_eq_zero_iff F M x).mpr hx, map_zero]

theorem characterLog_map_mul_left (l : M ⟶ P) {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    characterLog F P (map F M P l (x * m)) = characterLog F P (map F M P l m) := by
  rw [map_mul, characterLog_mul, characterLog_map_of_mem_normOne l hx, zero_add]

theorem characterLog_map_mul_right (l : M ⟶ P) {x : AdelicGroupPoints F M}
    (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    characterLog F P (map F M P l (m * x)) = characterLog F P (map F M P l m) := by
  rw [map_mul, characterLog_mul, characterLog_map_of_mem_normOne l hx, add_zero]

theorem parameterPower_map_mul_left (lam : ComplexCharacterParameter F P) (l : M ⟶ P)
    {x : AdelicGroupPoints F M} (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    parameterPower F P lam (map F M P l (x * m)) = parameterPower F P lam (map F M P l m) := by
  rw [parameterPower, parameterPower, characterLog_map_mul_left l hx]

theorem parameterPower_map_mul_right (lam : ComplexCharacterParameter F P) (l : M ⟶ P)
    {x : AdelicGroupPoints F M} (hx : x ∈ normOneSubgroup F M) (m : AdelicGroupPoints F M) :
    parameterPower F P lam (map F M P l (m * x)) = parameterPower F P lam (map F M P l m) := by
  rw [parameterPower, parameterPower, characterLog_map_mul_right l hx]

theorem parameterPower_map_of_mem_normOne (lam : ComplexCharacterParameter F P) (l : M ⟶ P)
    {x : AdelicGroupPoints F M} (hx : x ∈ normOneSubgroup F M) :
    parameterPower F P lam (map F M P l x) = 1 := by
  rw [parameterPower, characterLog_map_of_mem_normOne l hx, map_zero, Complex.exp_zero]

theorem parameterPower_of_characterLog_eq_zero (lam : ComplexCharacterParameter F P)
    {x : AdelicGroupPoints F P} (hx : characterLog F P x = 0) : parameterPower F P lam x = 1 := by
  rw [parameterPower, hx, map_zero, Complex.exp_zero]

theorem parameterPower_mul (lam : ComplexCharacterParameter F P) (x y : AdelicGroupPoints F P) :
    parameterPower F P lam (x * y) = parameterPower F P lam x * parameterPower F P lam y := by
  rw [parameterPower, parameterPower, parameterPower, characterLog_mul, map_add, Complex.exp_add]

theorem parameterPower_add (lam mu : ComplexCharacterParameter F P) (x : AdelicGroupPoints F P) :
    parameterPower F P (lam + mu) x = parameterPower F P lam x * parameterPower F P mu x := by
  rw [parameterPower, parameterPower, parameterPower, map_add, LinearMap.add_apply, Complex.exp_add]

theorem parameterPower_zero (x : AdelicGroupPoints F P) : parameterPower F P 0 x = 1 := by
  rw [parameterPower, map_zero, LinearMap.zero_apply, Complex.exp_zero]

section Modulus

variable [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]

theorem neg_modulus_add_half_add_half :
    -modulusParameter F P + halfModulusParameter F P + halfModulusParameter F P = 0 := by
  rw [modulusParameter, halfModulusParameter, ← TensorProduct.neg_tmul, ← TensorProduct.add_tmul,
    ← TensorProduct.add_tmul]
  have h : (-1 + 1 / 2 + 1 / 2 : ℂ) = 0 := by norm_num
  rw [h, TensorProduct.zero_tmul]

/-- `|m^{-2ρ_P}| |m^{ρ_P}|² = 1`. -/
theorem enorm_modulus_mul_half_sq (x : AdelicGroupPoints F P) :
    ‖parameterPower F P (-modulusParameter F P) x‖ₑ *
      ‖parameterPower F P (halfModulusParameter F P) x‖ₑ ^ 2 = 1 := by
  rw [sq, ← mul_assoc, ← enorm_mul, ← enorm_mul, ← parameterPower_add, ← parameterPower_add,
    neg_modulus_add_half_add_half, parameterPower_zero, enorm_one]

end Modulus

/-- Real pairings with a fixed parameter are continuous on the real dual. -/
theorem continuous_realParameterPairing (mu0 : RealCharacterParameter F P) :
    Continuous (realParameterPairing F P mu0) := by
  induction mu0 using TensorProduct.inductionOn with
  | tmul t χ =>
    have h : ⇑(realParameterPairing F P (t ⊗ₜ[ℤ] χ)) = fun H => t * H χ :=
      funext fun H => realParameterPairing_tmul F P t χ H
    rw [h]
    exact continuous_const.mul (continuous_dualEval F P χ)
  | add x y hx hy => rw [map_add, LinearMap.coe_add]; exact hx.add hy

/-- Complex pairings with a fixed parameter are continuous on the real dual. -/
theorem continuous_complexParameterPairing (lam : ComplexCharacterParameter F P) :
    Continuous (complexParameterPairing F P lam) := by
  induction lam using TensorProduct.inductionOn with
  | tmul t χ =>
    have h : ⇑(complexParameterPairing F P (t ⊗ₜ[ℤ] χ)) = fun H => t * (H χ : ℂ) :=
      funext fun H => complexParameterPairing_tmul F P t χ H
    rw [h]
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dualEval F P χ))
  | add x y hx hy => rw [map_add, LinearMap.coe_add]; exact hx.add hy

theorem continuous_parameterPower (lam : ComplexCharacterParameter F P) :
    Continuous (parameterPower F P lam) :=
  Complex.continuous_exp.comp
    ((continuous_complexParameterPairing lam).comp (continuous_characterLog F P))

theorem continuous_parameterCoordinates {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Continuous (parameterCoordinates F P e) :=
  continuous_pi fun _ => continuous_realParameterPairing _

theorem parameterCoordinates_add {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (H H' : RealCharacterDual F P) :
    parameterCoordinates F P e (H + H') =
      parameterCoordinates F P e H + parameterCoordinates F P e H' := by
  funext j
  simp only [parameterCoordinates, map_add, Pi.add_apply]

theorem parameterCoordinates_injective {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    Function.Injective (parameterCoordinates F P e) := by
  intro H H' h
  have hflip : (realParameterPairing F P).flip H = (realParameterPairing F P).flip H' := by
    apply ((Pi.basisFun ℝ (Fin n)).map e).ext
    intro j
    rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearMap.flip_apply, LinearMap.flip_apply]
    exact congrFun h j
  apply AddMonoidHom.ext
  intro χ
  have hχ := LinearMap.congr_fun hflip ((1 : ℝ) ⊗ₜ[ℤ] χ)
  rw [LinearMap.flip_apply, LinearMap.flip_apply, realParameterPairing_tmul,
    realParameterPairing_tmul, one_mul, one_mul] at hχ
  exact hχ

/-- A Levi embedding with a retraction induces an injective map of real duals. -/
theorem realCharacterDualMap_injective {l : M ⟶ P} {π : P ⟶ M} (h : l ≫ π = 𝟙 M) :
    Function.Injective (realCharacterDualMap F M P l) := by
  intro H H' hH
  apply AddMonoidHom.ext
  intro χ
  have hχ : characterRestrict l (characterRestrict π χ) = χ := by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, h, characterRestrict_id,
      AddMonoidHom.id_apply]
  have h' := DFunLike.congr_fun hH (characterRestrict π χ)
  change H (characterRestrict l (characterRestrict π χ)) =
    H' (characterRestrict l (characterRestrict π χ)) at h'
  rwa [hχ] at h'

end Algebra

section Forms

variable {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)

theorem map_map_mem_parabolicQuotientSubgroup {x : AdelicGroupPoints F M}
    (hx : x ∈ rationalSubgroup F M) :
    map F P G p (map F M P l x) ∈ parabolicQuotientSubgroup F p iU l := by
  obtain ⟨g₀, rfl⟩ := hx
  apply Subgroup.mem_sup_right
  exact ⟨g₀, map_comp_apply l p _⟩

variable {p iU l}

/-- Left invariance of a form on `U(𝔸) M(F) \ G(𝔸)` under `M(F)` in Levi coordinates. -/
theorem form_rational_mul {χ : AdelicGroupPoints F G → ℂ}
    (hχ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) χ)
    {x : AdelicGroupPoints F M} (hx : x ∈ rationalSubgroup F M) (m : AdelicGroupPoints F M)
    (g : AdelicGroupPoints F G) :
    χ (map F P G p (map F M P l (x * m)) * g) = χ (map F P G p (map F M P l m) * g) := by
  rw [map_mul, map_mul, mul_assoc]
  exact hχ _ (map_map_mem_parabolicQuotientSubgroup p iU l hx) _

/-- The `A^n_P` condition in Levi coordinates. -/
theorem form_canonical_mul {χ : AdelicGroupPoints F G → ℂ}
    (hχ : IsSplitComponentEquivariant p l χ)
    {x : AdelicGroupPoints F M} (hx : x ∈ RestrictionSplitCentre.canonicalSubgroup F M)
    (m : AdelicGroupPoints F M) (g : AdelicGroupPoints F G) :
    χ (map F P G p (map F M P l (x * m)) * g) =
      parameterPower F P (halfModulusParameter F P) (map F M P l x) *
        χ (map F P G p (map F M P l m) * g) := by
  rw [map_mul, map_mul, mul_assoc]
  exact hχ x hx _

end Forms

section Positive

variable {P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ M)
  (hi : Function.Injective (characterRestrict a)) [(characterRestrict a).range.FiniteIndex]
  (I : Type) [Fintype I] (eA : A.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

include hi I eA in
/-- The logarithm of a positive point determines the point. -/
theorem positivePointMap_injective_of_characterLog {b b' : intrinsicSubgroup F A}
    (h : characterLog F M (positivePointMap F M A a b) =
      characterLog F M (positivePointMap F M A a b')) : b = b' := by
  rw [← PositiveRealTorus.positiveFactor_positivePointMap F M A a hi I eA b,
    ← PositiveRealTorus.positiveFactor_positivePointMap F M A a hi I eA b',
    PositiveRealTorus.positiveFactor_apply, PositiveRealTorus.positiveFactor_apply]
  change (PositiveRealTorus.positiveAmbientLogEquiv F M A a hi I eA).symm
      (Multiplicative.ofAdd (characterLog F M (positivePointMap F M A a b))) = _
  rw [h]
  rfl

variable {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (l : M ⟶ P)

/-- The coordinates `y(a)` of `H_P(a)` for a positive point `a ∈ A_M`. -/
def positiveCoordinates (b : intrinsicSubgroup F A) : Fin n → ℝ :=
  parameterCoordinates F P e (characterLog F P (map F M P l (positivePointMap F M A a b)))

theorem positiveCoordinates_mul (b b' : intrinsicSubgroup F A) :
    positiveCoordinates a e l (b * b') = positiveCoordinates a e l b + positiveCoordinates a e l b' := by
  simp only [positiveCoordinates, map_mul, characterLog_mul, parameterCoordinates_add]

theorem continuous_positiveCoordinates : Continuous (positiveCoordinates a e l) :=
  (continuous_parameterCoordinates e).comp ((continuous_characterLog F P).comp
    ((map F M P l).continuous.comp (positivePointMap F M A a).continuous))

include hi I eA in
theorem positiveCoordinates_injective {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) :
    Function.Injective (positiveCoordinates a e l) := by
  intro b b' h
  apply positivePointMap_injective_of_characterLog a hi I eA
  apply realCharacterDualMap_injective hlπ
  rw [← characterLog_map, ← characterLog_map]
  exact parameterCoordinates_injective e h

include hi I eA in
/-- `a ↦ β(y(a))` has compact support on `A_M` for compactly supported `β`. -/
theorem hasCompactSupport_positiveCoordinates {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M)
    {β : (Fin n → ℝ) → ℝ} (hβs : HasCompactSupport β) :
    HasCompactSupport (fun b : intrinsicSubgroup F A => β (positiveCoordinates a e l b)) := by
  let L := PositiveRealTorus.positiveLogCoordinateEquiv F A I eA
  let Z : (I → ℝ) →+ (Fin n → ℝ) := AddMonoidHom.mk'
    (fun v => positiveCoordinates a e l (L.symm (Multiplicative.ofAdd v)))
    (fun v w => by
      simp only [ofAdd_add, map_mul, positiveCoordinates_mul])
  have hZc : Continuous Z :=
    (continuous_positiveCoordinates a e l).comp (L.symm.continuous.comp continuous_ofAdd)
  let ZL := Z.toRealLinearMap hZc
  have hZinj : Function.Injective ZL := by
    intro v w h
    have h' := positiveCoordinates_injective a hi I eA e l hlπ h
    exact Multiplicative.ofAdd.injective (L.symm.injective h')
  have hcl : Topology.IsClosedEmbedding ZL :=
    LinearMap.isClosedEmbedding_of_injective (f := ZL.toLinearMap)
      (LinearMap.ker_eq_bot.mpr hZinj)
  have hβZ : HasCompactSupport (fun v : I → ℝ => β (ZL v)) := hβs.comp_isClosedEmbedding hcl
  have hβZ' : HasCompactSupport (fun v : Multiplicative (I → ℝ) => β (ZL v.toAdd)) := hβZ
  have hfun : (fun b : intrinsicSubgroup F A => β (positiveCoordinates a e l b)) =
      (fun v : Multiplicative (I → ℝ) => β (ZL v.toAdd)) ∘ L.toHomeomorph := by
    funext b
    simp only [Function.comp_apply]
    congr 1
    change _ = positiveCoordinates a e l (L.symm (Multiplicative.ofAdd (L b).toAdd))
    rw [ofAdd_toAdd]
    exact congrArg _ (L.symm_apply_apply b).symm
  rw [hfun]
  exact hβZ'.comp_homeomorph L.toHomeomorph

end Positive

section Decomposition

variable {M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ M)

theorem mem_rationalNormOneSubgroup_iff (x : normOneSubgroup F M) :
    x ∈ rationalNormOneSubgroup F M ↔ (x : AdelicGroupPoints F M) ∈ rationalSubgroup F M := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

/-- Translating the chosen fundamental domain of `M(F)` in `M(𝔸)` by a central positive point
gives a fundamental domain of `M(F)` in `M(𝔸)^1`. -/
theorem isFundamentalDomain_positiveSlice (hc : IsCentral a) (b : intrinsicSubgroup F A)
    (ν : Measure (normOneSubgroup F M)) :
    IsFundamentalDomain (rationalNormOneSubgroup F M)
      {n : normOneSubgroup F M | positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈
        LeftCosetSpace.fundamentalDomain (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M)} ν := by
  set s := LeftCosetSpace.fundamentalDomain (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M)
  have hs : MeasurableSet s := LeftCosetSpace.measurableSet_fundamentalDomain _ _
  have hmeas : MeasurableSet {n : normOneSubgroup F M |
      positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s} :=
    hs.preimage ((continuous_const.mul continuous_subtype_val).measurable)
  refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun n => ?_
  have hcomm : ∀ x : AdelicGroupPoints F M, positivePointMap F M A a b *
      (x * (n : AdelicGroupPoints F M)) = x * (positivePointMap F M A a b * n) := fun x => by
    rw [← mul_assoc, (positivePointMap_commute F M A a hc b x).eq, mul_assoc]
  obtain ⟨g₀, hg₀, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M) (positivePointMap F M A a b * n)
  have hN : (g₀ : AdelicGroupPoints F M) ∈ normOneSubgroup F M :=
    rationalSubgroup_le_normOneSubgroup F M g₀.2
  refine ⟨⟨⟨g₀, hN⟩, (mem_rationalNormOneSubgroup_iff
    (⟨(g₀ : AdelicGroupPoints F M), hN⟩ : normOneSubgroup F M)).mpr g₀.2⟩, ?_, ?_⟩
  · change positivePointMap F M A a b * ((g₀ : AdelicGroupPoints F M) * n) ∈ s
    rw [hcomm]
    exact hg₀
  · intro δ hδ
    change positivePointMap F M A a b *
      (((δ : normOneSubgroup F M) : AdelicGroupPoints F M) * n) ∈ s at hδ
    rw [hcomm] at hδ
    have h := huniq ⟨_, (mem_rationalNormOneSubgroup_iff _).mp δ.2⟩ hδ
    have h' : ((δ : normOneSubgroup F M) : AdelicGroupPoints F M) = (g₀ : AdelicGroupPoints F M) :=
      congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

/-- Integration over `[M] = A_M M(F) \ M(𝔸)` of an invariant function is integration over the
chosen fundamental domain of `M(F)` in `M(𝔸)^1`. -/
theorem lintegral_canonicalMeasure {Hc : AdelicGroupPoints F M → ℝ≥0∞} (hHc : Measurable Hc)
    (hinv : ∀ g₀ ∈ RestrictionSplitCentre.canonicalRationalSubgroup F M, ∀ m,
      Hc (g₀ * m) = Hc m) :
    ∫⁻ q, Hc q.out ∂(RestrictionSplitCentre.canonicalMeasure F M) =
      ∫⁻ n in LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F M)
        (isDiscrete_rationalNormOneSubgroup F M), Hc (n : AdelicGroupPoints F M) ∂Measure.haar := by
  have hmeas := LeftCosetSpace.measurable_out_of_invariant _ hHc hinv
  rw [RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure,
    lintegral_map hmeas (RestrictionSplitCentre.measurable_normOneToQuotient _ _ _ _),
    normOneRationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
    LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
  refine (lintegral_map (f := fun q₁ => Hc (RestrictionSplitCentre.normOneToQuotient F M
      (RestrictionSplitCentre.canonicalRestrictionTorus F M)
      (RestrictionSplitCentre.canonicalRestrictionComponent F M) q₁).out)
    (hmeas.comp (RestrictionSplitCentre.measurable_normOneToQuotient _ _ _ _))
    (LeftCosetSpace.measurable_mk _)).trans ?_
  exact lintegral_congr fun n =>
    LeftCosetSpace.out_mk_of_invariant _ Hc hinv (n : AdelicGroupPoints F M)

variable (hi : Function.Injective (characterRestrict a)) [(characterRestrict a).range.FiniteIndex]
  (I : Type) [Fintype I] (eA : A.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral a)

/-- Integration over the chosen fundamental domain of `M(F)` in `M(𝔸)` of a function that
factors along `M(𝔸) = A_M × M(𝔸)^1`. -/
theorem setLIntegral_fundamentalDomain_eq (μM : Measure (AdelicGroupPoints F M))
    [μM.IsHaarMeasure] {Hf : AdelicGroupPoints F M → ℝ≥0∞} (hH : Measurable Hf)
    (B : intrinsicSubgroup F A → ℝ≥0∞) (hB : Measurable B)
    {g : normOneSubgroup F M → ℝ≥0∞} (hg : Measurable g)
    (hfac : ∀ (b : intrinsicSubgroup F A) (n : normOneSubgroup F M),
      Hf (positivePointMap F M A a b * (n : AdelicGroupPoints F M)) = B b * g n)
    (hinv : ∀ (g₀ : rationalNormOneSubgroup F M) (n : normOneSubgroup F M), g (g₀ • n) = g n) :
    ∫⁻ m in LeftCosetSpace.fundamentalDomain (rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M), Hf m ∂μM =
      (Measure.haarScalarFactor μM Measure.haar : ℝ≥0∞) *
        ((∫⁻ b, B b ∂normalizedPositiveHaarMeasure F M A a hi I eA hc) *
          ∫⁻ n in LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F M)
            (isDiscrete_rationalNormOneSubgroup F M), g n ∂Measure.haar) := by
  set s := LeftCosetSpace.fundamentalDomain (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M)
  set s1 := LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F M)
    (isDiscrete_rationalNormOneSubgroup F M)
  have hs : MeasurableSet s := LeftCosetSpace.measurableSet_fundamentalDomain _ _
  have h1 : ∫⁻ m in s, Hf m ∂μM = (Measure.haarScalarFactor μM Measure.haar : ℝ≥0∞) *
      ∫⁻ m in s, Hf m ∂(Measure.haar : Measure (AdelicGroupPoints F M)) := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μM Measure.haar]
    rw [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have h2 : ∫⁻ m in s, Hf m ∂(Measure.haar : Measure (AdelicGroupPoints F M)) =
      ∫⁻ z : intrinsicSubgroup F A × normOneSubgroup F M,
        s.indicator Hf (positivePointMap F M A a z.1 * (z.2 : AdelicGroupPoints F M))
        ∂((normalizedPositiveHaarMeasure F M A a hi I eA hc).prod Measure.haar) := by
    rw [← lintegral_indicator hs, ← map_normalizedPositiveHaarMeasure_prod F M A a hi I eA hc]
    exact lintegral_map_equiv _ (normOneDecomposition F M A a hi I eA).toMeasurableEquiv
  have := normalizedPositiveHaarMeasure_sigmaFinite F M A a hi I eA hc
  have hmeas : Measurable fun z : intrinsicSubgroup F A × normOneSubgroup F M =>
      s.indicator Hf (positivePointMap F M A a z.1 * (z.2 : AdelicGroupPoints F M)) :=
    (hH.indicator hs).comp (((positivePointMap F M A a).continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  rw [h1, h2, lintegral_prod _ hmeas.aemeasurable]
  congr 1
  have := LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalNormOneSubgroup F M)
  have h4 : ∀ b, ∫⁻ n, s.indicator Hf (positivePointMap F M A a b * (n : AdelicGroupPoints F M))
      ∂(Measure.haar : Measure (normOneSubgroup F M)) = B b * ∫⁻ n in s1, g n ∂Measure.haar := by
    intro b
    have ht := isFundamentalDomain_positiveSlice a hc b
      (Measure.haar : Measure (normOneSubgroup F M))
    have htm : MeasurableSet {n : normOneSubgroup F M |
        positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s} :=
      hs.preimage ((continuous_const.mul continuous_subtype_val).measurable)
    calc ∫⁻ n, s.indicator Hf (positivePointMap F M A a b * (n : AdelicGroupPoints F M))
          ∂(Measure.haar : Measure (normOneSubgroup F M))
        = ∫⁻ n, {n : normOneSubgroup F M |
            positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s}.indicator
              (fun n => B b * g n) n ∂Measure.haar := by
          refine lintegral_congr fun n => ?_
          by_cases hn : positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s
          · rw [Set.indicator_of_mem hn, Set.indicator_of_mem (show n ∈ {n : normOneSubgroup F M |
              positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s} from hn), hfac]
          · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem (show n ∉ {n : normOneSubgroup F M |
              positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s} from hn)]
      _ = ∫⁻ n in {n : normOneSubgroup F M |
            positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s}, B b * g n
              ∂Measure.haar := lintegral_indicator htm _
      _ = B b * ∫⁻ n in {n : normOneSubgroup F M |
            positivePointMap F M A a b * (n : AdelicGroupPoints F M) ∈ s}, g n
              ∂Measure.haar := lintegral_const_mul _ hg
      _ = B b * ∫⁻ n in s1, g n ∂Measure.haar := by
          rw [ht.setLIntegral_eq (LeftCosetSpace.isFundamentalDomain _ _ _) g hinv]
  rw [lintegral_congr h4, lintegral_mul_const _ hB]

end Decomposition

section Main

theorem mul_le_add_sq_aux (X x y : ℝ) (hX : 0 ≤ X) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    X * x * y ≤ X * x ^ 2 + X * y ^ 2 := by
  nlinarith [mul_nonneg hX (sq_nonneg (x - y)), mul_nonneg hX (mul_nonneg hx hy)]

theorem enorm_aux₁ {a b c d : ℝ≥0∞} (h : a * c = 1) : a * b * (c * d) = b * d := by
  calc a * b * (c * d) = (a * c) * (b * d) := by ring
    _ = b * d := by rw [h, one_mul]

theorem enorm_aux₂ {x y z w : ℝ≥0∞} (h : y * z = 1) : x * y * (z * w) = x * w := by
  calc x * y * (z * w) = x * (y * z) * w := by ring
    _ = x * w := by rw [h, mul_one]

variable {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} {π : P ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)} {hKc : IsCompact (K : Set (AdelicGroupPoints F G))}
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {β : (Fin n → ℝ) → ℝ}

/-- For `χ ∈ A^2_P`, the weighted square `β(y(m)) δ_P(m)⁻¹ χ(m k)²` is integrable on
`K × M(F) \ M(𝔸)`. -/
theorem integrable_weightedSquare (hM : IsConnectedReductive M) (ha : IsSplitComponent a)
    (hA : IsSplitTorus A.toGrp) (hlπ : l ≫ π = 𝟙 M) (μM : Measure (AdelicGroupPoints F M))
    [μM.IsHaarMeasure] (hβc : Continuous β) (hβs : HasCompactSupport β)
    {χ : AdelicGroupPoints F G → ℂ}
    (hχ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l χ) :
    Integrable (fun z : K × RationalQuotient F M =>
        (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2.out))) : ℂ) *
          parameterPower F P (-modulusParameter F P) (map F M P l z.2.out) *
          χ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) ^ 2)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
  obtain ⟨I, hIfin, ⟨eA⟩⟩ := hA
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨hi, hfi⟩ := characterRestriction F M hM A a ha
  have := hfi
  have hc : IsCentral a := ha.1.2
  have hχc : Continuous χ := hχ.1.2.1.1
  set κ := compactHaarProbability F G K hKc with hκ
  set ν := LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M) μM with hν
  set s1 := LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F M)
    (isDiscrete_rationalNormOneSubgroup F M) with hs1
  let W : K × AdelicGroupPoints F M → ℂ := fun z =>
    (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2))) : ℂ) *
      parameterPower F P (-modulusParameter F P) (map F M P l z.2) *
      χ (map F P G p (map F M P l z.2) * (z.1 : AdelicGroupPoints F G)) ^ 2
  have hWc : Continuous W :=
    ((Complex.continuous_ofReal.comp (hβc.comp ((continuous_parameterCoordinates e).comp
      ((continuous_characterLog F P).comp ((map F M P l).continuous.comp continuous_snd))))).mul
      ((continuous_parameterPower _).comp ((map F M P l).continuous.comp continuous_snd))).mul
      ((hχc.comp (((map F P G p).continuous.comp ((map F M P l).continuous.comp
        continuous_snd)).mul (continuous_subtype_val.comp continuous_fst))).pow 2)
  have hWinv : ∀ (k : K), ∀ x ∈ rationalSubgroup F M, ∀ m, W (k, x * m) = W (k, m) := by
    intro k x hx m
    have hx1 := rationalSubgroup_le_normOneSubgroup F M hx
    simp only [W]
    rw [characterLog_map_mul_left l hx1, parameterPower_map_mul_left _ l hx1,
      form_rational_mul hχ.1.1 hx]
  have hcont : Continuous (fun z : K × RationalQuotient F M => W (z.1, z.2.out)) :=
    LeftCosetSpace.continuous_out_of_invariant _ (fun k m => W (k, m)) hWc hWinv
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖W (z.1, z.2.out)‖ₑ ∂(κ.prod ν) < ∞
  have : SFinite ν := by
    rw [hν, LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
    infer_instance
  have hprodW : ∫⁻ z, ‖W (z.1, z.2.out)‖ₑ ∂(κ.prod ν) =
      ∫⁻ k, ∫⁻ q, ‖W (k, q.out)‖ₑ ∂ν ∂κ :=
    lintegral_prod _ hcont.measurable.enorm.aemeasurable
  let νp := normalizedPositiveHaarMeasure F M A a hi I eA hc
  let B : intrinsicSubgroup F A → ℝ≥0∞ := fun b => ‖(β (positiveCoordinates a e l b) : ℂ)‖ₑ
  have hBc : Continuous (fun b : intrinsicSubgroup F A =>
      (β (positiveCoordinates a e l b) : ℂ)) :=
    Complex.continuous_ofReal.comp (hβc.comp (continuous_positiveCoordinates a e l))
  have hBint : ∫⁻ b, B b ∂νp < ∞ := by
    have := normalizedPositiveHaarMeasure_isHaarMeasure F M A a hi I eA hc
    have hcs : HasCompactSupport (fun b : intrinsicSubgroup F A =>
        (β (positiveCoordinates a e l b) : ℂ)) :=
      (hasCompactSupport_positiveCoordinates a hi I eA e l hlπ hβs).comp_left
        Complex.ofReal_zero
    exact (hBc.integrable_of_hasCompactSupport hcs).hasFiniteIntegral
  have hinner : ∀ k : K, ∫⁻ q, ‖W (k, q.out)‖ₑ ∂ν =
      (Measure.haarScalarFactor μM Measure.haar : ℝ≥0∞) * ((∫⁻ b, B b ∂νp) *
        ∫⁻ n in s1, ‖χ (map F P G p (map F M P l (n : AdelicGroupPoints F M)) *
          (k : AdelicGroupPoints F G))‖ₑ ^ 2 ∂Measure.haar) := by
    intro k
    have hWk : Continuous (fun m => W (k, m)) :=
      hWc.comp (continuous_const.prodMk continuous_id)
    refine (LeftCosetSpace.lintegral_discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM (f := fun m => ‖W (k, m)‖ₑ) hWk.measurable.enorm
      (fun x hx m => congrArg _ (hWinv k x hx m))).trans ?_
    refine setLIntegral_fundamentalDomain_eq a hi I eA hc μM hWk.measurable.enorm B
      hBc.measurable.enorm ?_ ?_ ?_
    · exact (hχc.comp (((map F P G p).continuous.comp ((map F M P l).continuous.comp
        continuous_subtype_val)).mul continuous_const)).measurable.enorm.pow_const 2
    · intro b n0
      have hmemA : positivePointMap F M A a b ∈
          RestrictionSplitCentre.canonicalSubgroup F M := by
        rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup ha]
        exact ⟨b.val, b.property, rfl⟩
      simp only [W, B, positiveCoordinates]
      rw [characterLog_map_mul_right l n0.2, parameterPower_map_mul_right _ l n0.2,
        form_canonical_mul hχ.2.1 hmemA, enorm_mul, enorm_mul, enorm_pow, enorm_mul, mul_pow]
      exact enorm_aux₂ (enorm_modulus_mul_half_sq _)
    · intro g₀ n0
      show ‖χ (map F P G p (map F M P l (((g₀ : normOneSubgroup F M) : AdelicGroupPoints F M) *
          (n0 : AdelicGroupPoints F M))) * (k : AdelicGroupPoints F G))‖ₑ ^ 2 = _
      rw [form_rational_mul hχ.1.1 ((mem_rationalNormOneSubgroup_iff _).mp g₀.2)]
  rw [hprodW, lintegral_congr hinner, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    lintegral_const_mul' _ _ hBint.ne]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hBint ?_)
  let Gc : K → AdelicGroupPoints F M → ℝ≥0∞ := fun k m =>
    ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖ₑ *
      ‖χ (map F P G p (map F M P l m) * (k : AdelicGroupPoints F G))‖ₑ ^ 2
  have hGc : ∀ k : K, ∫⁻ n in s1, ‖χ (map F P G p (map F M P l (n : AdelicGroupPoints F M)) *
      (k : AdelicGroupPoints F G))‖ₑ ^ 2 ∂Measure.haar =
        ∫⁻ q, Gc k q.out ∂(RestrictionSplitCentre.canonicalMeasure F M) := by
    intro k
    have hmeasG : Measurable (Gc k) :=
      (((continuous_parameterPower _).comp (map F M P l).continuous).measurable.enorm).mul
        ((hχc.comp (((map F P G p).continuous.comp (map F M P l).continuous).mul
          continuous_const)).measurable.enorm.pow_const 2)
    have hinvG : ∀ g₀ ∈ RestrictionSplitCentre.canonicalRationalSubgroup F M, ∀ m,
        Gc k (g₀ * m) = Gc k m := by
      refine LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
        (Δ := rationalSubgroup F M) (Gc k) ?_ ?_
      · intro x hx m
        simp only [Gc]
        rw [form_canonical_mul hχ.2.1 hx, map_mul (map F M P l) x m, parameterPower_mul,
          enorm_mul, enorm_mul, mul_pow]
        exact enorm_aux₁ (enorm_modulus_mul_half_sq _)
      · intro x hx m
        simp only [Gc]
        rw [parameterPower_map_mul_left _ l (rationalSubgroup_le_normOneSubgroup F M hx),
          form_rational_mul hχ.1.1 hx]
    rw [lintegral_canonicalMeasure hmeasG hinvG]
    refine lintegral_congr fun n0 => ?_
    simp only [Gc]
    rw [parameterPower_map_of_mem_normOne _ l n0.2, enorm_one, one_mul]
  rw [lintegral_congr hGc]
  have hint := hχ.2.2
  have heq : (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
      ‖‖parameterPower F P (-modulusParameter F P) (map F M P l z.2.out)‖ *
        ‖χ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G))‖ ^ 2‖ₑ) =
      fun z => Gc z.1 z.2.out := by
    funext z
    simp only [Gc, enorm_mul, enorm_pow, enorm_norm]
  have : SFinite (RestrictionSplitCentre.canonicalMeasure F M) := by
    rw [RestrictionSplitCentre.canonicalMeasure, RestrictionSplitCentre.quotientHaarMeasure,
      normOneRationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
    infer_instance
  have hAE : AEMeasurable (fun z : K × RestrictionSplitCentre.CanonicalQuotient F M =>
      Gc z.1 z.2.out) (κ.prod (RestrictionSplitCentre.canonicalMeasure F M)) := by
    rw [← heq]
    exact hint.aestronglyMeasurable.enorm
  have hprod : ∫⁻ k, ∫⁻ q, Gc k q.out ∂(RestrictionSplitCentre.canonicalMeasure F M) ∂κ =
      ∫⁻ z, Gc z.1 z.2.out ∂(κ.prod (RestrictionSplitCentre.canonicalMeasure F M)) :=
    (lintegral_prod _ hAE).symm
  rw [hprod, ← heq]
  exact hint.hasFiniteIntegral

/-- **Absolute convergence of `(φ, ψ)_P`.** For `φ, ψ ∈ A^2_P` the integrand of
`inducedInnerProduct` is integrable on `K × M(F) \ M(𝔸)`: its norm is bounded by the sum of
the weighted squares of `φ` and `ψ`. -/
theorem integrable_inducedInnerProduct_integrand (hM : IsConnectedReductive M)
    (ha : IsSplitComponent a) (hA : IsSplitTorus A.toGrp) (hlπ : l ≫ π = 𝟙 M)
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] (hβc : Continuous β)
    (hβs : HasCompactSupport β) {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ)
    (hψ : IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l ψ) :
    Integrable (fun z : K × RationalQuotient F M =>
        (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2.out))) : ℂ) *
          parameterPower F P (-modulusParameter F P) (map F M P l z.2.out) *
          φ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) *
          (starRingEnd ℂ)
            (ψ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G))))
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
  have hφi := integrable_weightedSquare e hM ha hA hlπ μM hβc hβs hφ
  have hψi := integrable_weightedSquare e hM ha hA hlπ μM hβc hβs hψ
  have hφc : Continuous φ := hφ.1.2.1.1
  have hψc : Continuous ψ := hψ.1.2.1.1
  let V : K × AdelicGroupPoints F M → ℂ := fun z =>
    (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2))) : ℂ) *
      parameterPower F P (-modulusParameter F P) (map F M P l z.2) *
      φ (map F P G p (map F M P l z.2) * (z.1 : AdelicGroupPoints F G)) *
      (starRingEnd ℂ) (ψ (map F P G p (map F M P l z.2) * (z.1 : AdelicGroupPoints F G)))
  have hpt : Continuous (fun z : K × AdelicGroupPoints F M =>
      map F P G p (map F M P l z.2) * (z.1 : AdelicGroupPoints F G)) :=
    ((map F P G p).continuous.comp ((map F M P l).continuous.comp continuous_snd)).mul
      (continuous_subtype_val.comp continuous_fst)
  have hVc : Continuous V :=
    (((Complex.continuous_ofReal.comp (hβc.comp ((continuous_parameterCoordinates e).comp
      ((continuous_characterLog F P).comp ((map F M P l).continuous.comp continuous_snd))))).mul
      ((continuous_parameterPower _).comp ((map F M P l).continuous.comp continuous_snd))).mul
      (hφc.comp hpt)).mul (Complex.continuous_conj.comp (hψc.comp hpt))
  have hVinv : ∀ (k : K), ∀ x ∈ rationalSubgroup F M, ∀ m, V (k, x * m) = V (k, m) := by
    intro k x hx m
    have hx1 := rationalSubgroup_le_normOneSubgroup F M hx
    simp only [V]
    rw [characterLog_map_mul_left l hx1, parameterPower_map_mul_left _ l hx1,
      form_rational_mul hφ.1.1 hx, form_rational_mul hψ.1.1 hx]
  have hcont : Continuous (fun z : K × RationalQuotient F M => V (z.1, z.2.out)) :=
    LeftCosetSpace.continuous_out_of_invariant _ (fun k m => V (k, m)) hVc hVinv
  refine (hφi.norm.add hψi.norm).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_conj]
  exact mul_le_add_sq_aux _ _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    (norm_nonneg _)

end Main

end InducedInnerProductIntegrable

end Langlands.Global
