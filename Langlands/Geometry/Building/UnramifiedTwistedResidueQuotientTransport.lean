import Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientStatement
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction

/-! # Reduction of the twisted residue quotient to apartment points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace TwistedResidueQuotientTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))

/-- The conclusion of `UnramifiedTwistedResidueQuotientStatement` for one building `B`,
one automorphism `φ`, one twisting element `cφ` (the value of the cocycle at `φ`) and
one point `y`. -/
def Conclusion (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (cφ : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (y : B.ReducedBuilding) : Prop :=
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  letI : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  letI : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
    ∃ (P : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
      (q : P →* (Over.mk (𝟙 (Spec (CommRingCat.of
          (IsLocalRing.ResidueField (fixedFieldIntegers F))))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap 𝓀[F]
          (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj R).X))
      (θP : P → P),
      P ≤ B.fixer y ∧
      Function.Surjective q ∧
      (∀ g : P, (θP g : rationalPoints (baseChanged F (inertiaFixedField F) G)) =
        cφ * rationalConjugate F (inertiaFixedField F) G φ g * cφ⁻¹) ∧
      (∀ g : P, q (θP g) =
        descentBasePoint
          (algebraBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
          (galoisBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
            (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
              (IsLocalRing.ResidueField (fixedFieldIntegers F))))
          (galoisBaseMap_over 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
            (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
              (IsLocalRing.ResidueField (fixedFieldIntegers F))))
          R (q g)) ∧
      (∀ Y : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y →
        ∀ g : P, q g = 1 →
          ((g : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y = Y) ∧
      (∀ Y Y' : Set B.ReducedBuilding,
        B.HasChamberClosurePresentation Y y → B.HasChamberClosurePresentation Y' y →
        ∃ h : P, Y' = ((h : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y)

variable {B}

/-- Translating a set by `a` and then by `b` is translating by `b * a`. -/
theorem image_smul_image_smul (a b : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Y : Set B.ReducedBuilding) :
    (b • ·) '' ((a • ·) '' Y) = ((b * a) • ·) '' Y := by
  rw [Set.image_image]
  simp only [mul_smul]

set_option maxHeartbeats 1000000 in
/-- **Transport along a translation.** The conclusion at `y` for the twisting element
`g₀⁻¹ * cφ * φ(g₀)` gives the conclusion at `g₀ • y` for `cφ`, by conjugating the subgroup,
the reduction map and the twist by `g₀`. -/
theorem Conclusion.smul (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (cφ g₀ : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (y : B.ReducedBuilding)
    (h : Conclusion B φ (g₀⁻¹ * cφ * rationalConjugate F (inertiaFixedField F) G φ g₀) y) :
    Conclusion B φ cφ (g₀ • y) := by
  obtain ⟨R, hR, P, q, θ, hPfix, hq, hθ, hfrob, hker, htrans⟩ := h
  let e := (MulAut.conj g₀).subgroupMap P
  have he_coe : ∀ g : P, ((e g : P.map (MulAut.conj g₀ :
      rationalPoints (baseChanged F (inertiaFixedField F) G) →*
        rationalPoints (baseChanged F (inertiaFixedField F) G))) :
        rationalPoints (baseChanged F (inertiaFixedField F) G)) =
      g₀ * (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) * g₀⁻¹ :=
    fun g => rfl
  have he_symm : ∀ g, g = e (e.symm g) := fun g => (e.apply_symm_apply g).symm
  refine ⟨R, hR, _, q.comp e.symm.toMonoidHom, fun g => e (θ (e.symm g)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the conjugated subgroup fixes the translated point
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    rw [B.mem_fixer]
    have hpy : p • y = y := B.mem_fixer.mp (hPfix hp)
    change (g₀ * p * g₀⁻¹) • g₀ • y = g₀ • y
    rw [mul_smul, mul_smul, inv_smul_smul, hpy]
  · exact hq.comp e.symm.surjective
  · intro g
    rw [he_coe, hθ]
    conv_rhs => rw [he_symm g, he_coe]
    simp only [map_mul, map_inv]
    group
  · intro g
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply]
    exact hfrob _
  · intro Y hY g hg
    have hY' : B.HasChamberClosurePresentation ((g₀⁻¹ • ·) '' Y) y := by
      have := hY.smul g₀⁻¹
      rwa [inv_smul_smul] at this
    have hfix := hker _ hY' (e.symm g) hg
    rw [he_symm g, he_coe, ← image_smul_image_smul, ← image_smul_image_smul, hfix,
      image_smul_image_smul, mul_inv_cancel]
    simp only [one_smul, Set.image_id']
  · intro Y Y' hY hY'
    have h₁ : B.HasChamberClosurePresentation ((g₀⁻¹ • ·) '' Y) y := by
      have := hY.smul g₀⁻¹
      rwa [inv_smul_smul] at this
    have h₂ : B.HasChamberClosurePresentation ((g₀⁻¹ • ·) '' Y') y := by
      have := hY'.smul g₀⁻¹
      rwa [inv_smul_smul] at this
    obtain ⟨p, hp⟩ := htrans _ _ h₁ h₂
    refine ⟨e p, ?_⟩
    rw [he_coe, ← image_smul_image_smul, ← image_smul_image_smul, ← hp,
      image_smul_image_smul, mul_inv_cancel]
    simp only [one_smul, Set.image_id']

/-! ### Cohomologous cocycles -/

variable (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (g₀ : rationalPoints (baseChanged F (inertiaFixedField F) G))

/-- The cocycle `σ ↦ g₀⁻¹ * c σ * σ(g₀)`, cohomologous to `c`. -/
def twistCocycle (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    rationalPoints (baseChanged F (inertiaFixedField F) G) :=
  g₀⁻¹ * c σ * rationalConjugate F (inertiaFixedField F) G σ g₀

omit [IsAffineHom G.X.hom] in
/-- A cohomologous function of a crossed homomorphism is a crossed homomorphism. -/
theorem twistCocycle_mul
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (σ τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    twistCocycle c g₀ (σ * τ) =
      twistCocycle c g₀ σ *
        rationalConjugate F (inertiaFixedField F) G σ (twistCocycle c g₀ τ) := by
  simp only [twistCocycle, hc, rationalConjugate_mul, map_mul, map_inv]
  group

/-- The cohomologous function is trivial on the fixing subgroup of a finite subextension,
when `c` is and `G` is locally of finite type. -/
theorem exists_twistCocycle_eq_one [LocallyOfFiniteType G.X.hom]
    (hcE : ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) :
    ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, twistCocycle c g₀ σ = 1 := by
  obtain ⟨Ec, hEc, hcfix⟩ := hcE
  obtain ⟨Eg, hEg, hgfix⟩ :=
    TwistedGeneratorReduction.exists_finite_fixing_rationalPoints F (inertiaFixedField F)
      (G := G) (fun _ : PUnit.{u + 1} => g₀)
  refine ⟨Ec ⊔ Eg, IntermediateField.finiteDimensional_sup _ _, fun σ hσ => ?_⟩
  rw [twistCocycle, hcfix σ (IntermediateField.fixingSubgroup_le le_sup_left hσ),
    hgfix σ (IntermediateField.fixingSubgroup_le le_sup_right hσ) PUnit.unit, mul_one,
    inv_mul_cancel]

/-- If `g₀ • z` is fixed by the `c`-twisted action, then `z` is fixed by the action twisted
by the cohomologous cocycle. -/
theorem twistCocycle_smul_action
    (A : MaximalUnramified.SemilinearApartmentData B)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (z : B.ReducedBuilding)
    (hz : c σ • A.action σ (g₀ • z) = g₀ • z) :
    twistCocycle c g₀ σ • A.action σ z = z := by
  rw [MaximalUnramified.SemilinearApartmentData.action_smul] at hz
  rw [twistCocycle, mul_smul, mul_smul, hz, inv_smul_smul]

end TwistedResidueQuotientTransport

open TwistedResidueQuotientTransport

/-- `UnramifiedTwistedResidueQuotientStatement` restricted to points of the standard
apartment: the same hypotheses, with the twisted-fixed point `y` replaced by
`apartmentMap x` for an apartment point `x`, and the same conclusion. -/
def UnramifiedTwistedResidueQuotientApartmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
        (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          rationalPoints (baseChanged F (inertiaFixedField F) G)),
        (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
        (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
          ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
        ∀ x : (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).Apartment,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            c σ • (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ
                ((UnramifiedBuildingDescent.buildingData iT
                  (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                  hiT D C h6).apartmentMap x) =
              (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).apartmentMap x) →
          ∀ φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (∀ x : fixedFieldIntegers F,
              IsLocalRing.residue (fixedFieldIntegers F)
                  (Langlands.GroupScheme.Descent.FiniteUnramified.fixedFieldIntegerAut
                    F φ x) =
                IsLocalRing.residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) →
            Conclusion
              (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6)
              φ (c φ)
              ((UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).apartmentMap x)

/-- The residue-quotient statement at apartment points implies it at every twisted-fixed
point. -/
def UnramifiedTwistedResidueQuotientApartmentReductionStatement : Prop :=
  UnramifiedTwistedResidueQuotientApartmentStatement.{u} →
    UnramifiedTwistedResidueQuotientStatement.{u}

set_option maxHeartbeats 1600000 in
/-- **Reduction to apartment points.** Write the twisted-fixed point as `g₀ • apartmentMap x`,
apply the apartment statement to the cohomologous cocycle `σ ↦ g₀⁻¹ * c σ * σ(g₀)`, and
conjugate its data back by `g₀`. -/
theorem unramifiedTwistedResidueQuotientApartmentReduction :
    UnramifiedTwistedResidueQuotientApartmentReductionStatement.{u} := by
  intro hA F _ _ _ _ G hG T iT
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let _ := mono_of_isMaximalSplitTorus hiT
  let _ : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hcE y hy
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨g₀, x, rfl⟩ := (UnramifiedBuildingDescent.buildingData iT
    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
    hiT D C h6).exists_smul_apartmentMap y
  intro φ hφ
  exact Conclusion.smul φ (c φ) g₀ _
    (hA F G hG T iT hiT D C h6 hD (twistCocycle c g₀) (twistCocycle_mul c g₀ hc)
      (exists_twistCocycle_eq_one c g₀ hcE) x
      (fun σ => twistCocycle_smul_action c g₀ _ σ _ (hy σ)) φ hφ)

end Langlands.Geometry.Building
