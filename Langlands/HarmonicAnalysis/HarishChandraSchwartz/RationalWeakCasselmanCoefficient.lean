import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermLinearProjection
import Langlands.Representation.Aubert.General.UnitaryOppositeJacquet
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.SelectedWeightSplitting
import Langlands.Representation.Jacquet.StandardTensorConstantTerm

/-! # Weak constant term of a normalized Casselman coefficient -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

section Projection

variable {M : Type*} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {A : Type*} [CommGroup A]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]
  (j : A →* M) (hj : ∀ a, j a ∈ Subgroup.center M)

/-- The sum of the generalized weight spaces with unitary component character. -/
abbrev unitaryWeightPart (ρ : Representation ℂ M V) : Subrepresentation ρ :=
  selectedWeightPart ρ j hj (fun χ => ∀ a, ‖(χ a : ℂ)‖ = 1)

/-- The sum of the remaining generalized weight spaces. -/
abbrev nonunitaryWeightPart (ρ : Representation ℂ M V) : Subrepresentation ρ :=
  selectedWeightPart ρ j hj (fun χ => ¬ ∀ a, ‖(χ a : ℂ)‖ = 1)

/-- In an admissible representation the unitary and nonunitary parts are complementary. -/
theorem isCompl_unitaryWeightPart (ρ : Representation ℂ M V) (hρ : IsAdmissible ρ) :
    IsCompl (unitaryWeightPart j hj ρ).toSubmodule (nonunitaryWeightPart j hj ρ).toSubmodule :=
  ⟨selectedWeightPart_disjoint ρ j hj _ hρ.1,
    selectedWeightPart_codisjoint ρ j hj _
      (generalizedWeightSpace_iSup_eq_top ρ j hj hρ.1
        (CentralDecomposition.admissible_centerFinite ρ hρ))⟩

/-- The equivariant projection to the unitary part along the nonunitary part. -/
def unitaryWeightProjection (ρ : Representation ℂ M V) (hρ : IsAdmissible ρ) :
    ρ.IntertwiningMap (unitaryWeightPart j hj ρ).toRepresentation :=
  subrepresentationProjection _ _ (isCompl_unitaryWeightPart j hj ρ hρ)

omit [WeaklyLocallyCompactSpace M] in
private theorem map_mem_of_selectedWeightPart
    (ρ : Representation ℂ M V) (P : (A →* ℂˣ) → Prop)
    (L : V →ₗ[ℂ] W) (U : Submodule ℂ W)
    (hL : ∀ χ, P χ → (generalizedWeightSpace ρ j χ hj).toSubmodule ≤ U.comap L)
    {v : V} (hv : v ∈ selectedWeightPart ρ j hj P) :
    L v ∈ U := by
  have hle : (selectedWeightPart ρ j hj P).toSubmodule ≤ U.comap L := by
    rw [selectedWeightPart_toSubmodule]
    exact iSup_le fun χ => iSup_le (hL χ)
  exact hle hv

private def coefficientLinearMap (ρ : Representation ℂ M V) (ℓ : V →ₗ[ℂ] ℂ) :
    V →ₗ[ℂ] (M → ℂ) where
  toFun v m := ℓ (ρ m v)
  map_add' v w := funext fun m => by simp
  map_smul' c v := funext fun m => by simp

private theorem coefficient_mem_exponentSpace_of_selectedWeightPart
    (ρ : Representation ℂ M V) (hρ : IsSmooth ρ) (ℓ : V →ₗ[ℂ] ℂ) (P : (A → ℂ) → Prop)
    {v : V} (hv : v ∈ selectedWeightPart ρ j hj (fun χ => P (fun a => (χ a : ℂ)))) :
    (fun m => ℓ (ρ m v)) ∈ ⨆ χ : A → ℂ, ⨆ (_ : P χ),
      jointGenEigenspace (componentRightTranslation j) χ := by
  refine map_mem_of_selectedWeightPart j hj ρ _ (coefficientLinearMap ρ ℓ) _ ?_ hv
  intro χ hχ y hy
  obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth j χ hj hρ y).mp hy
  exact Submodule.mem_iSup_of_mem (fun a => (χ a : ℂ)) (Submodule.mem_iSup_of_mem hχ
    (coefficient_mem_jointGenEigenspace j ρ ℓ
      (mem_jointGenEigenspace.mpr fun a => ⟨d, hd a⟩)))

/-- The weak projection of a coefficient selects the unitary component of its source vector. -/
theorem weakPart_coefficient_eq_unitaryWeightProjection
    (ρ : Representation ℂ M V) (hρ : IsAdmissible ρ) (ℓ : V →ₗ[ℂ] ℂ) (v : V) :
    weakPart j (fun m => ℓ (ρ m v)) =
      fun m => ℓ (ρ m (unitaryWeightProjection j hj ρ hρ v : V)) := by
  let U := unitaryWeightPart j hj ρ
  let N := nonunitaryWeightPart j hj ρ
  let h := isCompl_unitaryWeightPart j hj ρ hρ
  let v₀ : V := unitaryWeightProjection j hj ρ hρ v
  let v₁ : V := subrepresentationProjection N U h.symm v
  have hv₀ : v₀ ∈ U := (unitaryWeightProjection j hj ρ hρ v).property
  have hv₁ : v₁ ∈ N := (subrepresentationProjection N U h.symm v).property
  have hsum : v₀ + v₁ = v := subrepresentationProjection_add U N h v
  have hd : (fun m => ℓ (ρ m v)) - (fun m => ℓ (ρ m v₀)) = fun m => ℓ (ρ m v₁) := by
    funext m
    rw [Pi.sub_apply, ← map_sub, ← map_sub, ← eq_sub_of_add_eq' hsum]
  apply weakPart_eq_of_mem j
  · exact coefficient_mem_exponentSpace_of_selectedWeightPart j hj ρ hρ.1 ℓ
      (· ∈ unitaryExponents A) hv₀
  · rw [hd]
    exact coefficient_mem_exponentSpace_of_selectedWeightPart j hj ρ hρ.1 ℓ
      (· ∉ unitaryExponents A) hv₁

private theorem pairingCoefficient_mem_positiveExponentSpace
    (ρ : Representation ℂ M V) (τ : Representation ℂ M W) (hτ : IsSmooth τ)
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hb : ∀ m x y, b (τ m x) (ρ m y) = b x y)
    (y : V) {x : W} (hx : x ∈ nonunitaryWeightPart j hj τ) :
    (fun m => b x (ρ m y)) ∈ positiveExponentSpace j := by
  let L : W →ₗ[ℂ] (M → ℂ) :=
    { toFun := fun z m => b z (ρ m y)
      map_add' := fun z z' => funext fun m => by simp
      map_smul' := fun c z => funext fun m => by simp }
  have htranslate (a : A) (z : W) :
      componentRightTranslation j a (L z) = L (τ (j a⁻¹) z) := by
    funext m
    have hm := hb (j a) (τ (j a⁻¹) z) (ρ m y)
    have hcancel : τ (j a) (τ (j a⁻¹) z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rfl
    rw [hcancel, ← Module.End.mul_apply, ← map_mul,
      ← Subgroup.mem_center_iff.mp (hj a) m] at hm
    rw [componentRightTranslation_apply]
    exact hm
  refine map_mem_of_selectedWeightPart j hj τ _ L _ ?_ hx
  intro χ hχ z hz
  obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth j χ hj hτ z).mp hz
  let χinv : A → ℂ := fun a => (χ a⁻¹ : ℂ)
  have hχinv : χinv ∉ unitaryExponents A := by
    intro h
    apply hχ
    intro a
    simpa only [χinv, inv_inv] using h a⁻¹
  change L z ∈ positiveExponentSpace j
  refine Submodule.mem_iSup_of_mem χinv (Submodule.mem_iSup_of_mem hχinv ?_)
  refine mem_jointGenEigenspace.mpr fun a => ⟨d, ?_⟩
  have hshift (w : W) :
      (componentRightTranslation j a - χinv a • 1) (L w) =
        L ((τ (j a⁻¹) - χinv a • 1) w) := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, htranslate]
  have hpow (k : ℕ) (w : W) :
      ((componentRightTranslation j a - χinv a • 1) ^ k) (L w) =
        L (((τ (j a⁻¹) - χinv a • 1) ^ k) w) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hshift]
  change ((componentRightTranslation j a - χinv a • 1) ^ d) (L z) = 0
  rw [hpow, hd a⁻¹, map_zero]

/-- For an invariant pairing the weak coefficient uses the unitary parts on both sides. -/
theorem weakPart_pairingCoefficient_eq_unitaryWeightProjections
    (ρ : Representation ℂ M V) (τ : Representation ℂ M W)
    (hρ : IsAdmissible ρ) (hτ : IsAdmissible τ)
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hb : ∀ m x y, b (τ m x) (ρ m y) = b x y) (x : W) (y : V) :
    weakPart j (fun m => b x (ρ m y)) =
      fun m => b (unitaryWeightProjection j hj τ hτ x : W)
        (ρ m (unitaryWeightProjection j hj ρ hρ y : V)) := by
  rw [weakPart_coefficient_eq_unitaryWeightProjection j hj ρ hρ (b x)]
  let y₀ : V := unitaryWeightProjection j hj ρ hρ y
  let x₀ : W := unitaryWeightProjection j hj τ hτ x
  have hx : x - x₀ ∈ nonunitaryWeightPart j hj τ := by
    let U := unitaryWeightPart j hj τ
    let N := nonunitaryWeightPart j hj τ
    let h := isCompl_unitaryWeightPart j hj τ hτ
    have hs := subrepresentationProjection_add U N h x
    change x₀ + (subrepresentationProjection N U h.symm x : W) = x at hs
    rw [← eq_sub_of_add_eq' hs]
    exact (subrepresentationProjection N U h.symm x).property
  have hw : (fun m => b (x - x₀) (ρ m y₀)) ∈ weakExponentSpace j :=
    coefficient_mem_exponentSpace_of_selectedWeightPart j hj ρ hρ.1 (b (x - x₀))
      (· ∈ unitaryExponents A) (unitaryWeightProjection j hj ρ hρ y).property
  have hp := pairingCoefficient_mem_positiveExponentSpace j hj ρ τ hτ.1 b hb y₀ hx
  have hzero := Submodule.disjoint_def.mp (disjoint_weakExponentSpace_positiveExponentSpace j)
    _ hw hp
  funext m
  exact sub_eq_zero.mp (by
    simpa only [map_sub, LinearMap.sub_apply, Pi.zero_apply] using congrFun hzero m)

end Projection

end Langlands.HarishChandraSchwartz

open scoped NNReal TensorProduct

namespace Langlands.Jacquet.StablePairingData

open HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (D : StablePairingData G) (ρ : Representation ℂ G V)
  (δ : D.M →* ℝ≥0ˣ)

/-- The normalization on the opposite quotient in the stable pairing. -/
def oppositeNormalizedAction : Representation ℂ D.M (Coinvariants (smoothContragredient ρ) D.N) :=
  characterTwistedAction (smoothContragredient ρ) D.N D.M D.hMN (inverseHalfCharacter δ)⁻¹

/-- The two Iwahori contraction orientations give admissibility of the normalized Jacquet actions. -/
theorem normalizedActions_isAdmissible (hρ : IsAdmissible ρ)
    (hBasis : HasOppositeIwahoriContractionBasis D.N D.M D.Nbar D.g)
    (hδ : IsOpen (δ.ker : Set D.M)) :
    IsAdmissible (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ) ∧
      IsAdmissible (D.oppositeNormalizedAction ρ δ) := by
  have hDual := isAdmissible_smoothContragredient_of_compact_cofinal
    (compactOpenCofinal_of_oppositeIwahoriContractionBasis hBasis) ρ hρ
  refine ⟨isAdmissible_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ hδ hρ.1
    (isAdmissible_action_of_iwahoriContraction ρ hρ D.Nbar D.M D.N D.hMNbar
      hBasis.symm.hasIwahoriContractionBasis), ?_⟩
  exact (isAdmissible_twist_iff (inverseHalfCharacter δ)⁻¹
    (action (smoothContragredient ρ) D.N D.M D.hMN)
    (isOpen_ker_inv (χ := inverseHalfCharacter δ) (isOpen_ker_inverseHalfCharacter δ hδ))).mpr
    (isAdmissible_action_of_iwahoriContraction (smoothContragredient ρ) hDual
      D.N D.M D.Nbar D.hMN hBasis.hasIwahoriContractionBasis)

variable {D ρ}
  {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- Stable evaluation is invariant under the reciprocal half-modulus twists. -/
theorem IsStablePairing.map_normalizedAction {hρ : IsSmooth ρ} (hAd : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (m : D.M)
    (x : Coinvariants (smoothContragredient ρ) D.N) (y : Coinvariants ρ D.Nbar) :
    b (D.oppositeNormalizedAction ρ δ m x)
      (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ m y) = b x y := by
  let c := inverseHalfCharacter δ m
  change b ((↑(c⁻¹) : ℂ) • action (smoothContragredient ρ) D.N D.M D.hMN m x)
    ((c : ℂ) • action ρ D.Nbar D.M D.hMNbar m y) = b x y
  simp only [map_smul, LinearMap.smul_apply, smul_smul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_smul, hb.map_action hAd]

variable [NonarchimedeanGroup D.M] [WeaklyLocallyCompactSpace D.M]
  {A : Type*} [CommGroup A] (j : A →* D.M) (hj : ∀ a, j a ∈ Subgroup.center D.M)
  (hr : IsAdmissible (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ))
  (hl : IsAdmissible (D.oppositeNormalizedAction ρ δ))

/-- The coefficient of the two projected normalized Jacquet classes, extended linearly to tensors. -/
def unitaryCoefficientTensorConstantTerm (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
    Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ) : V ⊗[ℂ] SmoothDual ρ →ₗ[ℂ] (D.M → ℂ) :=
  let R := normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ
  let L := D.oppositeNormalizedAction ρ δ
  let p := unitaryWeightProjection j hj R hr
  let q := unitaryWeightProjection j hj L hl
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun v ℓ m => b (q (Jacquet.mk (smoothContragredient ρ) D.N ℓ) :
      Coinvariants (smoothContragredient ρ) D.N) (R m (p (Jacquet.mk ρ D.Nbar v) :
        Coinvariants ρ D.Nbar)))
    (by intro v w ℓ; ext m; simp)
    (by intro c v ℓ; ext m; simp)
    (by intro v ℓ k; ext m; simp)
    (by intro c v ℓ; ext m; simp))

/-- The weak projection of the tensor constant term uses the unitary Jacquet classes. -/
theorem weakPart_coefficientTensorConstantTerm_eq_unitary
    {hρ : IsSmooth ρ} (hAd : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b)
    (hfin : ∀ t, IsRightFinite j.range (D.coefficientTensorConstantTerm ρ b δ t))
    (t : V ⊗[ℂ] SmoothDual ρ) :
    weakPart j (D.coefficientTensorConstantTerm ρ b δ t) =
      unitaryCoefficientTensorConstantTerm δ j hj hr hl b t := by
  let CT := (D.coefficientTensorConstantTerm ρ b δ).codRestrict
    (weakExponentSpace j ⊔ positiveExponentSpace j) (fun s => mem_sup_of_isRightFinite _ (hfin s))
  change ((weakPartLinear j).comp CT) t = _
  suffices h : (weakPartLinear j).comp CT = unitaryCoefficientTensorConstantTerm δ j hj hr hl b by
    rw [h]
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro ℓ
  change weakPart j (D.coefficientConstantTerm ρ b δ ℓ v) = _
  exact weakPart_pairingCoefficient_eq_unitaryWeightProjections j hj _ _ hr hl b
    (hb.map_normalizedAction δ hAd) _ _

end Langlands.Jacquet.StablePairingData

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Jacquet Langlands.Plancherel Langlands.HarishChandraSchwartz

namespace Langlands.BruhatTits.SpecialCompact

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B) {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)
  (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)

include hρ in
/-- Admissibility of the ordinary normalized Jacquet object and the reciprocally normalized
opposite quotient of the smooth dual, for the same standard parabolic. -/
theorem standardCasselmanPairingData_normalizedActions_isAdmissible :
    let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
    IsAdmissible (normalizedActionOfModulus ρ.representation D.Nbar D.M D.hMNbar
      (standardRadicalModulus i ν J)) ∧
      IsAdmissible (D.oppositeNormalizedAction ρ.representation (standardRadicalModulus i ν J)) :=
  (standardCasselmanPairingData hG hi hν hζ hB hA hmem).normalizedActions_isAdmissible
    ρ.representation (standardRadicalModulus i ν J) hρ
    (hasOppositeIwahoriContractionBasis_standard hi hζ hB hA hmem)
    isOpen_ker_standardRadicalModulus

/-- Waldspurger's weak coefficient formula for the actual standard constant term of a tensor. -/
def StandardWeakTensorCasselmanStatement : Prop :=
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  letI : WeaklyLocallyCompactSpace D.M := by
    change WeaklyLocallyCompactSpace (standardLeviPoints i ν J)
    let : LocallyCompactSpace (standardLeviPoints i ν J) :=
      (isClosed_standardLeviPoints i ν J).locallyCompactSpace
    infer_instance
  let hadm := standardCasselmanPairingData_normalizedActions_isAdmissible hG hi hν hζ hB hA hmem ρ hρ
  let hj (a : rationalPoints A.toGrp) : standardComponentHom hA a ∈ Subgroup.center D.M :=
    Subgroup.mem_center_iff.mpr fun m => (standardComponentHom_commute hA a m).symm
  ∀ (b : Coinvariants (smoothContragredient ρ.representation) D.N →ₗ[ℂ]
        Coinvariants ρ.representation D.Nbar →ₗ[ℂ] ℂ),
    D.IsStablePairing ρ.representation ρ.isSmooth b → ∀ t : CoefficientTensor ρ,
      weakPart (standardComponentHom hA)
          (standardConstantTerm hA (fun g => coefficientTensorMap ρ t g)) =
        StablePairingData.unitaryCoefficientTensorConstantTerm (D := D) (ρ := ρ.representation)
          (standardRadicalModulus i ν J)
          (standardComponentHom hA) hj hadm.1 hadm.2 b t

/-- The chosen constant term is the stable tensor coefficient, so its weak projection is
computed by the two unitary Jacquet projections. -/
theorem standardWeakTensorCasselman :
    StandardWeakTensorCasselmanStatement hG hi hν hζ hB hA hmem ρ hρ := by
  intro b hb t
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  let : WeaklyLocallyCompactSpace D.M := by
    change WeaklyLocallyCompactSpace (standardLeviPoints i ν J)
    let : LocallyCompactSpace (standardLeviPoints i ν J) :=
      (isClosed_standardLeviPoints i ν J).locallyCompactSpace
    infer_instance
  let hadm := standardCasselmanPairingData_normalizedActions_isAdmissible hG hi hν hζ hB hA hmem ρ hρ
  have hj (a : rationalPoints A.toGrp) : standardComponentHom hA a ∈ Subgroup.center D.M :=
    Subgroup.mem_center_iff.mpr fun m => (standardComponentHom_commute hA a m).symm
  rw [standardConstantTerm_coefficientTensorMap hG hi hν hζ hB hA hmem ρ hρ hb t]
  exact StablePairingData.weakPart_coefficientTensorConstantTerm_eq_unitary
    (D := D) (ρ := ρ.representation)
    (standardRadicalModulus i ν J) (standardComponentHom hA) hj hadm.1 hadm.2
    (standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ.representation hρ) hb
    (fun s => (coefficientTensorConstantTerm_spec hG hi hν hζ hB hA hmem ρ hρ hb s).1) t

end Langlands.BruhatTits.SpecialCompact
