import Langlands.Automorphic.UnitaryCharacterPairing
import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeRestrictionCuspidalL2

/-! # Continuous square-integrable functions on `[G]` and the unitary pairing

For a topological group `H` and subgroups `Γ₀` and `Z`, a continuous function on `H` with
trivial character for `Z` and left `Γ₀`-invariance is the same as a continuous function on the
actual quotient `(Z ⊔ Γ₀) \ H`. Under this identification the pairing `∫ conj f * g` of
`Langlands.Automorphic.UnitaryCharacterPairing` is the inner product of `L²` of the quotient,
and positive right translation upstairs is composition with actual right translation.

For a group scheme `G` over a number field, with `Γ₀ = G(F)` and `Z` the split-centre
subgroup of the restriction quotient `[G]`, this identifies the trivial-character functions of
the pairing with the published continuous square-integrable functions on `[G]`, compatibly with
the right actions and with the published map to `L²([G])`. For the canonical quotient measure of
a connected reductive group with central split-torus data, the representation is unitarizable
and the map to `L²([G])` is injective.
-/

noncomputable section

universe u

open MeasureTheory ComplexConjugate

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] [TopologicalSpace H] [MeasurableSpace H]
  [OpensMeasurableSpace H]

/-- Open subsets of the actual quotient are measurable for the quotient measurable structure. -/
instance opensMeasurableSpace (Γ : Subgroup H) : OpensMeasurableSpace (LeftCosetSpace Γ) where
  borel_le := by
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    exact measurableSet_quotient.mpr ((hU.preimage (continuous_mk Γ)).measurableSet)

end Langlands.Global.LeftCosetSpace

namespace Langlands.Automorphic.UnitaryCharacterPairing

open Langlands.Global

section Trivial

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
variable {Γ₀ Z : Subgroup H}

/-- A function with trivial character is fixed by left multiplication by `Z ⊔ Γ₀`. -/
theorem le_leftStabilizer_of_trivial (f : CharacterFunctions Γ₀ Z 1) :
    Z ⊔ Γ₀ ≤ leftStabilizer (f.val : H → ℂ) := by
  apply sup_le_leftStabilizer
  · intro γ hγ x
    exact CharacterFunctions.rational f hγ x
  · intro z hz x
    have h := CharacterFunctions.character f ⟨z, hz⟩ x
    simpa using h

/-- A function with trivial character, as a continuous function on the actual quotient
`(Z ⊔ Γ₀) \ H`. -/
def quotientFunction (f : CharacterFunctions Γ₀ Z 1) : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ) :=
  descend Γ₀ Z f.val (le_leftStabilizer_of_trivial f)

@[simp]
theorem quotientFunction_mk (f : CharacterFunctions Γ₀ Z 1) (x : H) :
    quotientFunction f (LeftCosetSpace.mk (Z ⊔ Γ₀) x) = f.val x := rfl

theorem quotientFunction_add (f f' : CharacterFunctions Γ₀ Z 1) :
    quotientFunction (f + f') = quotientFunction f + quotientFunction f' := by
  ext q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

theorem quotientFunction_smul (c : ℂ) (f : CharacterFunctions Γ₀ Z 1) :
    quotientFunction (c • f) = c • quotientFunction f := by
  ext q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

/-- Positive right translation upstairs is actual right translation of the descended
function. -/
theorem quotientFunction_characterAction (g : H) (f : CharacterFunctions Γ₀ Z 1)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    quotientFunction (characterAction Γ₀ Z 1 g f) q =
      quotientFunction f (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g q) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

/-- The descended absolute value is the absolute value of the descended function. -/
theorem norm_quotientFunction (f : CharacterFunctions Γ₀ Z 1) (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    ‖quotientFunction f q‖ = normDensity Γ₀ Z 1 f q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

/-- The descended product is the product of the descended functions. -/
theorem pairingDensity_eq_quotientFunction (f g : CharacterFunctions Γ₀ Z 1)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    pairingDensity Γ₀ Z 1 f g q = conj (quotientFunction f q) * quotientFunction g q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

variable (Γ₀ Z) in
/-- A continuous function on the actual quotient, pulled back to a function on `H` with
trivial character. -/
def ofQuotient (φ : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)) : CharacterFunctions Γ₀ Z 1 :=
  ⟨φ.comp ⟨LeftCosetSpace.mk (Z ⊔ Γ₀), LeftCosetSpace.continuous_mk (Z ⊔ Γ₀)⟩,
    (mem_characterSubmodule Γ₀ Z 1 _).mpr
      ⟨fun γ hγ x => congrArg φ
          (LeftCosetSpace.mk_subgroup_mul (Z ⊔ Γ₀) ⟨γ, (le_sup_right : Γ₀ ≤ Z ⊔ Γ₀) hγ⟩ x),
        fun z x => by
          change φ (LeftCosetSpace.mk (Z ⊔ Γ₀) ((z : H) * x)) =
            ((1 : Z →* Circle) z : ℂ) * φ (LeftCosetSpace.mk (Z ⊔ Γ₀) x)
          rw [LeftCosetSpace.mk_subgroup_mul (Z ⊔ Γ₀)
            ⟨z, (le_sup_left : Z ≤ Z ⊔ Γ₀) z.property⟩ x]
          simp⟩⟩

@[simp]
theorem ofQuotient_val_apply (φ : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)) (x : H) :
    (ofQuotient Γ₀ Z φ).val x = φ (LeftCosetSpace.mk (Z ⊔ Γ₀) x) := rfl

theorem quotientFunction_ofQuotient (φ : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)) :
    quotientFunction (ofQuotient Γ₀ Z φ) = φ := by
  ext q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (Z ⊔ Γ₀) q
  rfl

theorem ofQuotient_quotientFunction (f : CharacterFunctions Γ₀ Z 1) :
    ofQuotient Γ₀ Z (quotientFunction f) = f := by
  apply Subtype.ext
  ext x
  rfl

variable (Γ₀ Z) in
/-- Continuous functions on `H` with trivial character are exactly continuous functions on the
actual quotient `(Z ⊔ Γ₀) \ H`. -/
def trivialCharacterEquiv :
    CharacterFunctions Γ₀ Z 1 ≃ₗ[ℂ] C(LeftCosetSpace (Z ⊔ Γ₀), ℂ) where
  toFun := quotientFunction
  map_add' := quotientFunction_add
  map_smul' := quotientFunction_smul
  invFun := ofQuotient Γ₀ Z
  left_inv := ofQuotient_quotientFunction
  right_inv := quotientFunction_ofQuotient

@[simp]
theorem trivialCharacterEquiv_apply (f : CharacterFunctions Γ₀ Z 1) :
    trivialCharacterEquiv Γ₀ Z f = quotientFunction f := rfl

@[simp]
theorem trivialCharacterEquiv_symm_apply (φ : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)) :
    (trivialCharacterEquiv Γ₀ Z).symm φ = ofQuotient Γ₀ Z φ := rfl

end Trivial

section TrivialTopological

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {Γ₀ Z : Subgroup H}

/-- The identification carries positive right translation to composition with actual right
translation. -/
theorem trivialCharacterEquiv_characterAction (g : H)
    (f : CharacterFunctions Γ₀ Z 1) :
    trivialCharacterEquiv Γ₀ Z (characterAction Γ₀ Z 1 g f) =
      (trivialCharacterEquiv Γ₀ Z f).comp
        ⟨LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g,
          LeftCosetSpace.continuous_rightTranslate (Z ⊔ Γ₀) g⟩ := by
  ext q
  exact quotientFunction_characterAction g f q

end TrivialTopological

section L2

variable {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
variable {Γ₀ Z : Subgroup H}
variable [MeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
  [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))]
variable {μ : Measure (LeftCosetSpace (Z ⊔ Γ₀))}

/-- A function with trivial character has square-integrable descended absolute value exactly
when its descended function is square integrable. -/
theorem memLp_quotientFunction_iff (f : CharacterFunctions Γ₀ Z 1) :
    MemLp (quotientFunction f) 2 μ ↔ f ∈ l2CharacterSubmodule Γ₀ Z 1 μ := by
  rw [mem_l2CharacterSubmodule,
    ← memLp_norm_iff (quotientFunction f).continuous.aestronglyMeasurable]
  have h : (fun q => ‖quotientFunction f q‖) =
      (normDensity Γ₀ Z 1 f : LeftCosetSpace (Z ⊔ Γ₀) → ℝ) :=
    funext (norm_quotientFunction f)
  rw [h]

variable (Γ₀ Z μ) in
/-- Continuous square-integrable functions on the actual quotient. -/
def quotientL2Submodule : Submodule ℂ C(LeftCosetSpace (Z ⊔ Γ₀), ℂ) where
  carrier := {φ | MemLp φ 2 μ}
  zero_mem' := MemLp.zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

omit [ContinuousMul H] [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem mem_quotientL2Submodule (φ : C(LeftCosetSpace (Z ⊔ Γ₀), ℂ)) :
    φ ∈ quotientL2Submodule Γ₀ Z μ ↔ MemLp φ 2 μ := Iff.rfl

variable (μ) in
/-- Continuous square-integrable functions on the quotient, as classes in `L²`. -/
def quotientL2ToLp : quotientL2Submodule Γ₀ Z μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun φ := φ.property.toLp φ.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [ContinuousMul H] [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
theorem coeFn_quotientL2ToLp (φ : quotientL2Submodule Γ₀ Z μ) :
    quotientL2ToLp μ φ =ᵐ[μ] (φ.val : LeftCosetSpace (Z ⊔ Γ₀) → ℂ) :=
  MemLp.coeFn_toLp φ.property

variable (hμ : RightInvariant Γ₀ Z μ)

theorem memLp_quotientFunction_toCharacter (f : L2Functions Γ₀ Z 1 μ hμ) :
    MemLp (quotientFunction (toCharacter f)) 2 μ :=
  (memLp_quotientFunction_iff _).mpr (toCharacter_mem f)

/-- A continuous square-integrable function on the quotient, pulled back to a
square-integrable function on `H` with trivial character. -/
def ofQuotientL2 (φ : quotientL2Submodule Γ₀ Z μ) : L2Functions Γ₀ Z 1 μ hμ :=
  ⟨(ofQuotient Γ₀ Z φ.val).val, (mem_l2Submodule Γ₀ Z 1 μ _).mpr
    ⟨(ofQuotient Γ₀ Z φ.val).property, (memLp_quotientFunction_iff _).mp (by
      rw [quotientFunction_ofQuotient]
      exact φ.property)⟩⟩

/-- Square-integrable functions on `H` with trivial character are exactly continuous
square-integrable functions on the actual quotient. -/
def l2QuotientEquiv : L2Functions Γ₀ Z 1 μ hμ ≃ₗ[ℂ] quotientL2Submodule Γ₀ Z μ where
  toFun f := ⟨quotientFunction (toCharacter f), memLp_quotientFunction_toCharacter hμ f⟩
  map_add' f f' := Subtype.ext (quotientFunction_add (toCharacter f) (toCharacter f'))
  map_smul' c f := Subtype.ext (quotientFunction_smul c (toCharacter f))
  invFun := ofQuotientL2 hμ
  left_inv f := Subtype.ext (by
    have h := congrArg Subtype.val (ofQuotient_quotientFunction (toCharacter f))
    exact h)
  right_inv φ := Subtype.ext (quotientFunction_ofQuotient φ.val)

@[simp]
theorem l2QuotientEquiv_apply_mk (f : L2Functions Γ₀ Z 1 μ hμ) (x : H) :
    (l2QuotientEquiv hμ f).val (LeftCosetSpace.mk (Z ⊔ Γ₀) x) = f.val x := rfl

@[simp]
theorem l2QuotientEquiv_symm_apply_val (φ : quotientL2Submodule Γ₀ Z μ) (x : H) :
    ((l2QuotientEquiv hμ).symm φ).val x = φ.val (LeftCosetSpace.mk (Z ⊔ Γ₀) x) := rfl

/-- The identification carries positive right translation to actual right translation. -/
theorem l2QuotientEquiv_l2Action (g : H) (f : L2Functions Γ₀ Z 1 μ hμ)
    (q : LeftCosetSpace (Z ⊔ Γ₀)) :
    (l2QuotientEquiv hμ (l2Action Γ₀ Z 1 μ hμ g f)).val q =
      (l2QuotientEquiv hμ f).val (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g q) :=
  quotientFunction_characterAction g (toCharacter f) q

/-- Square-integrable functions with trivial character, as classes in `L²` of the actual
quotient. -/
def toL2 : L2Functions Γ₀ Z 1 μ hμ →ₗ[ℂ] Lp ℂ 2 μ :=
  quotientL2ToLp μ ∘ₗ (l2QuotientEquiv hμ).toLinearMap

theorem toL2_apply (f : L2Functions Γ₀ Z 1 μ hμ) :
    toL2 hμ f = quotientL2ToLp μ (l2QuotientEquiv hμ f) := rfl

theorem coeFn_toL2 (f : L2Functions Γ₀ Z 1 μ hμ) :
    toL2 hμ f =ᵐ[μ] (quotientFunction (toCharacter f) : LeftCosetSpace (Z ⊔ Γ₀) → ℂ) :=
  MemLp.coeFn_toLp (memLp_quotientFunction_toCharacter hμ f)

/-- The `L²` inner product of the classes is the pairing `∫ conj f * g`. -/
theorem inner_toL2 (f g : L2Functions Γ₀ Z 1 μ hμ) :
    inner ℂ (toL2 hμ f) (toL2 hμ g) = pairing Γ₀ Z 1 μ (toCharacter f) (toCharacter g) := by
  rw [MeasureTheory.L2.inner_def, pairing]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hμ f, coeFn_toL2 hμ g] with q hf hg
  rw [hf, hg, RCLike.inner_apply', pairingDensity_eq_quotientFunction]

/-- The `L²` inner product of the classes is the invariant sesquilinear pairing. -/
theorem inner_toL2_eq_sesquilinearPairing (f g : L2Functions Γ₀ Z 1 μ hμ) :
    inner ℂ (toL2 hμ f) (toL2 hμ g) = sesquilinearPairing Γ₀ Z 1 μ hμ f g :=
  inner_toL2 hμ f g

/-- The squared `L²` norm of the class is the integral of the squared descended absolute
value. -/
theorem norm_toL2_sq (f : L2Functions Γ₀ Z 1 μ hμ) :
    ‖toL2 hμ f‖ ^ 2 = ∫ q, normDensity Γ₀ Z 1 (toCharacter f) q ^ 2 ∂μ := by
  have h := inner_toL2 hμ f f
  rw [inner_self_eq_norm_sq_to_K, pairing_self] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact h

/-- Passing to classes carries positive right translation to composition with actual right
translation. -/
theorem toL2_l2Action (g : H) (f : L2Functions Γ₀ Z 1 μ hμ) :
    toL2 hμ (l2Action Γ₀ Z 1 μ hμ g f) =
      Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate (Z ⊔ Γ₀) g) (hμ g) (toL2 hμ f) := by
  change (memLp_quotientFunction_toCharacter hμ (l2Action Γ₀ Z 1 μ hμ g f)).toLp _ =
    Lp.compMeasurePreserving _ (hμ g) ((memLp_quotientFunction_toCharacter hμ f).toLp _)
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun q => quotientFunction_characterAction g (toCharacter f) q

omit [ContinuousMul H] [OpensMeasurableSpace (LeftCosetSpace (Z ⊔ Γ₀))] in
/-- For a measure positive on nonempty open sets, continuous square-integrable functions on the
quotient are determined by their classes. -/
theorem quotientL2ToLp_injective [μ.IsOpenPosMeasure] :
    Function.Injective (quotientL2ToLp μ : quotientL2Submodule Γ₀ Z μ → Lp ℂ 2 μ) := by
  intro φ φ' h
  apply Subtype.ext
  apply ContinuousMap.coe_injective
  exact Measure.eq_of_ae_eq ((MemLp.toLp_eq_toLp_iff φ.property φ'.property).mp h)
    φ.val.continuous φ'.val.continuous

/-- For a measure positive on nonempty open sets, passing to classes is injective. -/
theorem toL2_injective [μ.IsOpenPosMeasure] : Function.Injective (toL2 hμ) :=
  (quotientL2ToLp_injective (Γ₀ := Γ₀) (Z := Z)).comp (l2QuotientEquiv hμ).injective

end L2

end Langlands.Automorphic.UnitaryCharacterPairing

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre
open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}

section L2

/-- Open subsets of `[G]` are measurable for the quotient measurable structure of `[G]`, read on
the coset space of `Z ⊔ G(F)`, which is definitionally the same space. -/
instance quotientOpensMeasurableSpace :
    @OpensMeasurableSpace
      (LeftCosetSpace (subgroup F G S j ⊔ AdelicGroupPoints.rationalSubgroup F G)) _
      (Quotient.instMeasurableSpace : MeasurableSpace (Quotient F G S j)) :=
  LeftCosetSpace.opensMeasurableSpace (rationalSubgroup F G S j)

/-- Positivity on nonempty open sets of a measure on `[G]`, read on the coset space of
`Z ⊔ G(F)`. -/
theorem isOpenPosMeasure_sup (measureQ : Measure (Quotient F G S j))
    [measureQ.IsOpenPosMeasure] :
    @Measure.IsOpenPosMeasure
      (LeftCosetSpace (subgroup F G S j ⊔ AdelicGroupPoints.rationalSubgroup F G)) _
      (Quotient.instMeasurableSpace : MeasurableSpace (Quotient F G S j)) measureQ :=
  ‹measureQ.IsOpenPosMeasure›

variable (measureQ : Measure (Quotient F G S j)) (hInv : QuotientRightInvariant F G measureQ)

/-- Continuous functions on `G(𝔸)` fixed by left multiplication by `G(F)` and by the
split-centre subgroup, whose descent to `[G]` is square integrable for `measureQ`: the
trivial-character functions of `UnitaryCharacterPairing` for `Γ₀ = G(F)`. -/
abbrev ContinuousL2Functions :=
  UnitaryCharacterPairing.L2Functions (AdelicGroupPoints.rationalSubgroup F G)
    (subgroup F G S j) 1 measureQ hInv

/-- Positive right translation by `G(𝔸)` on `ContinuousL2Functions`. -/
abbrev continuousL2Action :
    Representation ℂ (AdelicGroupPoints F G) (ContinuousL2Functions F G measureQ hInv) :=
  UnitaryCharacterPairing.l2Action (AdelicGroupPoints.rationalSubgroup F G)
    (subgroup F G S j) 1 measureQ hInv

/-- Descent identifies `ContinuousL2Functions` with the published continuous square-integrable
functions on `[G]`. -/
def continuousL2Equiv :
    ContinuousL2Functions F G measureQ hInv ≃ₗ[ℂ] quotientContinuousL2Submodule F G measureQ :=
  UnitaryCharacterPairing.l2QuotientEquiv hInv

@[simp]
theorem continuousL2Equiv_apply_mk (f : ContinuousL2Functions F G measureQ hInv)
    (x : AdelicGroupPoints F G) :
    (continuousL2Equiv F G measureQ hInv f).val (LeftCosetSpace.mk (rationalSubgroup F G S j) x) =
      f.val x := rfl

@[simp]
theorem continuousL2Equiv_symm_apply_val (φ : quotientContinuousL2Submodule F G measureQ)
    (x : AdelicGroupPoints F G) :
    ((continuousL2Equiv F G measureQ hInv).symm φ).val x =
      φ.val (LeftCosetSpace.mk (rationalSubgroup F G S j) x) := rfl

/-- Descent intertwines positive right translation upstairs with the published right action on
continuous square-integrable functions on `[G]`. -/
theorem continuousL2Equiv_continuousL2Action (g : AdelicGroupPoints F G)
    (f : ContinuousL2Functions F G measureQ hInv) :
    continuousL2Equiv F G measureQ hInv (continuousL2Action F G measureQ hInv g f) =
      quotientContinuousL2RightAction F G measureQ hInv g (continuousL2Equiv F G measureQ hInv f) := by
  apply Subtype.ext
  ext q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F G S j) q
  rfl

/-- Descent followed by the published map to `L²([G])` is the class map of
`UnitaryCharacterPairing`. -/
theorem quotientContinuousL2ToLp_continuousL2Equiv (f : ContinuousL2Functions F G measureQ hInv) :
    quotientContinuousL2ToLp F G measureQ (continuousL2Equiv F G measureQ hInv f) =
      UnitaryCharacterPairing.toL2 hInv f := rfl

/-- The class map to `L²([G])` intertwines positive right translation with the published right
regular representation. -/
theorem toL2_continuousL2Action (g : AdelicGroupPoints F G)
    (f : ContinuousL2Functions F G measureQ hInv) :
    UnitaryCharacterPairing.toL2 hInv (continuousL2Action F G measureQ hInv g f) =
      rationalQuotientL2RightAction F G measureQ hInv g (UnitaryCharacterPairing.toL2 hInv f) :=
  UnitaryCharacterPairing.toL2_l2Action hInv g f

/-- The `L²([G])` inner product of descended functions is the unitary pairing. -/
theorem inner_quotientContinuousL2ToLp_continuousL2Equiv
    (f g : ContinuousL2Functions F G measureQ hInv) :
    inner ℂ (quotientContinuousL2ToLp F G measureQ (continuousL2Equiv F G measureQ hInv f))
        (quotientContinuousL2ToLp F G measureQ (continuousL2Equiv F G measureQ hInv g)) =
      UnitaryCharacterPairing.sesquilinearPairing (AdelicGroupPoints.rationalSubgroup F G)
        (subgroup F G S j) 1 measureQ hInv f g :=
  UnitaryCharacterPairing.inner_toL2 hInv f g

end L2

section Canonical

variable (hG : IsConnectedReductive G)
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)

local notation "hμ" => quotientHaarMeasure_rightInvariant_of_connectedReductive F G hG h hi hc hT

/-- For connected reductive `G` and central split-torus data, the pairing `∫ conj f * g` is an
invariant positive definite Hermitian form for positive right translation on continuous
functions whose descent is square integrable for the canonical measure on `[G]`. -/
def reductiveContinuousL2InvariantForm :
    InvariantPositiveForm (V := ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ)
      (continuousL2Action F G (quotientHaarMeasure F G S j) hμ) :=
  haveI := quotientHaarMeasure_isOpenPosMeasure_of_connectedReductive F G hG h hi hc hT
  haveI := isOpenPosMeasure_sup F G (quotientHaarMeasure F G S j)
  UnitaryCharacterPairing.invariantPositiveForm _ _ 1 _ hμ

/-- The form is the inner product of the classes in `L²([G])`. -/
theorem reductiveContinuousL2InvariantForm_inner
    (f g : ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ) :
    (reductiveContinuousL2InvariantForm F G hG h hi hc hT).inner f g =
      inner ℂ
        (quotientContinuousL2ToLp F G (quotientHaarMeasure F G S j)
          (continuousL2Equiv F G (quotientHaarMeasure F G S j) hμ f))
        (quotientContinuousL2ToLp F G (quotientHaarMeasure F G S j)
          (continuousL2Equiv F G (quotientHaarMeasure F G S j) hμ g)) :=
  (inner_quotientContinuousL2ToLp_continuousL2Equiv F G _ hμ f g).symm

/-- Positive right translation on continuous functions with square-integrable descent to `[G]`
is unitarizable. -/
theorem isUnitarizable_reductiveContinuousL2Action :
    IsUnitarizable (V := ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ)
      (continuousL2Action F G (quotientHaarMeasure F G S j) hμ) :=
  ⟨reductiveContinuousL2InvariantForm F G hG h hi hc hT⟩

/-- For the canonical measure, the class map to `L²([G])` is injective. -/
theorem reductive_toL2_injective :
    Function.Injective (UnitaryCharacterPairing.toL2 hμ) :=
  haveI := quotientHaarMeasure_isOpenPosMeasure_of_connectedReductive F G hG h hi hc hT
  haveI := isOpenPosMeasure_sup F G (quotientHaarMeasure F G S j)
  UnitaryCharacterPairing.toL2_injective hμ

end Canonical

section SplitComponents

variable (hG : IsConnectedReductive G)
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (hj : IsSplitComponent j) (hs : IsSplitComponent i)

local notation "hμ" =>
  quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive F G hG hi hj hs

/-- For split components and connected reductive `G`, the invariant positive definite
Hermitian form `∫ conj f * g` for the canonical measure on `[G]`. -/
def splitComponentContinuousL2InvariantForm :
    InvariantPositiveForm (V := ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ)
      (continuousL2Action F G (quotientHaarMeasure F G S j) hμ) :=
  haveI := quotientHaarMeasure_isOpenPosMeasure_of_splitComponents_of_connectedReductive
    F G hG hi hj hs
  haveI := isOpenPosMeasure_sup F G (quotientHaarMeasure F G S j)
  UnitaryCharacterPairing.invariantPositiveForm _ _ 1 _ hμ

/-- The form is the inner product of the classes in `L²([G])`. -/
theorem splitComponentContinuousL2InvariantForm_inner
    (f g : ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ) :
    (splitComponentContinuousL2InvariantForm F G hG hi hj hs).inner f g =
      inner ℂ
        (quotientContinuousL2ToLp F G (quotientHaarMeasure F G S j)
          (continuousL2Equiv F G (quotientHaarMeasure F G S j) hμ f))
        (quotientContinuousL2ToLp F G (quotientHaarMeasure F G S j)
          (continuousL2Equiv F G (quotientHaarMeasure F G S j) hμ g)) :=
  (inner_quotientContinuousL2ToLp_continuousL2Equiv F G _ hμ f g).symm

/-- For split components, positive right translation on continuous functions with
square-integrable descent to `[G]` is unitarizable. -/
theorem isUnitarizable_splitComponentContinuousL2Action :
    IsUnitarizable (V := ContinuousL2Functions F G (quotientHaarMeasure F G S j) hμ)
      (continuousL2Action F G (quotientHaarMeasure F G S j) hμ) :=
  ⟨splitComponentContinuousL2InvariantForm F G hG hi hj hs⟩

/-- For split components, the class map to `L²([G])` is injective. -/
theorem splitComponent_toL2_injective :
    Function.Injective (UnitaryCharacterPairing.toL2 hμ) :=
  haveI := quotientHaarMeasure_isOpenPosMeasure_of_splitComponents_of_connectedReductive
    F G hG hi hj hs
  haveI := isOpenPosMeasure_sup F G (quotientHaarMeasure F G S j)
  UnitaryCharacterPairing.toL2_injective hμ

end SplitComponents

end Langlands.Global.RestrictionSplitCentre
