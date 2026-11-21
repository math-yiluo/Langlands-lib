import Langlands.Global.AdelicWeylFamilyCounting
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Representation.Exponents.LeviNormalizerBridge
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # The self Weyl set `Ω(P, P)`: finiteness and invariance of Lebesgue measure

For a presented parabolic `P = MU` with Levi projection `π` (`l ≫ π = 𝟙 M`), every Weyl
conjugation `(w, c)` from `P` to itself normalizes the split component `A` of `M`, and the
parameter map `λ ↦ wλ` is determined by the action of `w` on the characters of `A`. The full
Weyl image of the closed split torus `A` in `G` is finite, so `Ω(P, P)` is finite. The real
parameter maps form a finite set closed under composition and containing the identity, so each
has finite order, and in linear coordinates it preserves Lebesgue measure. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Weyl

variable {F : Type u} [Field F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M ⟶ M}

/-- A Weyl conjugation `(w, c)` from `P` to itself: conjugation by `w` restricts to the
automorphism `c⁻¹` of the Levi `l ≫ p`. -/
theorem IsWeylConjugation.inv_comp_eq_self [IsIso c] (h : IsWeylConjugation p l p l w c) :
    inv c ≫ l ≫ p = (l ≫ p) ≫ (G.innerIso w).hom := by
  rw [IsIso.inv_comp_eq]
  simp only [Category.assoc]
  rw [reassoc_of% h.comp_eq, Iso.inv_hom_id, Category.comp_id]

variable [IsAffineHom M.X.hom]

/-- A Weyl conjugation from `P` to itself normalizes the split component of the Levi. -/
theorem IsWeylConjugation.isNormalizingPoint_splitComponent [IsIso c] (ha : IsSplitComponent a)
    (h : IsWeylConjugation p l p l w c) :
    IsNormalizingPoint (a ≫ l ≫ p) w (ha.automorphismRestrictionIso (asIso c).symm) :=
  ha.isNormalizingPoint_of_normalizes (j := l ≫ p) h.inv_comp_eq_self

/-- The Weyl action of `w` on the characters of the split component is restriction along `c`. -/
theorem IsWeylConjugation.weylAction_characterRestrict [IsIso c]
    [Mono (a ≫ l ≫ p).hom.hom.left] (ha : IsSplitComponent a)
    (h : IsWeylConjugation p l p l w c) (χ : rationalCharacters M) :
    weylAction (a ≫ l ≫ p) ⟨w, _, h.isNormalizingPoint_splitComponent ha⟩
        (rationalCharacters.equivCharacterLattice A (characterRestrict a χ)) =
      rationalCharacters.equivCharacterLattice A (characterRestrict a (characterRestrict c χ)) := by
  rw [weylAction_eq (a ≫ l ≫ p) (n := ⟨w, _, h.isNormalizingPoint_splitComponent ha⟩)
    (h.isNormalizingPoint_splitComponent ha)]
  have key : ha.automorphismRestriction (asIso c).symm.symm ≫ a ≫ χ.toMul =
      a ≫ c ≫ χ.toMul := by
    rw [← Category.assoc, ha.automorphismRestriction_comp]
    rfl
  exact congrArg Additive.ofMul key

/-- Two Weyl conjugations from `P` to itself with the same action on the characters of the
split component restrict characters of `M` in the same way. -/
theorem IsWeylConjugation.characterRestrict_eq_of_weylAction_eq
    [Mono (a ≫ l ≫ p).hom.hom.left] (ha : IsSplitComponent a)
    (hinj : Function.Injective (characterRestrict a))
    {w' : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c' : M ⟶ M} [IsIso c] [IsIso c']
    (h : IsWeylConjugation p l p l w c) (h' : IsWeylConjugation p l p l w' c')
    (he : weylAction (a ≫ l ≫ p) ⟨w, _, h.isNormalizingPoint_splitComponent ha⟩ =
      weylAction (a ≫ l ≫ p) ⟨w', _, h'.isNormalizingPoint_splitComponent ha⟩) :
    characterRestrict c = characterRestrict c' := by
  refine AddMonoidHom.ext fun χ => hinj ?_
  have hχ := LinearEquiv.congr_fun he
    (rationalCharacters.equivCharacterLattice A (characterRestrict a χ))
  rw [h.weylAction_characterRestrict ha, h'.weylAction_characterRestrict ha] at hχ
  exact (rationalCharacters.equivCharacterLattice A).injective hχ

end Weyl

section Finite

variable {F : Type u} [Field F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The restriction maps `χ ↦ χ ∘ l ∘ c ∘ π` (precomposition with `π ≫ c ≫ l : P → P`) on
the characters of `P`, for the Weyl conjugations `(w, c)` from `P` to itself, form a finite
set. -/
theorem finite_selfWeylCharacterMaps (r : ParabolicRootPresentation p l a) (π : P ⟶ M) :
    {g : rationalCharacters P →+ rationalCharacters P | ∃ (w : Over.mk
        (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M ⟶ M),
        IsWeylConjugation p l p l w c ∧ characterRestrict (π ≫ c ≫ l) = g}.Finite := by
  classical
  have hM := r.isCompatible.levi.isConnectedReductive
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have ha := r.isCompatible.splitComponent
  have hpc := r.isCompatible.parabolic.isClosedSubgroup
  have hlc := r.isCompatible.levi.isClosedSubgroup.comp hpc
  have hi : IsClosedSubgroup (a ≫ l ≫ p) := ha.1.1.2.comp hlc
  have : IsClosedImmersion (a ≫ l ≫ p).hom.hom.left := hi
  have : Finite (weylImage (a ≫ l ≫ p)) := splitTorusWeylImageFinite F G A ha.1.1.1 _ hi
  have hinj := characterRestrict_injective_of_centralSplitTorusCharacter
    centralSplitTorusCharacter hM ha
  set W := {g : rationalCharacters P →+ rationalCharacters P | ∃ (w : Over.mk
        (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M ⟶ M),
        IsWeylConjugation p l p l w c ∧ characterRestrict (π ≫ c ≫ l) = g} with hW
  have hmem : ∀ s : W, ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M ⟶ M),
      IsWeylConjugation p l p l w c ∧ characterRestrict (π ≫ c ≫ l) = s.1 := fun s => s.2
  choose w c hc hs using hmem
  let f : W → weylImage (a ≫ l ≫ p) := fun s =>
    haveI := (hc s).isIso
    ⟨weylAction (a ≫ l ≫ p) ⟨w s, _, (hc s).isNormalizingPoint_splitComponent ha⟩, ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro s s' hss
    have := (hc s).isIso
    have := (hc s').isIso
    have he := congrArg Subtype.val hss
    have hcc := (hc s).characterRestrict_eq_of_weylAction_eq ha hinj (hc s') he
    apply Subtype.ext
    rw [← hs s, ← hs s', characterRestrict_comp, characterRestrict_comp, hcc,
      ← characterRestrict_comp, ← characterRestrict_comp]
  have : Finite W := Finite.of_injective f hf
  exact Set.toFinite W

variable [NumberField F]

/-- `Ω(P, P)` is finite. In Getz–Hahn §10.2, p. 273, the corresponding set `W(𝔞_M, 𝔞_M)` is
defined as the restrictions of elements of the finite Weyl group `W(G, T)(F)`; here finiteness
is proved instead from the finite full Weyl image of the split component of the Levi
(`finite_selfWeylCharacterMaps`). -/
theorem finite_weylParameterSet_self (r : ParabolicRootPresentation p l a) (π : P ⟶ M) :
    (weylParameterSet p l p l π).Finite := by
  refine ((finite_selfWeylCharacterMaps r π).image
    (fun g => AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ) g.toIntLinearMap)).subset ?_
  rintro s ⟨w, c, hc, rfl⟩
  exact ⟨_, ⟨w, c, hc, rfl⟩, rfl⟩

end Finite

section Real

variable {F : Type u} [Field F] [NumberField F] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

theorem realWeylParameter_tmul (c : M ⟶ M) (π : P ⟶ M) (s : ℝ) (χ : rationalCharacters P) :
    realWeylParameter l c π (s ⊗ₜ[ℤ] χ) = s ⊗ₜ[ℤ] characterRestrict (π ≫ c ≫ l) χ :=
  rfl

/-- Composition of real Weyl parameters. -/
theorem realWeylParameter_comp {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) (c c' : M ⟶ M) :
    (realWeylParameter (F := F) l c' π).comp (realWeylParameter l c π) =
      realWeylParameter l (c' ≫ c) π := by
  refine TensorProduct.AlgebraTensorModule.ext fun s χ => ?_
  rw [LinearMap.comp_apply, realWeylParameter_tmul, realWeylParameter_tmul,
    realWeylParameter_tmul]
  congr 1
  rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
  congr 1
  simp only [Category.assoc, reassoc_of% hlπ]

/-- The identity conjugation gives the identity on real parameters. -/
theorem realWeylParameter_id (r : ParabolicRootPresentation p l a) {π : P ⟶ M}
    (hlπ : l ≫ π = 𝟙 M) : realWeylParameter (F := F) l (𝟙 M) π = LinearMap.id := by
  have hl : Function.Injective (characterRestrict l) := by
    have h := characterRestrict_splitComponent_injective r
    rw [characterRestrict_comp, AddMonoidHom.coe_comp] at h
    exact Function.Injective.of_comp h
  refine TensorProduct.AlgebraTensorModule.ext fun s χ => ?_
  rw [realWeylParameter_tmul, LinearMap.id_apply]
  congr 1
  apply hl
  rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
  congr 2
  simp only [Category.id_comp, reassoc_of% hlπ]

theorem isWeylConjugation_one :
    IsWeylConjugation p l p l (1 : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (𝟙 M) :=
  ⟨inferInstance, by rw [innerIso_one_inv, Category.id_comp, Category.comp_id]⟩

variable [LocallyOfFiniteType G.X.hom]

/-- The real parameter maps of the Weyl conjugations from `P` to itself form a finite set. -/
theorem finite_realSelfWeylParameters (r : ParabolicRootPresentation p l a) (π : P ⟶ M) :
    {L : RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P | ∃ (w : Over.mk
        (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M ⟶ M),
        IsWeylConjugation p l p l w c ∧ realWeylParameter l c π = L}.Finite := by
  refine ((finite_selfWeylCharacterMaps r π).image
    (fun g => AlgebraTensorModule.map (LinearMap.id : ℝ →ₗ[ℝ] ℝ) g.toIntLinearMap)).subset ?_
  rintro s ⟨w, c, hc, rfl⟩
  exact ⟨_, ⟨w, c, hc, rfl⟩, rfl⟩

/-- Every real parameter map of a Weyl conjugation from `P` to itself has finite order. -/
theorem exists_pow_realWeylParameter_eq_one (r : ParabolicRootPresentation p l a) {π : P ⟶ M}
    (hlπ : l ≫ π = 𝟙 M) {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M ⟶ M}
    (h : IsWeylConjugation p l p l w c) :
    ∃ m : ℕ, 0 < m ∧ realWeylParameter l c π ^ m = 1 := by
  set L := realWeylParameter (F := F) l c π with hL
  -- powers of `L` are parameters of Weyl conjugations
  have hpow : ∀ k : ℕ, ∃ (w' : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c' : M ⟶ M),
      IsWeylConjugation p l p l w' c' ∧ realWeylParameter l c' π = L ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, 𝟙 M, isWeylConjugation_one, by rw [realWeylParameter_id r hlπ]; rfl⟩
    | succ k ih =>
      obtain ⟨w', c', hc', hk⟩ := ih
      refine ⟨w * w', c ≫ c', hc'.comp h, ?_⟩
      rw [← realWeylParameter_comp hlπ, hk, pow_succ']
      rfl
  set W := {L : RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P | ∃ (w : Over.mk
        (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M ⟶ M),
        IsWeylConjugation p l p l w c ∧ realWeylParameter l c π = L} with hW
  have : Finite W := (finite_realSelfWeylParameters r π).to_subtype
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨L ^ k, hpow k⟩ : W))
  have hEq' : L ^ i = L ^ j := congrArg Subtype.val hEq
  -- `L` is invertible
  obtain ⟨c', hc', h1, -⟩ := h.exists_symm
  set L' := realWeylParameter (F := F) l c' π
  have h3' : c' ≫ c = 𝟙 M := by
    obtain ⟨c'', -, h2, -⟩ := hc'.exists_symm
    have hc'' : c'' = c := by
      calc c'' = (c ≫ c') ≫ c'' := by rw [h1, Category.id_comp]
        _ = c ≫ (c' ≫ c'') := Category.assoc _ _ _
        _ = c := by rw [h2, Category.comp_id]
    exact hc'' ▸ h2
  have hL'L : L' * L = 1 := by
    change L'.comp L = LinearMap.id
    rw [realWeylParameter_comp hlπ, h3', realWeylParameter_id r hlπ]
  have hLL' : L * L' = 1 := by
    change L.comp L' = LinearMap.id
    rw [realWeylParameter_comp hlπ, h1, realWeylParameter_id r hlπ]
  let u : (RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P)ˣ := ⟨L, L', hLL', hL'L⟩
  have hu : u ^ i = u ^ j := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact hEq'
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have : u ^ (j - i) = 1 := by
      rw [pow_sub u hlt.le, hu, mul_inv_cancel]
    have := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have : u ^ (i - j) = 1 := by
      rw [pow_sub u hlt.le, hu, mul_inv_cancel]
    have := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

/-- In linear coordinates `e`, the real parameter map of a Weyl conjugation from `P` to itself
preserves Lebesgue measure. -/
theorem measurePreserving_realWeylParameter (r : ParabolicRootPresentation p l a)
    {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    {c : M ⟶ M} (h : IsWeylConjugation p l p l w c) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    MeasurePreserving (fun x => e.symm (realWeylParameter l c π (e x))) volume volume := by
  obtain ⟨m, hm, hLm⟩ := exists_pow_realWeylParameter_eq_one r hlπ h
  set τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    e.symm.toLinearMap ∘ₗ realWeylParameter l c π ∘ₗ e.toLinearMap with hτ
  have hτpow : ∀ k : ℕ, τ ^ k =
      e.symm.toLinearMap ∘ₗ (realWeylParameter l c π ^ k) ∘ₗ e.toLinearMap := by
    intro k
    induction k with
    | zero =>
      refine LinearMap.ext fun x => ?_
      simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      refine LinearMap.ext fun x => ?_
      simp [τ, Module.End.mul_apply]
  have hτm : τ ^ m = 1 := by
    rw [hτpow, hLm]
    refine LinearMap.ext fun x => ?_
    simp
  have hdet : |LinearMap.det τ| = 1 := by
    have h1 : LinearMap.det τ ^ m = 1 := by rw [← map_pow, hτm, map_one]
    have h2 : |LinearMap.det τ| ^ m = 1 := by rw [← abs_pow, h1, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm.ne').mp h2
  have hdet0 : LinearMap.det τ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨(LinearMap.continuous_of_finiteDimensional τ).measurable, ?_⟩
  change Measure.map τ volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, abs_inv, hdet, inv_one,
    ENNReal.ofReal_one, one_smul]

end Real

end Langlands.Global.AdelicGroupPoints
