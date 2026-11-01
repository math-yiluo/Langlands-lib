import Langlands.Representation.Induction.SplitKernelCovariance
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Jacquet.Localization

/-!
# Character-twisted relative integration over a split kernel

For a split kernel `N = ker r` and a smooth character `θ` of `N` that is trivial
on `I = H ∩ N`, the relative integral `f ↦ ∫_{I\N} θ(n)⁻¹ f(n)` identifies the
`θ`-localized quotient of compact induction from `H` with the coinvariants of
the restricted inducing representation.
-/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal

universe uG uL uN uV uW

/-- Compactly induced functions are determined by their values. -/
theorem compactFunctions_eval_ext {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module ℂ V] {P : Subgroup G}
    {σ : Representation ℂ P V} {f g : CompactFunctions P σ}
    (h : ∀ x, eval P σ f.1 x = eval P σ g.1 x) : f = g :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

section Multiply

variable {N : Type uN} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The pointwise inverse of a smooth character, with the same open kernel. -/
def inverseCharacter (χ : SmoothCharacter ℂ N) : SmoothCharacter ℂ N where
  toMonoidHom := χ.toMonoidHom⁻¹
  isOpen_ker := by
    convert χ.isOpen_ker using 1
    ext g
    change (χ.toMonoidHom g)⁻¹ = 1 ↔ χ.toMonoidHom g = 1
    exact inv_eq_one

omit [IsTopologicalGroup N] in
@[simp] theorem inverseCharacter_apply (χ : SmoothCharacter ℂ N) (g : N) :
    (inverseCharacter χ).toMonoidHom g = (χ.toMonoidHom g)⁻¹ := rfl

/-- The identity map from the twist by a character that is trivial on `I`. -/
def twistTrivialIntertwining (I : Subgroup N) (χ : N →* ℂˣ) (hχ : ∀ i : I, χ i = 1)
    (σ : Representation ℂ I V) : (twist (χ.comp I.subtype) σ).IntertwiningMap σ where
  toLinearMap := LinearMap.id
  isIntertwining' i := by
    apply LinearMap.ext
    intro v
    change (χ (i : N) : ℂ) • σ i v = σ i v
    rw [hχ i, Units.val_one, one_smul]

/-- Pointwise multiplication by a smooth character that is trivial on `I`, on
compact induction from `I`. It is the published character-twist equivalence
followed by the identity coefficient map. -/
def characterMultiply (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) (σ : Representation ℂ I V) :
    CompactFunctions I σ →ₗ[ℂ] CompactFunctions I σ :=
  (compactInducedMap I (twistTrivialIntertwining I χ.toMonoidHom hχ σ)).toLinearMap ∘ₗ
    (compactInductionTwistEquiv I χ σ).toLinearEquiv.toLinearMap

@[simp] theorem eval_characterMultiply (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) (σ : Representation ℂ I V)
    (f : CompactFunctions I σ) (x : N) :
    eval I σ (characterMultiply I χ hχ σ f).1 x = (χ.toMonoidHom x : ℂ) • eval I σ f.1 x :=
  rfl

omit [IsTopologicalGroup N] in
theorem inverseCharacter_trivial {I : Subgroup N} {χ : SmoothCharacter ℂ N}
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) :
    ∀ i : I, (inverseCharacter χ).toMonoidHom i = 1 := fun i => by
  rw [inverseCharacter_apply, hχ i, inv_one]

/-- Multiplying by `χ⁻¹` undoes multiplying by `χ`. -/
theorem characterMultiply_inverse_apply (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) (σ : Representation ℂ I V)
    (f : CompactFunctions I σ) :
    characterMultiply I (inverseCharacter χ) (inverseCharacter_trivial hχ) σ
      (characterMultiply I χ hχ σ f) = f := by
  apply compactFunctions_eval_ext
  intro x
  rw [eval_characterMultiply, eval_characterMultiply, inverseCharacter_apply, smul_smul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Multiplying by `χ` undoes multiplying by `χ⁻¹`. -/
theorem characterMultiply_apply_inverse (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) (σ : Representation ℂ I V)
    (f : CompactFunctions I σ) :
    characterMultiply I χ hχ σ
      (characterMultiply I (inverseCharacter χ) (inverseCharacter_trivial hχ) σ f) = f := by
  apply compactFunctions_eval_ext
  intro x
  rw [eval_characterMultiply, eval_characterMultiply, inverseCharacter_apply, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- Right translation by `n` commutes with multiplication up to the scalar `χ(n)⁻¹`. -/
theorem characterMultiply_translate (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) (σ : Representation ℂ I V) (n : N)
    (f : CompactFunctions I σ) :
    characterMultiply I χ hχ σ (compactInduced I σ n f) =
      (((χ.toMonoidHom n)⁻¹ : ℂˣ) : ℂ) •
        compactInduced I σ n (characterMultiply I χ hχ σ f) := by
  apply compactFunctions_eval_ext
  intro x
  change (χ.toMonoidHom x : ℂ) • eval I σ f.1 (x * n) =
    (((χ.toMonoidHom n)⁻¹ : ℂˣ) : ℂ) • ((χ.toMonoidHom (x * n) : ℂ) • eval I σ f.1 (x * n))
  rw [smul_smul, map_mul, Units.val_mul, ← mul_assoc, mul_comm _ (χ.toMonoidHom x : ℂ),
    mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- Multiplication commutes with every coefficient intertwiner. -/
theorem characterMultiply_natural (I : Subgroup N) (χ : SmoothCharacter ℂ N)
    (hχ : ∀ i : I, χ.toMonoidHom i = 1) {σ : Representation ℂ I V}
    {τ : Representation ℂ I W} (T : σ.IntertwiningMap τ) (f : CompactFunctions I σ) :
    characterMultiply I χ hχ τ (compactInducedMap I T f) =
      compactInducedMap I T (characterMultiply I χ hχ σ f) := by
  apply compactFunctions_eval_ext
  intro x
  change (χ.toMonoidHom x : ℂ) • T (eval I σ f.1 x) = T ((χ.toMonoidHom x : ℂ) • eval I σ f.1 x)
  rw [map_smul]

end Multiply

section SplitKernel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L] [TopologicalSpace L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [LocallyCompactSpace G]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)
variable (θ : SmoothCharacter ℂ r.ker)
variable (hθ : ∀ i : H.comap r.ker.subtype, θ.toMonoidHom i = 1)

local notation "I" => H.comap r.ker.subtype
local notation "σI" => σ.comp (r.ker.subtype.subgroupComap H)
local notation "E" => splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ
local notation "M" => characterMultiply (H.comap r.ker.subtype) (inverseCharacter θ)
  (inverseCharacter_trivial hθ) (σ.comp (r.ker.subtype.subgroupComap H))
local notation "M'" => characterMultiply (H.comap r.ker.subtype) θ hθ
  (σ.comp (r.ker.subtype.subgroupComap H))

variable [MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
variable [BorelSpace (LeftQuotient (H.comap r.ker.subtype))]
variable (ν : Measure (LeftQuotient (H.comap r.ker.subtype))) [IsFiniteMeasureOnCompacts ν]

/-- The `θ`-twisted relative integral `f ↦ ∫_{I\N} θ(n)⁻¹ f(n)`, valued in the
actual coinvariants of the restricted inducing representation. -/
def splitKernelCharacterIntegral : CompactFunctions H σ →ₗ[ℂ] Representation.Coinvariants σI :=
  compactCoinvariantIntegral I σI ν ∘ₗ M ∘ₗ (E).toLinearEquiv.toLinearMap

theorem splitKernelCharacterIntegral_apply (f : CompactFunctions H σ) :
    splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f =
      compactCoinvariantIntegral I σI ν (M (E f)) := rfl

/-- The twisted integral is the untwisted relative integral of a modified function. -/
theorem splitKernelCharacterIntegral_eq (f : CompactFunctions H σ) :
    splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f =
      splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν ((E).symm (M (E f))) := by
  rw [splitKernelCharacterIntegral_apply]
  change _ = compactCoinvariantIntegral I σI ν (E ((E).symm (M (E f))))
  rw [(E).apply_symm_apply]

variable (hν : ∀ n : r.ker, MeasurePreserving (rightTranslate (H.comap r.ker.subtype) n) ν ν)

include hν in
/-- Kernel translation multiplies the twisted integral by `θ`. -/
theorem splitKernelCharacterIntegral_translate (n : r.ker) (f : CompactFunctions H σ) :
    splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν
        (compactInduced H σ (n : G) f) =
      (θ.toMonoidHom n : ℂ) •
        splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f := by
  rw [splitKernelCharacterIntegral_apply, splitKernelCharacterIntegral_apply,
    splitKernelCompactEquiv_translate, characterMultiply_translate, map_smul,
    compactCoinvariantIntegral_translate I σI ν hν, inverseCharacter_apply, inv_inv]

include hν in
/-- The actual `θ`-relations lie in the kernel of the twisted integral. -/
theorem relations_le_ker_splitKernelCharacterIntegral :
    Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom ≤
      LinearMap.ker (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν) :=
  (Jacquet.Localization.relations_le_ker_iff _ _ _ _).2 fun n f =>
    splitKernelCharacterIntegral_translate r s hrs hr hs H hH hsH σ hσ θ hθ ν hν n f

omit [MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
  [BorelSpace (LeftQuotient (H.comap r.ker.subtype))] in
/-- Extension after multiplication by `θ` sends ordinary kernel coinvariant
relations into the actual `θ`-relations. -/
theorem coinvariantsKer_le_comap_relations :
    Representation.Coinvariants.ker (compactInduced I σI) ≤
      (Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom).comap
        ((E).symm.toLinearEquiv.toLinearMap ∘ₗ M') := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨n, x⟩, rfl⟩
  change (E).symm (M' (compactInduced I σI n x - x)) ∈
    Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom
  have hsym : ∀ y, (E).symm (compactInduced I σI n y) = compactInduced H σ (n : G) ((E).symm y) :=
    fun y => Representation.IntertwiningMap.isIntertwining _ _ (E).symm.toIntertwiningMap n y
  rw [map_sub, map_sub, characterMultiply_translate, map_smul, hsym]
  have h := (Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom).smul_mem
    (((θ.toMonoidHom n)⁻¹ : ℂˣ) : ℂ)
    (Jacquet.Localization.sub_mem_relations (compactInduced H σ) r.ker θ.toMonoidHom n
      ((E).symm (M' x)))
  rwa [smul_sub, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h

section Bijectivity

variable [T2Space G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
  ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
variable (μN : Measure r.ker) (μI : Measure (H.comap r.ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible (H.comap r.ker.subtype) μN μI ν)

include hBasis hCompatible in
/-- The kernel of the twisted integral is exactly the span of the actual `θ`-relations. -/
theorem ker_splitKernelCharacterIntegral :
    LinearMap.ker (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν) =
      Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom := by
  apply le_antisymm
  · intro f hf
    have hb := compactCoinvariantIntegralBijective hBasis I
      (isClosed_splitKernelIntersection r H hH) μN μI ν hCompatible V σI
      (isSmooth_splitKernelInducing r H σ hσ)
    have h0 : compactCoinvariantDesc I σI ν hCompatible.right_invariant
        (Representation.Coinvariants.mk (compactInduced I σI) (M (E f))) =
        compactCoinvariantDesc I σI ν hCompatible.right_invariant 0 := by
      rw [map_zero]
      exact LinearMap.mem_ker.mp hf
    have hk := (Representation.Coinvariants.mk_eq_zero _).1 (hb.1 h0)
    have hf' := coinvariantsKer_le_comap_relations r s hrs hr hs H hH hsH σ hσ θ hθ hk
    rw [Submodule.mem_comap] at hf'
    change (E).symm (M' (M (E f))) ∈
      Jacquet.Localization.relations (compactInduced H σ) r.ker θ.toMonoidHom at hf'
    rwa [characterMultiply_apply_inverse, (E).symm_apply_apply] at hf'
  · exact relations_le_ker_splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν
      hCompatible.right_invariant

include hBasis hCompatible in
/-- The twisted integral is surjective. -/
theorem splitKernelCharacterIntegral_surjective :
    Function.Surjective (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν) := by
  intro z
  have hb := compactCoinvariantIntegralBijective hBasis I
    (isClosed_splitKernelIntersection r H hH) μN μI ν hCompatible V σI
    (isSmooth_splitKernelInducing r H σ hσ)
  obtain ⟨y, rfl⟩ := hb.2 z
  obtain ⟨φ, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  refine ⟨(E).symm (M' φ), ?_⟩
  rw [splitKernelCharacterIntegral_apply, (E).apply_symm_apply,
    characterMultiply_inverse_apply]
  rfl

/-- The `θ`-localized quotient of compact induction is the actual coinvariant
space of the restricted inducing representation. -/
def splitKernelCharacterEquiv :
    Jacquet.Localization.Coinvariants (compactInduced H σ) r.ker θ.toMonoidHom ≃ₗ[ℂ]
      Representation.Coinvariants σI :=
  LinearEquiv.ofBijective
    (Jacquet.Localization.lift (compactInduced H σ) r.ker θ.toMonoidHom
      (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν)
      (splitKernelCharacterIntegral_translate r s hrs hr hs H hH hsH σ hσ θ hθ ν
        hCompatible.right_invariant))
    ⟨by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      obtain ⟨f, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ z
      rw [Jacquet.Localization.lift_mk] at hz
      rw [Jacquet.Localization.mk_eq_zero, ← ker_splitKernelCharacterIntegral r s hrs hr hs H hH
        hsH σ hσ θ hθ ν hBasis μN μI hCompatible]
      exact LinearMap.mem_ker.mpr hz,
    by
      intro z
      obtain ⟨f, rfl⟩ := splitKernelCharacterIntegral_surjective r s hrs hr hs H hH hsH σ hσ θ hθ ν
        hBasis μN μI hCompatible z
      exact ⟨Jacquet.Localization.mk _ _ _ f, rfl⟩⟩

@[simp] theorem splitKernelCharacterEquiv_mk (f : CompactFunctions H σ) :
    splitKernelCharacterEquiv r s hrs hr hs H hH hsH σ hσ θ hθ ν hBasis μN μI hCompatible
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f) =
      splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f := rfl

end Bijectivity

section Naturality

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)

/-- The twisted integral commutes with every coefficient intertwiner. -/
theorem splitKernelCharacterIntegral_natural (f : CompactFunctions H σ) :
    splitKernelCharacterIntegral r s hrs hr hs H hH hsH τ hτ θ hθ ν (compactInducedMap H T f) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f) := by
  rw [splitKernelCharacterIntegral_apply, splitKernelCharacterIntegral_apply,
    splitKernelCompactEquiv_natural r s hrs hr hs H hH hsH hσ hτ T, characterMultiply_natural,
    compactCoinvariantIntegral_natural]

end Naturality

section Section

variable [T2Space G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable {μN : Measure r.ker} {μI : Measure (H.comap r.ker.subtype)}
variable [IsHaarMeasure μN] [μN.Regular]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible (H.comap r.ker.subtype) μN μI ν)

local notation "α" => splitKernelConjugation r s
local notation "hα" => splitKernelConjugation_mem r s H hsH

include hCompatible in
/-- Section translation of the twisted integral, for a section value whose
inverse conjugation fixes `θ`, has the actual subgroup-to-kernel Haar ratio. -/
theorem splitKernelCharacterIntegral_section (l : L)
    (hθl : ∀ n : r.ker, θ.toMonoidHom (α l n) = θ.toMonoidHom n) (f : CompactFunctions H σ) :
    letI : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν
        (compactInduced H σ (s l) f) =
      ((((mulEquivHaarChar (subgroupAutomorphism I (α l) (hα l)) /
        mulEquivHaarChar (α l) : ℝ≥0) : ℝ) : ℂ)) •
        splitKernelCoefficientAction r s H hsH σ l
          (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ hθ ν f) := by
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  set f'' := (E).symm (M (E f))
  have hB : M (E (compactInduced H σ (s l) f)) = E (compactInduced H σ (s l) f'') := by
    apply compactFunctions_eval_ext
    intro n
    rw [eval_characterMultiply, splitKernelCompactEquiv_section_eval,
      splitKernelCompactEquiv_section_eval]
    change _ = σ (splitKernelSection s H hsH l) (eval I σI (E ((E).symm (M (E f)))).1 (α l n))
    rw [(E).apply_symm_apply, eval_characterMultiply, map_smul, inverseCharacter_apply,
      inverseCharacter_apply, hθl]
  rw [splitKernelCharacterIntegral_apply r s hrs hr hs H hH hsH σ hσ θ hθ ν
      (compactInduced H σ (s l) f), hB,
    splitKernelCharacterIntegral_eq r s hrs hr hs H hH hsH σ hσ θ hθ ν f]
  exact splitKernelCompactIntegral_section (r := r) (s := s) (H := H) (hsH := hsH) (σ := σ)
    (hrs := hrs) (hr := hr) (hs := hs) (hH := hH) (hσ := hσ) (ν := ν)
    (hCompatible := hCompatible) l f''

end Section

end SplitKernel

end Langlands.Induction
