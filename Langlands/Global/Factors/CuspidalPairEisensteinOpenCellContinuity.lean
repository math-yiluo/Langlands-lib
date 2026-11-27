import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpenGroups
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingLeviIntegral
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingSeries
import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.Factors.CuspidalPairEisensteinOneplaceIntegrand
import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.AdelicBlockSmoothSectionGrowth
import Langlands.Global.RankinSelberg.DualExpansionFinal
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Continuity of the open-cell integrand

The twisted section `φ_s = φ · H^s` of a cuspidal-pair section is continuous and left invariant
under the rational points of the parabolic. A Whittaker coefficient over the compact quotient
`N(F) \ N(𝔸)` of a jointly continuous family of functions left invariant under `N(F)` depends
continuously on the parameter; applying this to both blocks shows that the Levi Whittaker
coefficient `W_M(φ_s)` is continuous on `GL_N(𝔸)`, and hence that the open-cell integrand
`Y ↦ W_M(φ_s)(w u'(Y)) conj(ψ_N(u'(Y)))` is continuous. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Automorphic (CuspidalOperatorRealization)

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellContinuity

open Langlands.GeneralLinear Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicBlockScalarSections AdelicBlockEisensteinGeometry AdelicGroupPoints
  GeneralLinearGroupPoints AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight RankinSelbergGlobal RankinSelbergGlobal.Unfolding

variable {F : Type u} [Field F] [NumberField F]

local instance continuitySchemeAffine (n : ℕ) :
    IsAffine (RankinSelbergGlobal.Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance continuitySchemeSmooth (n : ℕ) :
    Smooth (RankinSelbergGlobal.Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section Parametric

local instance continuityQuotientBorel (n : ℕ) :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F (Scheme F (n + 1))
      (upperUnipotent F (n + 1))) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F _ _

/-- **Whittaker coefficients of continuous families.** Let `ψ` be a standard additive
character. If `h : P → GL_(n+1)(𝔸) → ℂ` is jointly continuous and each `h p` is left invariant
under the rational points, then
`p ↦ W_(h p)(1)` is continuous. -/
theorem continuous_whittaker_param {P : Type*} [TopologicalSpace P] {n : ℕ}
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (h : P → Points F (n + 1) → ℂ) (hc : Continuous fun q : P × Points F (n + 1) => h q.1 q.2)
    (hinv : ∀ p, ∀ c ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (n + 1)), ∀ x,
      h p (c * x) = h p x) :
    Continuous fun p => generalLinearWhittakerFunction F n ψ (fun _ => 1) (h p) 1 := by
  have hcpt := compactSpace_unipotentRationalQuotient F (n + 1)
  have hprob := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F
    (Scheme F (n + 1)) (upperUnipotent F (n + 1))
  set Γ := AdelicSubgroupPoints.rationalSubgroup F (Scheme F (n + 1)) (upperUnipotent F (n + 1))
  have hφ : ∀ (p : P) (g₀ : Γ) (u : unipotentAdelic F (n + 1)),
      h p ((((g₀ : unipotentAdelic F (n + 1)) * u : unipotentAdelic F (n + 1)) :
          Points F (n + 1)) * 1) *
        starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) ((g₀ : unipotentAdelic F (n + 1)) * u)) =
      h p ((u : Points F (n + 1)) * 1) *
        starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) u) := by
    intro p g₀ u
    rw [Subgroup.coe_mul, mul_assoc, hinv p _ (mem_rationalSubgroup_of_unipotent F g₀),
      genericCharacter_rational_mul F n ψ hψ]
  have hint : ∀ (p : P)
      (x : AdelicSubgroupPoints.RationalQuotient F (Scheme F (n + 1)) (upperUnipotent F (n + 1))),
      h p (((Quotient.out x : unipotentAdelic F (n + 1)) : Points F (n + 1)) * 1) *
          starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) (Quotient.out x)) =
        LeftCosetSpace.lift Γ (fun u : unipotentAdelic F (n + 1) =>
          h p ((u : Points F (n + 1)) * 1) *
            starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) u)) (hφ p) x := by
    intro p x
    conv_rhs => rw [← Quotient.out_eq x]
    rfl
  unfold generalLinearWhittakerFunction subgroupCharacterCoefficient
  simp_rw [hint]
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_integral_of_continuous_uncurry _ ?_
  have hq : IsOpenQuotientMap (Prod.map (id : P → P) (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  rw [hq.isQuotientMap.continuous_iff]
  have hc' : Continuous fun q : P × unipotentAdelic F (n + 1) =>
      h q.1 ((q.2 : Points F (n + 1)) * 1) *
        starRingEnd ℂ (genericCharacter F n ψ (fun _ => 1) q.2) :=
    (hc.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).mul
      (Complex.continuous_conj.comp
        ((continuous_genericCharacter F n ψ hψ.1 _).comp continuous_snd))
  exact hc'.congr fun q => rfl

end Parametric

section Twisted

variable {r t : ℕ}

local instance continuityParabolicAffine :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance continuityParabolicClosed :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

theorem leviEmbedding_rationalLevi {n : ℕ} (B : BlockShape n) (m : B.Levi F) :
    B.leviEmbedding (Adeles F) (rationalLevi F B m) =
      AdelicGL.rational F n (B.leviEmbedding F m) := by
  apply Units.ext
  change Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' fun i => ((m i).val).map (algebraMap F (Adeles F))) =
    (Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' fun i => (m i).val)).map (algebraMap F (Adeles F))
  rw [← Matrix.blockDiagonal'_map _ _ (map_zero _)]
  rfl

theorem continuous_leviPair' {X : Type*} [TopologicalSpace X]
    {f : X → AdelicGL F (r + 1)} {g : X → AdelicGL F (t + 1)} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => leviPair F r t (f x) (g x) :=
  (Unfolding.continuous_leviPair F r t).comp (hf.prodMk hg)

theorem exists_rational_of_mem {n : ℕ} {c : Points F n}
    (hc : c ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    ∃ c' : RationalGL F n, GeneralLinearGroupPoints.adelicEquiv F n c = AdelicGL.rational F n c' := by
  obtain ⟨x, rfl⟩ := hc
  exact ⟨rationalEquiv F n x, adelicEquiv_rational F n x⟩

variable [CompactSpace (AdeleQuotient F)]
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {φ : AdelicGL F (r + t + 2) → ℂ}

local instance continuityVAGroup :
    AddCommGroup (FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T')) :=
  Submodule.addCommGroup _

theorem continuous_twisted (hφ : IsSection T T' φ) (s : ℂ) :
    Continuous (Oneplace.twisted φ s) :=
  (continuous_of_isSection hφ).mul (continuous_heightPower s)

/-- For a section `φ` with `IsSection T T' φ`, the twisted section is left invariant under
rational Levi elements. -/
theorem twisted_leviPair_rational_mul (hφ : IsSection T T' φ) (s : ℂ)
    (c₁ : RationalGL F (r + 1)) (c₂ : RationalGL F (t + 1)) (z : AdelicGL F (r + t + 2)) :
    Oneplace.twisted φ s
        (leviPair F r t (AdelicGL.rational F (r + 1) c₁) (AdelicGL.rational F (t + 1) c₂) * z) =
      Oneplace.twisted φ s z := by
  set m : (blockShape r t).Levi F :=
    (Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) F).symm (c₁, c₂)
  have hlevi : Oneplace.leviOf (AdelicGL.rational F (r + 1) c₁) (AdelicGL.rational F (t + 1) c₂) =
      rationalLevi F (blockShape r t) m := by
    funext i
    rcases eq_firstBlock_or_eq_secondBlock r t i with rfl | rfl <;> rfl
  have hm : leviPair F r t (AdelicGL.rational F (r + 1) c₁) (AdelicGL.rational F (t + 1) c₂) =
      AdelicGL.rational F (r + t + 2) ((blockShape r t).leviEmbedding F m) := by
    rw [Oneplace.leviPair_eq_leviEmbedding, hlevi, leviEmbedding_rationalLevi]
  have hmem : (blockShape r t).leviEmbedding F m ∈ (blockShape r t).parabolic F :=
    ((blockShape r t).leviInParabolic F m).property
  rw [hm, Oneplace.twisted, Oneplace.twisted, isSection_rational_mul hφ _ hmem,
    heightPower_rational_mul s _ hmem]

theorem twisted_leviPair_left (hφ : IsSection T T' φ) (s : ℂ) (c : RationalGL F (r + 1))
    (a : AdelicGL F (r + 1)) (b : AdelicGL F (t + 1)) (z : AdelicGL F (r + t + 2)) :
    Oneplace.twisted φ s (leviPair F r t (AdelicGL.rational F (r + 1) c * a) b * z) =
      Oneplace.twisted φ s (leviPair F r t a b * z) := by
  have h : leviPair F r t (AdelicGL.rational F (r + 1) c * a) b =
      leviPair F r t (AdelicGL.rational F (r + 1) c) (AdelicGL.rational F (t + 1) 1) *
        leviPair F r t a b := by
    rw [map_one, ← Unfolding.leviPair_mul, one_mul]
  rw [h, mul_assoc, twisted_leviPair_rational_mul hφ s]

theorem twisted_leviPair_right (hφ : IsSection T T' φ) (s : ℂ) (c : RationalGL F (t + 1))
    (a : AdelicGL F (r + 1)) (b : AdelicGL F (t + 1)) (z : AdelicGL F (r + t + 2)) :
    Oneplace.twisted φ s (leviPair F r t a (AdelicGL.rational F (t + 1) c * b) * z) =
      Oneplace.twisted φ s (leviPair F r t a b * z) := by
  have h : leviPair F r t a (AdelicGL.rational F (t + 1) c * b) =
      leviPair F r t (AdelicGL.rational F (r + 1) 1) (AdelicGL.rational F (t + 1) c) *
        leviPair F r t a b := by
    rw [map_one, ← Unfolding.leviPair_mul, one_mul]
  rw [h, mul_assoc, twisted_leviPair_rational_mul hφ s]

/-- The inner Whittaker coefficient of `W_M(φ_s)`, as a function of the first block and the
point of `GL_N(𝔸)`. -/
def innerWhittaker (ψ : AddChar (Adeles F) ℂ) (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ)
    (G : AdelicGL F (r + t + 2)) (x : Points F (r + 1)) : ℂ :=
  generalLinearWhittakerFunction F t ψ (fun _ => 1)
    (fun y => Oneplace.twisted φ s (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * G)) 1

theorem continuous_innerWhittaker (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (hφ : IsSection T T' φ) (s : ℂ) :
    Continuous fun q : AdelicGL F (r + t + 2) × Points F (r + 1) =>
      innerWhittaker ψ φ s q.1 q.2 := by
  have hf : Continuous (Oneplace.twisted φ s) := continuous_twisted hφ s
  have hE : ∀ n : ℕ, Continuous (GeneralLinearGroupPoints.adelicEquiv F n) := fun n =>
    (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous
  have h2 : Continuous fun q : (AdelicGL F (r + t + 2) × Points F (r + 1)) × Points F (t + 1) =>
      leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.1.2)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) q.2) :=
    continuous_leviPair' ((hE (r + 1)).comp (continuous_snd.comp continuous_fst))
      ((hE (t + 1)).comp continuous_snd)
  have h3 : Continuous fun q : (AdelicGL F (r + t + 2) × Points F (r + 1)) × Points F (t + 1) =>
      leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.1.2)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) q.2) * q.1.1 :=
    h2.mul (continuous_fst.comp continuous_fst)
  have hc : Continuous fun q : (AdelicGL F (r + t + 2) × Points F (r + 1)) × Points F (t + 1) =>
      Oneplace.twisted φ s (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.1.2)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) q.2) * q.1.1) :=
    hf.comp h3
  have hinv : ∀ (q : AdelicGL F (r + t + 2) × Points F (r + 1)),
      ∀ c ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1)), ∀ y : Points F (t + 1),
        Oneplace.twisted φ s (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.2)
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) (c * y)) * q.1) =
        Oneplace.twisted φ s (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.2)
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * q.1) := by
    intro q c hc y
    obtain ⟨c', hc'⟩ := exists_rational_of_mem hc
    rw [map_mul, hc', twisted_leviPair_right hφ s]
  have key := continuous_whittaker_param (P := AdelicGL F (r + t + 2) × Points F (r + 1))
    (n := t) ψ hψ (fun q y => Oneplace.twisted φ s
      (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) q.2)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * q.1)) hc hinv
  unfold innerWhittaker
  exact key

theorem innerWhittaker_rational_mul (ψ : AddChar (Adeles F) ℂ) (hφ : IsSection T T' φ)
    (s : ℂ) (G : AdelicGL F (r + t + 2)) {c : Points F (r + 1)}
    (hc : c ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    innerWhittaker ψ φ s G (c * x) = innerWhittaker ψ φ s G x := by
  obtain ⟨c', hc'⟩ := exists_rational_of_mem hc
  have hfun : (fun y => Oneplace.twisted φ s
      (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (c * x))
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * G)) =
      fun y => Oneplace.twisted φ s
        (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * G) := by
    funext y
    rw [map_mul, hc', twisted_leviPair_left hφ s]
  unfold innerWhittaker
  rw [hfun]

/-- **Continuity of the Levi Whittaker coefficient** of the twisted section, for a standard
additive character `ψ` and a section `φ` with `IsSection T T' φ`. -/
theorem continuous_leviWhittaker (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (hφ : IsSection T T' φ) (s : ℂ) :
    Continuous (leviWhittaker F r t ψ (Oneplace.twisted φ s)) := by
  have h := continuous_whittaker_param ψ hψ (innerWhittaker ψ φ s)
    (continuous_innerWhittaker ψ hψ hφ s)
    (fun G c hc x => innerWhittaker_rational_mul ψ hφ s G hc x)
  have heq : leviWhittaker F r t ψ (Oneplace.twisted φ s) = fun G =>
      generalLinearWhittakerFunction F r ψ (fun _ => 1) (innerWhittaker ψ φ s G) 1 := by
    funext G
    unfold leviWhittaker innerWhittaker
    rfl
  rw [heq]
  exact h

end Twisted

section Integrand

variable {r t : ℕ}

theorem continuous_openCellUnipotent : Continuous (openCellUnipotent F r t) := by
  have hval : Continuous fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) =>
      ((openCellUnipotent F r t Y : AdelicGL F (r + t + 2)) :
        Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) :=
    (((continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_reindex
      finSumFinEquiv finSumFinEquiv).matrix_reindex _ _).matrix_reindex _ _
  have hinv : ∀ Y, (openCellUnipotent F r t Y)⁻¹ = openCellUnipotent F r t (-Y) := by
    intro Y
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← Oneplace.openCellUnipotent_add, neg_add_cancel, Unfolding.openCellUnipotent_zero]
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [hinv]
  exact hval.comp continuous_neg

variable [CompactSpace (AdeleQuotient F)]
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {φ : AdelicGL F (r + t + 2) → ℂ}

/-- **Continuity of the open-cell integrand**, for a standard additive character `ψ` and a
section `φ` with `IsSection T T' φ`. -/
theorem continuous_openCellIntegrand (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (hφ : IsSection T T' φ) (s : ℂ) :
    Continuous (openCellIntegrand ψ φ s) := by
  have h1 : Continuous fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) =>
      leviWhittaker F r t ψ (Oneplace.twisted φ s)
        (openCellWeyl F r t * openCellUnipotent F r t Y) :=
    (continuous_leviWhittaker ψ hψ hφ s).comp (continuous_const.mul continuous_openCellUnipotent)
  have h2 : Continuous fun Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F) =>
      starRingEnd ℂ (ψ (∑ i : Fin (r + t + 1),
        (openCellUnipotent F r t Y : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
          i.castSucc i.succ)) := by
    simp_rw [openCellUnipotent_superdiagonal_sum]
    exact Complex.continuous_conj.comp (hψ.1.comp ((continuous_apply 0).comp
      (continuous_apply (Fin.last t))))
  exact h1.mul h2

end Integrand

end Langlands.Global.CuspidalPairEisenstein.OpenCellContinuity
