import Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement
import Langlands.Global.ImaginaryAxisCoordinates
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # The open chamber of standard Eisenstein series parameters -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open GroupScheme RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (D : RelativeRootReflectionData i) (J : Set (characterLattice T))

local notation "P" => Standard.parabolicScheme i ν J
local notation "M" => Standard.leviScheme i ν J

include hG hi in
omit [NumberField F] in
/-- In any complex linear chart, the standard parameter inequalities define an open set. -/
theorem isOpen_standardRegularRegion (R : ℝ) {m : ℕ}
    (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    IsOpen {z | IsStandardRegularParameter D J R (e z)} := by
  let L (α : characterLattice T) : (Fin m → ℂ) →ₗ[ℝ] ℝ :=
    (pair T).flip (corootVector D α) ∘ₗ restrictToTorus F i ν J ∘ₗ parameterRealPart F P ∘ₗ
      e.toLinearMap.restrictScalars ℝ
  have hregion : {z | IsStandardRegularParameter D J R (e z)} =
      ⋂ α ∈ simpleRelativeRoots i ν \ J, {z | R < L α z} := by
    ext z
    simp only [mem_ofPred_eq, IsStandardRegularParameter, mem_iInter, Set.mem_sdiff, L,
      LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.restrictScalars_apply]
    exact ⟨fun h α hα => h α hα.1 hα.2, fun h α hα hα' => h α ⟨hα, hα'⟩⟩
  rw [hregion]
  refine (Set.Finite.sdiff ((ArthurRelative.finite_relativeRoots hG hi).subset
    (simpleRelativeRoots_subset_relativeRoots i ν))).isOpen_biInter fun α _ => ?_
  exact isOpen_lt continuous_const (L α).continuous_of_finiteDimensional

include hG hi in
omit [NumberField F] in
/-- The sum of the full fundamental weights outside the Levi has coroot value one on
every missing simple root. The corresponding standard chamber is nonempty at every depth. -/
theorem exists_standardRegularParameter (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (π : P ⟶ M)
    (hπ : Standard.leviToParabolic i ν J ≫ π = 𝟙 M) (R : ℝ) :
    ∃ lam : ComplexCharacterParameter F P, IsStandardRegularParameter D J R lam := by
  classical
  let Δ := simpleRelativeRoots i ν
  let s := (simpleFinset ν hG hi).filter (· ∉ J)
  let W : V T →ₗ[ℝ] ℝ := ∑ β ∈ s, ArthurRelative.weight hG hi ν D Δ β
  let hd := isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1
  obtain ⟨y, hy⟩ := hd.bijective_left.surjective W
  have hvalues (β : relativeRoots i) (hβ : β.1 ∈ Δ) :
      pair T y (D.realCoroot β) = if β.1 ∈ J then 0 else 1 := by
    rw [DFunLike.congr_fun hy (D.realCoroot β)]
    calc
      W (D.realCoroot β) = ∑ α ∈ s, if α = β.1 then (1 : ℝ) else 0 := by
        rw [show W (D.realCoroot β) = ∑ α ∈ s,
          ArthurRelative.weight hG hi ν D Δ α (D.realCoroot β) by simp only [W, LinearMap.sum_apply]]
        refine Finset.sum_congr rfl fun α hα => ?_
        exact ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl
          ((mem_simpleFinset (ν := ν) hG hi).mp (Finset.mem_filter.mp hα).1) β hβ
      _ = _ := by
        have hβ' : β.1 ∈ simpleRelativeRoots i ν := hβ
        by_cases hβJ : β.1 ∈ J <;> simp [s, hβ', hβJ]
  have hAnn : y ∈ corootAnnihilator i D J := by
    rw [mem_corootAnnihilator]
    intro β hβ
    change pair T y (D.realCoroot β) = 0
    rw [hvalues β (hJ hβ), ite_eq_left hβ]
  let t := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
  have ht := standardLeviTorusFactor_comp i ν J (Standard.isRepresentedBy_leviHom i ν J)
  have hrange := standardLeviCharacterAnnihilator F G hG T i hi ν hν J hJ M
    (Standard.leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J) t ht D
  obtain ⟨u, hu⟩ := hrange.symm ▸ hAnn
  have htl : t ≫ Standard.leviToParabolic i ν J = torusToParabolic F i ν J := by
    apply (Standard.isRepresentedBy_parabolicHom i ν J).hom_ext
    rw [Category.assoc, Standard.leviToParabolic_comp, ht, torusToParabolic_comp]
  let x := rationalCharacterRestrictReal π u
  have hx : restrictToTorus F i ν J x = y := by
    change rationalCharacterRestrictReal (torusToParabolic F i ν J)
      (rationalCharacterRestrictReal π u) = y
    rw [rationalCharacterRestrictReal_comp_apply, ← htl, Category.assoc, hπ, Category.comp_id, hu]
  let xR := (R + 1) • x
  let lam : ComplexCharacterParameter F P := ImaginaryAxis.complexify xR
  have hcomp : (parameterRealPart F P).comp ImaginaryAxis.complexify = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro a χ
    change (a : ℂ).re ⊗ₜ[ℤ] χ = a ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  have hreal : parameterRealPart F P lam = xR := LinearMap.congr_fun hcomp xR
  refine ⟨lam, fun α hα hαJ => ?_⟩
  have hαr := simpleRelativeRoots_subset_relativeRoots i ν hα
  rw [hreal, show xR = (R + 1) • x from rfl, map_smul, hx, corootVector, dite_eq_left hαr,
    map_smul, LinearMap.smul_apply, hvalues ⟨α, hαr⟩ hα, ite_eq_right hαJ,
    smul_eq_mul, mul_one]
  linarith

/-- The real-part inequalities defining standard regular parameters give a nonempty open set
in every complex linear chart and for every real threshold. -/
def StandardRegularRegionStatement : Prop :=
  ∀ {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {ν : cocharacterLattice T} (_hG : IsConnectedReductive G) (_hi : IsMaximalSplitTorus i)
    (_hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i) (J : Set (characterLattice T)),
    J ⊆ simpleRelativeRoots i ν →
    ∀ (π : Standard.parabolicScheme i ν J ⟶ Standard.leviScheme i ν J),
    Standard.leviToParabolic i ν J ≫ π = 𝟙 (Standard.leviScheme i ν J) →
    ∀ (R : ℝ) {m : ℕ}
      (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (Standard.parabolicScheme i ν J)),
    let U := {z | IsStandardRegularParameter D J R (e z)}
    IsOpen U ∧ U.Nonempty

theorem standardRegularRegion : StandardRegularRegionStatement := by
  intro F _ G _ T i _ ν hG hi hν D J hJ π hπ R m e U
  obtain ⟨lam, hlam⟩ := exists_standardRegularParameter hG hi D J hν hJ π hπ R
  refine ⟨isOpen_standardRegularRegion hG hi D J R e, ⟨e.symm lam, ?_⟩⟩
  change IsStandardRegularParameter D J R (e (e.symm lam))
  rwa [LinearEquiv.apply_symm_apply]

end Langlands.Global.ArthurTruncation
