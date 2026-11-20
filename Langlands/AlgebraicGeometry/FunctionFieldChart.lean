import Mathlib.AlgebraicGeometry.FunctionField
import Langlands.CommutativeAlgebra.ChartUniqueFactorization

/-! # Sections over open immersions as subrings of the function field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.FunctionFieldChart

open Langlands.CommutativeAlgebra.ChartUniqueFactorization

instance nonempty_top {Y : Scheme.{u}} [Nonempty Y] : Nonempty (⊤ : Y.Opens) :=
  ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

instance nonempty_image {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (V : Y.Opens)
    [Nonempty V] : Nonempty (f ''ᵁ V) :=
  ⟨⟨f (Nonempty.some ‹Nonempty V›).1, ⟨_, (Nonempty.some ‹Nonempty V›).2, rfl⟩⟩⟩

variable {X : Scheme.{u}} [IsIntegral X]

section OpenImmersion

variable {U : Scheme.{u}} (φ : U ⟶ X) [IsOpenImmersion φ] [Nonempty U]

/-- The sections of `U` as rational functions on `X`, for an open immersion `φ : U ⟶ X`. -/
def toFunctionField : Γ(U, ⊤) →+* X.functionField :=
  (X.germToFunctionField (φ ''ᵁ ⊤)).hom.comp (φ.appIso ⊤).inv.hom

theorem toFunctionField_apply (s : Γ(U, ⊤)) :
    toFunctionField φ s = X.germToFunctionField (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv s) := rfl

theorem toFunctionField_injective : Function.Injective (toFunctionField φ) := by
  intro s t h
  have h' := X.germToFunctionField_injective (φ ''ᵁ ⊤) h
  have := congrArg (φ.appIso ⊤).hom h'
  simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] using this

/-- Two equal open immersions give the same rational functions. -/
theorem toFunctionField_congr {φ' : U ⟶ X} [IsOpenImmersion φ'] (h : φ = φ') (s : Γ(U, ⊤)) :
    toFunctionField φ s = toFunctionField φ' s := by
  subst h; rfl

/-- The rational function of a restricted section is that of the section. -/
theorem germToFunctionField_map {V V' : X.Opens} [Nonempty V] [Nonempty V']
    (i : op V' ⟶ op V) (t : Γ(X, V')) :
    X.germToFunctionField V (X.presheaf.map i t) = X.germToFunctionField V' t :=
  X.presheaf.germ_res_apply i.unop _ _ t

/-- Pulled-back global functions of `X` are the functions of `X` themselves. -/
theorem toFunctionField_appTop (a : Γ(X, ⊤)) :
    toFunctionField φ (φ.appTop a) = algebraMap Γ(X, ⊤) X.functionField a := by
  rw [toFunctionField_apply]
  have h := congrArg (fun f => f.hom a) (φ.app_appIso_inv ⊤)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  change X.germToFunctionField (φ ''ᵁ ⊤) ((φ.appIso (φ ⁻¹ᵁ ⊤)).inv (φ.app ⊤ a)) = _
  rw [h]
  exact germToFunctionField_map _ _

/-- Restricting along an open immersion `a : W ⟶ U` does not change the rational function. -/
theorem toFunctionField_comp {W : Scheme.{u}} (a : W ⟶ U) [IsOpenImmersion a] [Nonempty W]
    (s : Γ(U, ⊤)) : toFunctionField (a ≫ φ) (a.appTop s) = toFunctionField φ s := by
  rw [toFunctionField_apply, toFunctionField_apply, Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, CommRingCat.comp_apply]
  have h1 := congrArg (fun f => f.hom s) (a.app_appIso_inv ⊤)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  change X.germToFunctionField _ ((X.presheaf.mapIso _).inv ((φ.appIso (a ''ᵁ ⊤)).inv
    ((a.appIso (a ⁻¹ᵁ ⊤)).inv (a.app ⊤ s)))) = _
  rw [h1]
  have h2 := congrArg (fun f => f.hom s)
    (φ.appIso_inv_naturality (homOfLE (le_top : a ''ᵁ ⊤ ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  erw [h2]
  rw [Functor.mapIso_inv, germToFunctionField_map, germToFunctionField_map]

/-- Two charts that agree after restriction to a common open piece define the same rational
functions. -/
theorem toFunctionField_eq_of_comp_eq {U' W : Scheme.{u}} (φ' : U' ⟶ X) [IsOpenImmersion φ']
    [Nonempty U'] [Nonempty W] (ψ : W ⟶ U) (k : W ⟶ U') [IsOpenImmersion k]
    (h : ψ ≫ φ = k ≫ φ') (s : Γ(U, ⊤)) (s' : Γ(U', ⊤)) (hs : ψ.appTop s = k.appTop s') :
    toFunctionField φ s = toFunctionField φ' s' := by
  have : IsOpenImmersion (ψ ≫ φ) := by rw [h]; infer_instance
  have : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ φ
  rw [← toFunctionField_comp φ ψ s, ← toFunctionField_comp φ' k s', hs]
  exact toFunctionField_congr _ h _

end OpenImmersion

section Opens

theorem algebraMap_eq_germToFunctionField (a : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) X.functionField a = X.germToFunctionField ⊤ a := rfl

variable (V : X.Opens) [Nonempty V]

/-- The sections over a nonempty open, as a subalgebra of the function field. -/
def sectionSubalgebra : Subalgebra Γ(X, ⊤) X.functionField where
  carrier := Set.range (X.germToFunctionField V)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ a b⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ a b⟩
  algebraMap_mem' a := ⟨X.presheaf.map (homOfLE le_top).op a, germToFunctionField_map _ _⟩

theorem mem_sectionSubalgebra {x : X.functionField} :
    x ∈ sectionSubalgebra V ↔ ∃ t : Γ(X, V), X.germToFunctionField V t = x := Iff.rfl

/-- Sections over `V` are isomorphic to the subalgebra of their rational functions. -/
def sectionEquiv : Γ(X, V) ≃+* sectionSubalgebra V :=
  RingEquiv.ofBijective
    ({ toFun := fun t => ⟨X.germToFunctionField V t, t, rfl⟩
       map_one' := Subtype.ext (map_one _)
       map_mul' := fun a b => Subtype.ext (map_mul _ a b)
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun a b => Subtype.ext (map_add _ a b) } : Γ(X, V) →+* sectionSubalgebra V)
    ⟨fun _ _ h => X.germToFunctionField_injective V (congrArg Subtype.val h),
      fun ⟨_, t, rfl⟩ => ⟨t, rfl⟩⟩

@[simp] theorem sectionEquiv_apply_coe (t : Γ(X, V)) :
    (sectionEquiv V t : X.functionField) = X.germToFunctionField V t := rfl

theorem algebraMap_sectionSubalgebra (a : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) (sectionSubalgebra V) a =
      sectionEquiv V (X.presheaf.map (homOfLE le_top).op a) := by
  apply Subtype.ext
  change X.germToFunctionField ⊤ a = X.germToFunctionField V _
  rw [germToFunctionField_map]

/-- The rational functions coming from a stalk are the fractions of sections over any affine
open neighbourhood with denominators invertible at the point. -/
theorem mem_range_stalk_iff {W : X.Opens} (hW : IsAffineOpen W) [Nonempty W] {y : X}
    (hy : y ∈ W) (x : X.functionField) :
    x ∈ Set.range (algebraMap (X.presheaf.stalk y) X.functionField) ↔
      ∃ a s : Γ(X, W), s ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal ∧
        x = X.germToFunctionField W a * (X.germToFunctionField W s)⁻¹ := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : W)
  have := hW.isLocalization_stalk ⟨y, hy⟩
  have hg : ∀ t : Γ(X, W), algebraMap (X.presheaf.stalk y) X.functionField
      (algebraMap Γ(X, W) (X.presheaf.stalk y) t) = X.germToFunctionField W t :=
    fun t => Scheme.algebraMap_germ_eq_germToFunctionField X hy t
  have hne : ∀ s : Γ(X, W), s ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal →
      X.germToFunctionField W s ≠ 0 := by
    intro s hs h0
    apply hs
    have : s = 0 := X.germToFunctionField_injective W (h0.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  have key : ∀ (a : Γ(X, W)) (s : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl),
      algebraMap (X.presheaf.stalk y) X.functionField (IsLocalization.mk' _ a s) =
        X.germToFunctionField W a * (X.germToFunctionField W s)⁻¹ := by
    intro a s
    have h := IsLocalization.mk'_spec (X.presheaf.stalk y) a s
    have h' := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) h
    rw [map_mul, hg, hg] at h'
    rw [← h', mul_assoc, mul_inv_cancel₀ (hne s s.2), mul_one]
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl m
    exact ⟨a, s, s.2, key a s⟩
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨IsLocalization.mk' _ a (⟨s, hs⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl),
      key a ⟨s, hs⟩⟩

instance isFractionRing_top [IsAffine X] : IsFractionRing Γ(X, ⊤) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)

omit [IsIntegral X] in
/-- The prime of the global sections at a point of an affine open is the contraction of its
prime in the sections over that open. -/
theorem comap_primeIdealOf_res [IsAffine X] {V : X.Opens} (hV : IsAffineOpen V) {y : X}
    (hy : y ∈ V) :
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap (X.presheaf.map (homOfLE le_top).op).hom =
      ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 X) ⊤ (isAffineOpen_top X) V hV
    le_top hy
  have h' := congrArg PrimeSpectrum.asIdeal h
  simp only [PrimeSpectrum.comap_asIdeal] at h'
  convert h' using 3
  · simp [Scheme.Hom.appLE]
  · rfl

/-- **Sections over an affine open form a chart.** For an affine open `V` of an integral affine
scheme `X`, the localization of the sections over `V` at any prime agrees, inside the function
field, with the localization of the global sections at the contracted prime. -/
theorem isChart_sectionSubalgebra [IsAffine X] {V : X.Opens} (hV : IsAffineOpen V)
    [Nonempty V] :
    IsChart (sectionSubalgebra V) := by
  intro Q _ x
  let e := sectionEquiv V
  let Q₁ : Ideal Γ(X, V) := Q.comap (e : Γ(X, V) →+* sectionSubalgebra V)
  have hQ₁ : Q₁.IsPrime := Ideal.comap_isPrime _ _
  let y := hV.fromSpec ⟨Q₁, hQ₁⟩
  have hy : y ∈ V := by
    have h : y ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [hV.range_fromSpec] at h
  have hprime : hV.primeIdealOf ⟨y, hy⟩ = ⟨Q₁, hQ₁⟩ := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact hV.fromSpec_primeIdealOf ⟨y, hy⟩
  have hq : Q.comap (algebraMap Γ(X, ⊤) (sectionSubalgebra V)) =
      ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal := by
    rw [← comap_primeIdealOf_res hV hy, hprime]
    ext a
    simp only [Ideal.mem_comap]
    rw [algebraMap_sectionSubalgebra]
    rfl
  have h1 : x ∈ chartLoc X.functionField (sectionSubalgebra V) Q ↔
      ∃ a s : Γ(X, V), s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal ∧
        x = X.germToFunctionField V a * (X.germToFunctionField V s)⁻¹ := by
    rw [hprime]
    constructor
    · rintro ⟨a, s, hs, h⟩
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨s', rfl⟩ := e.surjective s
      exact ⟨a', s', hs, h⟩
    · rintro ⟨a, s, hs, h⟩
      exact ⟨e a, e s, hs, h⟩
  have h2 : x ∈ loc X.functionField (Q.comap (algebraMap Γ(X, ⊤) (sectionSubalgebra V))) ↔
      ∃ a s : Γ(X, ⊤), s ∉ ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal ∧
        x = X.germToFunctionField ⊤ a * (X.germToFunctionField ⊤ s)⁻¹ := by
    constructor
    · rintro ⟨a, s, hs, h⟩
      refine ⟨a, s, ?_, h⟩
      rw [← hq]
      exact hs
    · rintro ⟨a, s, hs, h⟩
      refine ⟨a, s, ?_, h⟩
      change s ∉ Q.comap (algebraMap Γ(X, ⊤) (sectionSubalgebra V))
      rw [hq]
      exact hs
  rw [h1, h2, ← mem_range_stalk_iff hV hy, mem_range_stalk_iff (isAffineOpen_top X) trivial]

/-- Every point of an affine open gives a prime of the sections over it lying over the prime of
the point in the global sections. -/
theorem exists_prime_comap_eq [IsAffine X] {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    {y : X} (hy : y ∈ V) :
    ∃ Q : Ideal (sectionSubalgebra V), Q.IsPrime ∧
      Q.comap (algebraMap Γ(X, ⊤) (sectionSubalgebra V)) =
        ((isAffineOpen_top X).primeIdealOf ⟨y, trivial⟩).asIdeal := by
  refine ⟨(hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap ((sectionEquiv V).symm : _ →+* Γ(X, V)),
    Ideal.comap_isPrime _ _, ?_⟩
  rw [← comap_primeIdealOf_res hV hy]
  ext a
  simp only [Ideal.mem_comap]
  rw [algebraMap_sectionSubalgebra]
  simp

omit [IsIntegral X] in
/-- The prime ideal of the global sections at the point it defines. -/
theorem primeIdealOf_fromSpec_top [IsAffine X] (q : PrimeSpectrum Γ(X, ⊤)) :
    (isAffineOpen_top X).primeIdealOf ⟨(isAffineOpen_top X).fromSpec q, trivial⟩ = q := by
  apply (isAffineOpen_top X).fromSpec.isOpenEmbedding.injective
  exact (isAffineOpen_top X).fromSpec_primeIdealOf ⟨_, trivial⟩

omit [IsIntegral X] in
/-- A section not invertible at a point of an affine open lies in the prime of that point. -/
theorem mem_primeIdealOf_of_notMem_basicOpen {V : X.Opens} (hV : IsAffineOpen V) {y : X}
    (hy : y ∈ V) {t : Γ(X, V)} (ht : y ∉ X.basicOpen t) :
    t ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
  have := hV.isLocalization_stalk ⟨y, hy⟩
  by_contra h
  apply ht
  rw [Scheme.mem_basicOpen X t y hy]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal t).2 h

end Opens

section ChartSubalgebra

variable {U : Scheme.{u}} (φ : U ⟶ X) [IsOpenImmersion φ] [Nonempty U]

/-- The sections of `U` are isomorphic to their rational functions on `X`. -/
def chartEquiv : Γ(U, ⊤) ≃+* sectionSubalgebra (φ ''ᵁ ⊤) :=
  (φ.appIso ⊤).symm.commRingCatIsoToRingEquiv.trans (sectionEquiv _)

@[simp] theorem chartEquiv_apply_coe (s : Γ(U, ⊤)) :
    (chartEquiv φ s : X.functionField) = toFunctionField φ s := rfl

theorem toFunctionField_mem (s : Γ(U, ⊤)) :
    toFunctionField φ s ∈ sectionSubalgebra (φ ''ᵁ ⊤) :=
  (chartEquiv φ s).2

omit [IsIntegral X] [Nonempty U] in
/-- The image of an affine chart is an affine open. -/
theorem isAffineOpen_image_top [IsAffine U] : IsAffineOpen (φ ''ᵁ ⊤) :=
  (isAffineOpen_top U).image_of_isOpenImmersion φ

end ChartSubalgebra

end Langlands.AlgebraicGeometry.FunctionFieldChart
