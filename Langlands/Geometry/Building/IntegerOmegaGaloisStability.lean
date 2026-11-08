import Langlands.Geometry.Building.ApartmentGaloisAction
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.Geometry.Building.CentralizerGaloisTransport
import Langlands.Geometry.Building.IntegerOmegaApartmentRigidity

/-! # Coefficient stability and fixed loci of centralizer-compatible apartment classes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- The points of a real affine space fixed by every member of a monoid acting by
affine equivalences. -/
def fixedAffineSubspace {M V P : Type*} [Monoid M] [AddCommGroup V] [Module ℝ V]
    [AddTorsor V P] (ρ : M →* (P ≃ᵃ[ℝ] P)) : AffineSubspace ℝ P where
  carrier := {x | ∀ m, ρ m x = x}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ := by
    have h₁' : ∀ m, ρ m p₁ = p₁ := h₁
    have h₂' : ∀ m, ρ m p₂ = p₂ := h₂
    have h₃' : ∀ m, ρ m p₃ = p₃ := h₃
    intro m
    have hv : (ρ m).linear (p₁ -ᵥ p₂) = p₁ -ᵥ p₂ := by
      have h := (ρ m).toAffineMap.linearMap_vsub p₁ p₂
      rw [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_toAffineMap, h₁' m, h₂' m] at h
      exact h
    rw [AffineEquiv.map_vadd, LinearEquiv.map_smul, hv, h₃' m]

theorem mem_fixedAffineSubspace_iff {M V P : Type*} [Monoid M] [AddCommGroup V]
    [Module ℝ V] [AddTorsor V P] (ρ : M →* (P ≃ᵃ[ℝ] P)) (x : P) :
    x ∈ fixedAffineSubspace ρ ↔ ∀ m, ρ m x = x := Iff.rfl

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine' : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- The affine subspace of apartment points fixed by every coefficient automorphism. -/
def galoisFixedApartment : AffineSubspace ℝ D.Apartment :=
  fixedAffineSubspace (galoisAffineAction k K i D hD)

theorem mem_galoisFixedApartment_iff (x : D.Apartment) :
    x ∈ galoisFixedApartment k K i D hD ↔ ∀ σ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G σ x.val = x.val := by
  change (∀ σ, galoisAction k K i D hD σ x = x) ↔ _
  constructor
  · intro h σ
    exact congrArg Apartment.val (h σ)
  · intro h σ
    exact Apartment.ext (h σ)

/-- A coefficient-invariant normalizer point preserves the fixed apartment. -/
theorem normalizer_smul_mem_galoisFixedApartment
    (n : normalizerPoints (T := T_K) i_K)
    (hn : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ n.val = n.val)
    {x : D.Apartment} (hx : x ∈ galoisFixedApartment k K i D hD) :
    n • x ∈ galoisFixedApartment k K i D hD := by
  have hx' : ∀ σ, galoisAction k K i D hD σ x = x := hx
  intro σ
  change galoisAction k K i D hD σ (n • x) = n • x
  have hσ : normalizerGaloisAction k K i σ n = n := Subtype.ext (hn σ)
  rw [galoisAction_normalizer_smul, hσ, hx' σ]

/-- Fixed apartment points give coefficient-fixed points of the actual reduced
building. -/
theorem galoisQuotientAction_apartmentMap_of_mem {x : D.Apartment}
    (hx : x ∈ galoisFixedApartment k K i D hD) (σ : K ≃ₐ[k] K) :
    galoisQuotientAction k K i D hD σ (D.apartmentMap x) = D.apartmentMap x := by
  have hx' : ∀ σ, galoisAction k K i D hD σ x = x := hx
  rw [galoisQuotientAction_apartmentMap, hx' σ]

/-- Coefficient-invariant rational points preserve coefficient-fixed points of the
actual reduced building. -/
theorem galoisQuotientAction_smul_of_fixed (g : rationalPoints G_K)
    (hg : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ g = g) {z : D.ReducedBuilding}
    (hz : ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K i D hD σ z = z) (σ : K ≃ₐ[k] K) :
    galoisQuotientAction k K i D hD σ (g • z) = g • z := by
  rw [galoisQuotientAction_smul, hg σ, hz σ]

end KPApartmentData

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building.IntegerValuation

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (j : Z ⟶ G) (s : T.toGrp ⟶ Z)
  (w : Valuation K (WithZero (Multiplicative ℤ)))

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "s_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) s

variable [IsAffineHom G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

/-- A class compatible with the base-changed centralizer datum equals its actual
coefficient image, under actual opposite-pair existence upstairs. -/
theorem IsOmegaCompatible.galoisImage_eq (σ : K ≃ₐ[k] K)
    (hw : ∀ t : Kˣ, order w (Units.map σ.toMonoidHom t) = order w t)
    (D : KPApartmentData (S := T_K) i_K (order w))
    (hcl : IsClosedSubgroup j_K)
    (hrep : (torusCentralizer (T := T_K) i_K).IsRepresentedBy j_K)
    (hcomp : s_K ≫ j_K = i_K)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (hD : IsOmegaCompatible w D ⟨(GroupScheme.baseChange b).obj Z, j_K, s_K, hcl, hrep,
      hcomp, hK⟩)
    (hG : IsConnectedReductive G_K) (hi : IsMaximalSplitTorus (T := T_K) i_K)
    (hpair : RelativeRoot.HasOppositeFactorPairs (T := T_K) i_K) :
    KPApartmentData.galoisImage k K i D σ hw = D :=
  (IsOmegaCompatible.galoisImage k K i j s w σ hw D hcl hrep hcomp hK hD).eq_of_hasOppositeFactorPairs
    hD hG hi hpair

/-- A class compatible with the base-changed centralizer datum is stable under every
order-preserving coefficient automorphism, under actual opposite-pair existence
upstairs. -/
theorem IsOmegaCompatible.galoisStable
    (hw : ∀ (σ : K ≃ₐ[k] K) (t : Kˣ), order w (Units.map σ.toMonoidHom t) = order w t)
    (D : KPApartmentData (S := T_K) i_K (order w))
    (hcl : IsClosedSubgroup j_K)
    (hrep : (torusCentralizer (T := T_K) i_K).IsRepresentedBy j_K)
    (hcomp : s_K ≫ j_K = i_K)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := T_K) s_K))
    (hD : IsOmegaCompatible w D ⟨(GroupScheme.baseChange b).obj Z, j_K, s_K, hcl, hrep,
      hcomp, hK⟩)
    (hG : IsConnectedReductive G_K) (hi : IsMaximalSplitTorus (T := T_K) i_K)
    (hpair : RelativeRoot.HasOppositeFactorPairs (T := T_K) i_K) :
    KPApartmentData.GaloisStable k K i D := by
  intro σ φ hφ
  have h := IsOmegaCompatible.galoisImage_eq k K i j s w σ (hw σ) D hcl hrep hcomp hK hD hG hi
    hpair
  rw [← h]
  exact ⟨φ, hφ, rfl⟩

end Langlands.Geometry.Building.IntegerValuation
