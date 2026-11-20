import Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AffinePinching
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite open factorizations over an affine scheme -/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.QuasiFiniteFactorization

open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation

/-- A factorization through an open subscheme of a finite affine scheme over the target. -/
structure FiniteOpenFactorization {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ring : CommRingCat.{u}
  openMap : X ⟶ Spec ring
  finiteMap : Spec ring ⟶ Y
  openImmersion : IsOpenImmersion openMap
  finite : IsFinite finiteMap
  comp_eq : openMap ≫ finiteMap = f

private theorem exists_finiteType_subalgebra_localizing {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] {ι : Type*} [Finite ι] (h : ι → R)
    (hft : ∀ i, ((algebraMap R (Localization.Away (h i))).comp (algebraMap A R)).FiniteType) :
    ∃ (B : Subalgebra A R) (hB : ∀ i, h i ∈ B), Algebra.FiniteType A B ∧
      ∀ i, Function.Bijective (Localization.awayMap (B.val : B →+* R) ⟨h i, hB i⟩) := by
  classical
  let (i : ι) : Algebra A (Localization.Away (h i)) :=
    ((algebraMap R (Localization.Away (h i))).comp (algebraMap A R)).toAlgebra
  have ht (i : ι) : Algebra.FiniteType A (Localization.Away (h i)) := hft i
  choose S hS using fun i => (ht i).out
  have hnum (i : ι) (x : Localization.Away (h i)) : ∃ (y : R) (n : ℕ),
      x = IsLocalization.mk' (Localization.Away (h i)) y
        (⟨h i ^ n, n, rfl⟩ : Submonoid.powers (h i)) := by
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (h i)) x
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp m.2
    exact ⟨y, n, congrArg (IsLocalization.mk' _ y) (Subtype.ext hn.symm)⟩
  choose num pw hnum using hnum
  let G : Set R := Set.range h ∪ ⋃ i, num i '' (S i : Set (Localization.Away (h i)))
  have hG : G.Finite := (Set.finite_range h).union
    (Set.finite_iUnion fun i => (S i).finite_toSet.image _)
  let B := Algebra.adjoin A G
  have hGB : G ⊆ B := Algebra.subset_adjoin
  have hB : ∀ i, h i ∈ B := fun i => hGB (Or.inl ⟨i, rfl⟩)
  refine ⟨B, hB, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [← Subalgebra.fg_iff_finiteType]
    obtain ⟨F, hF⟩ := hG.exists_finset_coe
    exact ⟨F, by rw [hF]⟩
  · rw [Localization.awayMap_injective_iff]
    intro b hb
    exact ⟨0, by simpa using Subtype.ext hb⟩
  · let b : B := ⟨h i, hB i⟩
    let φ : Localization.Away b →+* Localization.Away (h i) :=
      Localization.awayMap (B.val : B →+* R) b
    change Function.Surjective φ
    intro y
    have hy : y ∈ Algebra.adjoin A (S i : Set (Localization.Away (h i))) := by
      rw [hS i]
      trivial
    apply RingHom.mem_range.mp
    refine Algebra.adjoin_induction (fun x hx => ?_) (fun a => ?_)
      (fun _ _ _ _ hx hy => φ.range.add_mem hx hy)
      (fun _ _ _ _ hx hy => φ.range.mul_mem hx hy) hy
    · have hnumB := hGB (Or.inr (Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩))
      refine ⟨IsLocalization.mk' (Localization.Away b) (⟨num i x, hnumB⟩ : B)
        (⟨b ^ pw i x, pw i x, rfl⟩ : Submonoid.powers b), ?_⟩
      refine Eq.trans ?_ (hnum i x).symm
      simp only [φ, IsLocalization.Away.map]
      erw [IsLocalization.map_mk']
      rfl
    · refine ⟨algebraMap B (Localization.Away b) (algebraMap A B a), ?_⟩
      simp only [φ, IsLocalization.Away.map]
      erw [IsLocalization.map_eq]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_localization_of_basicOpen_le {X S Y : Scheme.{u}}
    [IsAffine S] [IsAffine Y] (j : X ⟶ S) [IsOpenImmersion j] (k : S ⟶ Y)
    [LocallyOfFiniteType (j ≫ k)] (a : Γ(S, ⊤)) (ha : S.basicOpen a ≤ j.opensRange) :
    ((algebraMap Γ(S, ⊤) (Localization.Away a)).comp k.appTop.hom).FiniteType := by
  let U := S.basicOpen a
  have hU : IsAffineOpen U := (isAffineOpen_top S).basicOpen a
  have hV := hU.preimage_of_isOpenImmersion j ha
  have := j.isIso_app U ha
  have hcomp : k.appLE ⊤ U (by simp) ≫ j.app U =
      (j ≫ k).appLE ⊤ (j ⁻¹ᵁ U) (by simp) := by
    rw [j.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have hft : (k.appLE ⊤ U (by simp)).hom.FiniteType := by
    have H := (j ≫ k).finiteType_appLE (isAffineOpen_top Y) hV (by simp)
    rw [← hcomp, CommRingCat.hom_comp,
      RingHom.finiteType_respectsIso.cancel_right_isIso] at H
    exact H
  let e : Γ(S, U) ≃ₐ[Γ(S, ⊤)] Localization.Away a :=
    IsLocalization.algEquiv (Submonoid.powers a) _ _
  have hcomm : (e : Γ(S, U) →+* Localization.Away a).comp (k.appLE ⊤ U (by simp)).hom =
      (algebraMap Γ(S, ⊤) (Localization.Away a)).comp k.appTop.hom := by
    ext x
    exact e.commutes (k.appTop.hom x)
  rw [← hcomm]
  exact (RingHom.FiniteType.of_surjective _ e.surjective).comp hft

set_option backward.isDefEq.respectTransparency false in
/-- The finite factorization form of Zariski's Main Theorem over an affine base. -/
theorem nonempty_finiteOpenFactorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] : Nonempty (FiniteOpenFactorization f) := by
  classical
  let S := f.normalization
  let j : X ⟶ S := f.toNormalization
  let k : S ⟶ Y := f.fromNormalization
  have : IsIntegralHom k := inferInstanceAs (IsIntegralHom f.fromNormalization)
  have : IsAffine S := isAffine_of_isAffineHom k
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion f.toNormalization)
  have : LocallyOfFiniteType (j ≫ k) := f.toNormalization_fromNormalization ▸ ‹_›
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : X.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion j
  let ι := {a : Γ(S, ⊤) // S.basicOpen a ≤ j.opensRange}
  have hcover : (Set.range j : Set S) ⊆ ⋃ a : ι, (S.basicOpen a.1 : Set S) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := (isAffineOpen_top S).exists_basicOpen_le (V := j.opensRange)
      ⟨x, hx⟩ (by trivial)
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hxa⟩
  obtain ⟨L, hL⟩ := (isCompact_range j.continuous).elim_finite_subcover
    (fun a : ι => (S.basicOpen a.1 : Set S)) (fun a => (S.basicOpen a.1).2) hcover
  let h (i : ↥L) : Γ(S, ⊤) := (i.1 : ι).1
  let : Algebra Γ(Y, ⊤) Γ(S, ⊤) := k.appTop.hom.toAlgebra
  obtain ⟨B, hB, hft, hbij⟩ := exists_finiteType_subalgebra_localizing h fun i =>
    finiteType_localization_of_basicOpen_le j k (h i) (i.1 : ι).2
  let r (i : ↥L) : B := ⟨h i, hB i⟩
  let ψ : CommRingCat.of B ⟶ Γ(X, ⊤) := CommRingCat.ofHom (j.appTop.hom.comp B.val.toRingHom)
  let τ : Γ(Y, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B)
  have hψ i : Function.Bijective (Localization.awayMap ψ.hom (r i)) :=
    bijective_awayMap_comp _ _ _ (hbij i)
      (bijective_awayMap_appTop_of_isOpenImmersion j (h i) (i.1 : ι).2)
  have hcov : ⨆ i, X.basicOpen (ψ (r i)) = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hL (Set.mem_range_self x))
    refine Opens.mem_iSup.mpr ⟨⟨a, ha⟩, ?_⟩
    change x ∈ X.basicOpen (j.appTop.hom (h ⟨a, ha⟩))
    rw [← Scheme.preimage_basicOpen_top j (h ⟨a, ha⟩)]
    exact hxa
  have : IsOpenImmersion (X.toSpecΓ ≫ Spec.map ψ) :=
    (isOpenImmersion_toSpecΓ_comp_SpecMap ψ r hψ hcov).1
  have : Algebra.IsIntegral Γ(Y, ⊤) Γ(S, ⊤) := by
    refine ⟨fun x => ?_⟩
    change k.appTop.hom.IsIntegralElem x
    exact k.isIntegral_app ⊤ (isAffineOpen_top Y) x
  have : Algebra.IsIntegral Γ(Y, ⊤) B :=
    Algebra.IsIntegral.of_injective B.val Subtype.val_injective
  have : Module.Finite Γ(Y, ⊤) B := Algebra.IsIntegral.finite
  have : IsFinite (Spec.map τ) := (IsFinite.SpecMap_iff τ).mpr (RingHom.finite_algebraMap.mpr ‹_›)
  refine ⟨⟨CommRingCat.of B, X.toSpecΓ ≫ Spec.map ψ, Spec.map τ ≫ Y.isoSpec.inv,
    inferInstance, inferInstance, ?_⟩⟩
  have hτψ : τ ≫ ψ = f.appTop := by
    rw [← f.toNormalization_fromNormalization, Scheme.Hom.comp_appTop]
    rfl
  rw [Category.assoc, ← Spec.map_comp_assoc, hτψ, ← Scheme.toSpecΓ_naturality_assoc]
  change (f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv = f
  simp

end Langlands.AlgebraicGeometry.QuasiFiniteFactorization
