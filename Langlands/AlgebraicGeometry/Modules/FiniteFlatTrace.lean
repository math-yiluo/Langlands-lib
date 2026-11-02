import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # The trace of a finite flat morphism on sections of a pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace Langlands.Scheme.Modules

section Algebra

/-- Freeness of the standard localization `LocalizedModule S M` over `Localization S` transfers to
every other model `Mₛ` of the localization of `M` over every model `Rₛ` of the localization
of `R`. -/
theorem free_of_isLocalizedModule_of_free {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (S : Submonoid R) {Rₛ Mₛ : Type*} [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ] [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ]
    [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ Mₛ := by
  let b := Module.Free.chooseBasis (Localization S) (LocalizedModule S M)
  let E : Mₛ ≃ₗ[R] (Module.Free.ChooseBasisIndex (Localization S) (LocalizedModule S M) →₀ Rₛ) :=
    (IsLocalizedModule.iso S f).symm ≪≫ₗ b.repr.restrictScalars R ≪≫ₗ
      Finsupp.mapRange.linearEquiv (IsLocalization.algEquiv S (Localization S) Rₛ).toLinearEquiv
  exact Module.Free.of_basis (Module.Basis.ofRepr (E.extendScalarsOfIsLocalization S Rₛ))

end Algebra

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- An open `V` of `Y` is a free chart for `f` if it is affine and `Γ(X, f⁻¹V)` is a free
`Γ(Y, V)`-module, the algebra structure being `f.app V`. -/
def IsFreeChart (V : Y.Opens) : Prop :=
  IsAffineOpen V ∧
    letI := (f.app V).hom.toAlgebra
    Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V)

/-- The trace `Γ(X, f⁻¹V) → Γ(Y, V)` of the algebra `f.app V`. -/
def chartTrace (V : Y.Opens) : Γ(X, f ⁻¹ᵁ V) →+ Γ(Y, V) :=
  letI := (f.app V).hom.toAlgebra
  (Algebra.trace Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).toAddMonoidHom

lemma chartTrace_app_mul (V : Y.Opens) (r : Γ(Y, V)) (a : Γ(X, f ⁻¹ᵁ V)) :
    chartTrace f V (f.app V r * a) = r * chartTrace f V a := by
  let := (f.app V).hom.toAlgebra
  exact (Algebra.trace Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).map_smul r a

/-- Over an affine open, the rank of `Γ(X, f⁻¹V)` at every prime of `Γ(Y, V)` is the rank of
`f`. -/
lemma rankAtStalk_chart [IsFinite f] [Flat f] {d : ℕ} (hd : ∀ y, f.finrank y = d)
    {V : Y.Opens} (hV : IsAffineOpen V) (q : PrimeSpectrum Γ(Y, V)) :
    letI := (f.app V).hom.toAlgebra
    Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) q = d := by
  let := (f.app V).hom.toAlgebra
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hfin := f.finite_app V hV
  have hflat : (f.app V).hom.Flat := by
    simpa only [Scheme.Hom.app_eq_appLE] using f.flat_appLE hV hW le_rfl
  have : IsFinite (Spec.map (f.app V)) := (IsFinite.SpecMap_iff _).mpr hfin
  have : Flat (Spec.map (f.app V)) := Flat.SpecMap_iff.mpr hflat
  have hpb := IsOpenImmersion.isPullback (Spec.map (f.app V)) hW.fromSpec hV.fromSpec f
    (by simpa only [Scheme.Hom.app_eq_appLE] using (hV.SpecMap_appLE_fromSpec f hW le_rfl).symm)
    (by rw [hV.opensRange_fromSpec, hW.opensRange_fromSpec])
  have hr := Scheme.Hom.finrank_of_isPullback hW.fromSpec (Spec.map (f.app V)) f hV.fromSpec
    hpb.flip q
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat, hd] at hr
  exact hr

/-- On a free chart, the trace of `1` is the rank of `f`. -/
lemma chartTrace_one [IsFinite f] [Flat f] {d : ℕ} (hd : ∀ y, f.finrank y = d)
    {V : Y.Opens} (hV : IsFreeChart f V) : chartTrace f V 1 = (d : Γ(Y, V)) := by
  let := (f.app V).hom.toAlgebra
  have : Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hV.2
  rcases subsingleton_or_nontrivial Γ(Y, V) with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum Γ(Y, V)))
    have hq : Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) q = d := rankAtStalk_chart f hd hV.1 q
    simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at hq
    change Algebra.trace Γ(Y, V) Γ(X, f ⁻¹ᵁ V) 1 = _
    rw [← map_one (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)), Algebra.trace_algebraMap, hq, nsmul_one]

/-- The restriction of `Γ(X, f⁻¹V)` to the inverse image of a basic open of `V` is a
localization. -/
lemma isLocalization_preimage_basicOpen [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V)
    (g : Γ(Y, V)) :
    letI := (f.app V).hom.toAlgebra
    letI : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V) (Submonoid.powers g))
      Γ(X, f ⁻¹ᵁ Y.basicOpen g) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  exact (hV.preimage f).isLocalization_of_eq_basicOpen _ _ (f.preimage_basicOpen g)

/-- The trace of a free chart commutes with restriction to a basic open. -/
lemma chartTrace_basicOpen [IsFinite f] {V : Y.Opens} (hV : IsFreeChart f V) (g : Γ(Y, V))
    (a : Γ(X, f ⁻¹ᵁ V)) :
    chartTrace f (Y.basicOpen g)
        (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op a) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (chartTrace f V a) := by
  let := (f.app V).hom.toAlgebra
  let := (f.app (Y.basicOpen g)).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (f.appLE V _ (f.preimage_mono (Y.basicOpen_le g))).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE]
  have : IsLocalization.Away g Γ(Y, Y.basicOpen g) := hV.1.isLocalization_basicOpen g
  have := isLocalization_preimage_basicOpen f hV.1 g
  have : Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hV.2
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV.1
  exact Algebra.trace_localization Γ(Y, V) (Submonoid.powers g) a

/-- Free charts are stable under basic opens. -/
lemma IsFreeChart.basicOpen [IsFinite f] {V : Y.Opens} (hV : IsFreeChart f V) (g : Γ(Y, V)) :
    IsFreeChart f (Y.basicOpen g) := by
  refine ⟨hV.1.basicOpen g, ?_⟩
  let := (f.app V).hom.toAlgebra
  let := (f.app (Y.basicOpen g)).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (f.appLE V _ (f.preimage_mono (Y.basicOpen_le g))).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE]
  have : IsLocalization.Away g Γ(Y, Y.basicOpen g) := hV.1.isLocalization_basicOpen g
  have := isLocalization_preimage_basicOpen f hV.1 g
  have : Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hV.2
  exact Module.Free.of_basis
    ((Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).localizationLocalization
      Γ(Y, Y.basicOpen g) (Submonoid.powers g) Γ(X, f ⁻¹ᵁ Y.basicOpen g))

/-- Free charts cover `Y` when `f` is finite flat of constant rank. -/
lemma exists_isFreeChart [IsFinite f] [Flat f] {d : ℕ} (hd : ∀ y, f.finrank y = d) (y : Y) :
    ∃ V, IsFreeChart f V ∧ y ∈ V := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have h : (f.app V).hom.Flat := by
      simpa only [Scheme.Hom.app_eq_appLE] using f.flat_appLE hV (hV.preimage f) le_rfl
    exact h
  obtain ⟨a, ha, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant
    Γ(X, f ⁻¹ᵁ V) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
    (fun m _ => (rankAtStalk_chart f hd hV _).trans (rankAtStalk_chart f hd hV _).symm)
  refine ⟨Y.basicOpen a, ⟨hV.basicOpen a, ?_⟩, ?_⟩
  · let := (f.app (Y.basicOpen a)).hom.toAlgebra
    let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le a))).op).hom.toAlgebra
    let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
      (f.appLE V _ (f.preimage_mono (Y.basicOpen_le a))).hom.toAlgebra
    have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
      .of_algebraMap_eq' rfl
    have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen a) Γ(X, f ⁻¹ᵁ Y.basicOpen a) :=
      .of_algebraMap_eq' <| by
        simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
          Scheme.Hom.map_appLE]
    have : IsLocalization.Away a Γ(Y, Y.basicOpen a) := hV.isLocalization_basicOpen a
    have : IsLocalizedModule (Submonoid.powers a)
        (IsScalarTower.toAlgHom Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen a)).toLinearMap :=
      isLocalizedModule_iff_isLocalization.mpr (isLocalization_preimage_basicOpen f hV a)
    have : Module.Free (Localization (Submonoid.powers a))
        (LocalizedModule (Submonoid.powers a) Γ(X, f ⁻¹ᵁ V)) := hfree
    exact free_of_isLocalizedModule_of_free (Submonoid.powers a)
      (IsScalarTower.toAlgHom Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen a)).toLinearMap
  · have h1 : hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a := by
      change hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen a
      rw [hV.fromSpec_preimage_basicOpen]
      exact ha
    rwa [hV.fromSpec_primeIdealOf] at h1

section LocalTrace

variable (M : Y.Modules)

/-- The trace on `Γ(X, f⁻¹V) ⊗_{Γ(Y, V)} Γ(M, V)`, `a ⊗ m ↦ tr(a) • m`. -/
def tensorTrace (V : Y.Opens) :
    (ModuleCat.extendScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V)) →+ Γ(M, V) :=
  (TensorProduct.lift (LinearMap.mk₂ Γ(Y, V)
    (fun (a : (ModuleCat.restrictScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
        (ModuleCat.of Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ V))) (m : Γ(M, V)) => chartTrace f V a • m)
    (fun a a' m => by
      show chartTrace f V ((show Γ(X, f ⁻¹ᵁ V) from a) + (show Γ(X, f ⁻¹ᵁ V) from a')) • m = _
      rw [map_add, add_smul])
    (fun r a m => by
      show chartTrace f V ((f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r * show Γ(X, f ⁻¹ᵁ V) from a) • m = _
      rw [← Scheme.Hom.app_eq_appLE, chartTrace_app_mul, mul_smul])
    (fun a m m' => smul_add _ m m')
    (fun r a m => smul_comm _ r m))).toAddMonoidHom

lemma tensorTrace_tmul (V : Y.Opens) (a : Γ(X, f ⁻¹ᵁ V)) (m : Γ(M, V)) :
    tensorTrace f M V (a ⊗ₜ[Γ(Y, V), (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom] m) =
      chartTrace f V a • m :=
  rfl

lemma tensorTrace_smul (V : Y.Opens) (r : Γ(Y, V))
    (z : (ModuleCat.extendScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V))) :
    tensorTrace f M V (f.app V r • z) = r • tensorTrace f M V z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a m =>
    rw [ModuleCat.ExtendScalars.smul_tmul, tensorTrace_tmul, tensorTrace_tmul, chartTrace_app_mul,
      mul_smul]

variable [M.IsQuasicoherent]

/-- Over an affine open `V`, sections of `f_* f^* M` are `Γ(X, f⁻¹V) ⊗_{Γ(Y, V)} Γ(M, V)`. -/
def pullbackTensorEquiv [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V) :
    (ModuleCat.extendScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V)) ≃ₗ[Γ(X, f ⁻¹ᵁ V)]
        Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) :=
  LinearEquiv.ofBijective (pullbackTensorMap f M (le_refl (f ⁻¹ᵁ V))).hom
    (pullbackTensorMap_bijective f M _ (hV.preimage f) hV)

lemma pullbackTensorEquiv_apply [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V)
    (z : (ModuleCat.extendScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V))) :
    pullbackTensorEquiv f M hV z = pullbackTensorMap f M (le_refl (f ⁻¹ᵁ V)) z :=
  rfl

/-- The trace `Γ(f_* f^* M, V) → Γ(M, V)` over an affine open `V`. -/
def localTrace [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V) :
    Γ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M), V) →ₗ[Γ(Y, V)] Γ(M, V) where
  toFun z := tensorTrace f M V ((pullbackTensorEquiv f M hV).symm z)
  map_add' z z' := by
    show tensorTrace f M V ((pullbackTensorEquiv f M hV).symm
      ((show Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) from z) +
        (show Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) from z'))) = _
    rw [map_add, map_add]
  map_smul' r z := by
    show tensorTrace f M V ((pullbackTensorEquiv f M hV).symm
      (f.app V r • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) from z))) =
        r • _
    rw [map_smul, tensorTrace_smul]

lemma localTrace_pullbackTensorMap [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V)
    (z : (ModuleCat.extendScalars (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom).obj
      (ModuleCat.of Γ(Y, V) Γ(M, V))) :
    localTrace f M hV (pullbackTensorMap f M (le_refl (f ⁻¹ᵁ V)) z) = tensorTrace f M V z := by
  show tensorTrace f M V ((pullbackTensorEquiv f M hV).symm (pullbackTensorEquiv f M hV z)) = _
  rw [LinearEquiv.symm_apply_apply]

lemma localTrace_smul_sectionPullbackLE [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V)
    (a : Γ(X, f ⁻¹ᵁ V)) (m : Γ(M, V)) :
    localTrace f M hV (a • sectionPullbackLE f M (le_refl (f ⁻¹ᵁ V)) m) = chartTrace f V a • m := by
  rw [← pullbackTensorMap_tmul, localTrace_pullbackTensorMap, tensorTrace_tmul]

/-- On a free chart, the local trace of a pulled-back section is `d` times the section. -/
lemma localTrace_sectionPullback [IsFinite f] [Flat f] {d : ℕ} (hd : ∀ y, f.finrank y = d)
    {V : Y.Opens} (hV : IsFreeChart f V) (m : Γ(M, V)) :
    localTrace f M hV.1 (sectionPullback f M V m) = d • m := by
  rw [← sectionPullbackLE_self, ← pullbackTensorMap_one_tmul, localTrace_pullbackTensorMap,
    tensorTrace_tmul, chartTrace_one f hd hV, Nat.cast_smul_eq_nsmul]

/-- The local trace of a free chart commutes with restriction to a basic open. -/
lemma localTrace_basicOpen [IsFinite f] {V : Y.Opens} (hV : IsFreeChart f V) (g : Γ(Y, V))
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M), V)) :
    localTrace f M (IsFreeChart.basicOpen f hV g).1
        (((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).presheaf.map
            (homOfLE (Y.basicOpen_le g)).op z) =
      M.presheaf.map (homOfLE (Y.basicOpen_le g)).op (localTrace f M hV.1 z) := by
  obtain ⟨w, rfl⟩ :=
    (pullbackTensorMap_bijective f M (le_refl (f ⁻¹ᵁ V)) (hV.1.preimage f) hV.1).2 z
  induction w using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]
  | tmul a m =>
    rw [pullbackTensorMap_tmul, localTrace_smul_sectionPullbackLE]
    show localTrace f M (IsFreeChart.basicOpen f hV g).1
      (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map
        (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op
          ((show Γ(X, f ⁻¹ᵁ V) from a) • sectionPullbackLE f M (le_refl (f ⁻¹ᵁ V)) m)) = _
    rw [AlgebraicGeometry.Scheme.Modules.map_smul
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M),
      map_sectionPullbackLE,
      ← sectionPullbackLE_restrict f M (Y.basicOpen_le g) (le_refl (f ⁻¹ᵁ Y.basicOpen g)) m,
      localTrace_smul_sectionPullbackLE, chartTrace_basicOpen f hV g a,
      AlgebraicGeometry.Scheme.Modules.map_smul M]

end LocalTrace

end Langlands.Scheme.Modules
