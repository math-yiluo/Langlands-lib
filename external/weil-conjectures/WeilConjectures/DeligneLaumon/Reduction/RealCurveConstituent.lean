/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.ConstantExtension
public import WeilConjectures.WeilSheaf.RealPurity
public import WeilConjectures.WeilSheaf.StalkAtPurity

/-!
# Purity of the irreducible constituents of real lisse sheaves on smooth affine schemes

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 2` over a finite
field `k₀` and `𝒢` an `ι`-real lisse Weil sheaf on `X₀`. Every irreducible lisse subquotient of
`𝒢` is punctually `ι`-pure (blueprint `theorem-real-constructible-sheaves-are-mixed--1`, the lisse
stratum).

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_of_mono_cokernel`: on a
  curve, an irreducible lisse subsheaf of a lisse subquotient of a real lisse sheaf is pure.
-/

@[expose] public section

universe u

open CategoryTheory Limits

-- As in `WeilConjectures.WeilSheaf.CurvePullback`: elaborating through these instances produces
-- terms which the kernel compares slowly with the imported ones.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

namespace FrobeniusModule

variable {K : Type*} [Field K] {ι : K →+* ℂ} {q : ℕ} {w w' : ℝ}

/-- `M` is `ι`-pure of weight `w` relative to `q` *on the subspace `U`*: every eigenvector of
the Frobenius lying in `U` has an eigenvalue `α` with `|ι α| = q ^ (w / 2)`. -/
def IsPureOfWeightOn (ι : K →+* ℂ) (q : ℕ) (M : FrobeniusModule.{u} K)
    (U : Submodule K M.carrier) (w : ℝ) : Prop :=
  ∀ (α : K) (x : M.carrier), x ∈ U → x ≠ 0 → M.frobenius x = α • x → ‖ι α‖ = (q : ℝ) ^ (w / 2)

/-- The image of an injective Frobenius-equivariant map from a pure module is pure. -/
theorem IsPureOfWeight.isPureOfWeightOn_range {M N : FrobeniusModule.{u} K}
    (h : N.IsPureOfWeight ι q w) (f : N.carrier →ₗ[K] M.carrier)
    (hf : ∀ x, f (N.frobenius x) = M.frobenius (f x)) (hinj : Function.Injective f) :
    M.IsPureOfWeightOn ι q (LinearMap.range f) w := by
  rintro α _ ⟨y, rfl⟩ hy hα
  refine h α (Module.End.hasEigenvalue_of_hasEigenvector (x := y) ?_)
  refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hinj ?_), ?_⟩
  · rw [map_smul, ← hα, ← hf]
    rfl
  · rintro rfl
    exact hy (map_zero f)

/-- Purity on a subspace is transported along an isomorphism of Frobenius modules. -/
theorem IsPureOfWeightOn.map {M N : FrobeniusModule.{u} K} {U : Submodule K M.carrier}
    (h : M.IsPureOfWeightOn ι q U w) (e : M.carrier ≃ₗ[K] N.carrier)
    (he : ∀ x, e (M.frobenius x) = N.frobenius (e x)) :
    N.IsPureOfWeightOn ι q (U.map e.toLinearMap) w := by
  rintro α _ ⟨y, hy, rfl⟩ hy0 hα
  refine h α y hy (fun h0 ↦ hy0 (by simp [h0])) (e.injective ?_)
  rw [he, map_smul]
  exact hα

/-- Purity on a subspace descends along an isomorphism of Frobenius modules. -/
theorem IsPureOfWeightOn.of_map {M N : FrobeniusModule.{u} K} {U : Submodule K M.carrier}
    (e : M.carrier ≃ₗ[K] N.carrier) (he : ∀ x, e (M.frobenius x) = N.frobenius (e x))
    (h : N.IsPureOfWeightOn ι q (U.map e.toLinearMap) w) : M.IsPureOfWeightOn ι q U w := by
  intro α x hx hx0 hα
  refine h α (e x) ⟨x, hx, rfl⟩ (fun h0 ↦ hx0 (e.injective (h0.trans (map_zero e).symm))) ?_
  rw [← he, hα, map_smul]

/-- Purity on a subspace is transported along an isomorphism of Frobenius modules, to a subspace
known to be the image. -/
theorem IsPureOfWeightOn.map_eq {M N : FrobeniusModule.{u} K} {U : Submodule K M.carrier}
    {U' : Submodule K N.carrier} (h : M.IsPureOfWeightOn ι q U w) (e : M.carrier ≃ₗ[K] N.carrier)
    (he : ∀ x, e (M.frobenius x) = N.frobenius (e x)) (hU : U.map e.toLinearMap = U') :
    N.IsPureOfWeightOn ι q U' w :=
  hU ▸ h.map e he

/-- Purity on a subspace descends along an isomorphism of Frobenius modules, from a subspace
known to be the image. -/
theorem IsPureOfWeightOn.of_map_eq {M N : FrobeniusModule.{u} K} {U : Submodule K M.carrier}
    {U' : Submodule K N.carrier} (e : M.carrier ≃ₗ[K] N.carrier)
    (he : ∀ x, e (M.frobenius x) = N.frobenius (e x)) (hU : U.map e.toLinearMap = U')
    (h : N.IsPureOfWeightOn ι q U' w) : M.IsPureOfWeightOn ι q U w :=
  of_map e he (hU ▸ h)

/-- The weight of a module pure on a nonzero Frobenius-stable subspace is unique. -/
theorem IsPureOfWeightOn.weight_eq [IsAlgClosed K] {M : FrobeniusModule.{u} K}
    {U : Submodule K M.carrier} (h : M.IsPureOfWeightOn ι q U w)
    (h' : M.IsPureOfWeightOn ι q U w') (hU : U ≠ ⊥) (hUs : ∀ x ∈ U, M.frobenius x ∈ U)
    (hq : 1 < q) : w = w' := by
  let T : Module.End K U := M.frobeniusEnd.restrict hUs
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue T
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have hx' : M.frobenius x = α • (x : M.carrier) := congrArg Subtype.val hx.1
  have hx0 : (x : M.carrier) ≠ 0 := fun h0 ↦ hx.2 (Subtype.ext h0)
  have e := (h α x x.2 hx0 hx').symm.trans (h' α x x.2 hx0 hx')
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have := (Real.rpow_right_inj (by linarith) hq'.ne').1 e
  linarith [this]

/-- The weight of a nonzero pure Frobenius module is unique. -/
theorem IsPureOfWeight.weight_eq [IsAlgClosed K] {M : FrobeniusModule.{u} K}
    [Nontrivial M.carrier] (h : M.IsPureOfWeight ι q w) (h' : M.IsPureOfWeight ι q w')
    (hq : 1 < q) : w = w' := by
  have hp (w : ℝ) (h : M.IsPureOfWeight ι q w) : M.IsPureOfWeightOn ι q ⊤ w :=
    fun α x _ hx0 hα ↦ h α (Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hα, hx0⟩))
  exact (hp w h).weight_eq (hp w' h') top_ne_bot (fun _ _ ↦ trivial) hq

/-- A module which is pure on the whole space is pure. -/
theorem isPureOfWeightOn_top_iff {M : FrobeniusModule.{u} K} :
    M.IsPureOfWeightOn ι q ⊤ w ↔ M.IsPureOfWeight ι q w := by
  refine ⟨fun h α hα ↦ ?_, fun h α x _ hx0 hα ↦ h α (Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hα, hx0⟩))⟩
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  exact h α x trivial hx.2 hx.1

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Curve

variable {ι : PadicAlgCl l →+* ℂ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Purity of real lisse sheaves on curves**, subobject form (blueprint:
`theorem-purity-real-sheaves-curves--1`, as used in
`theorem-real-constructible-sheaves-are-mixed--1`). Let `C₀` be a smooth geometrically connected
curve over `k₀`, `𝒢` an `ι`-real lisse Weil sheaf on `C₀` and `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢` lisse subsheaves. Every
irreducible lisse subsheaf `W` of `𝒢₂ / 𝒢₁` is punctually `ι`-pure: it is the irreducible
constituent `P / K` of `𝒢`, where `P ⊆ 𝒢₂` is the preimage of `W` and `K ⊆ P` the kernel of
`P ⟶ W`. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_of_mono_cokernel {𝒢 : WeilSheaf k₀ l C}
    (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂)
    (j : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse)
    {W : WeilSheaf k₀ l C} (u : W ⟶ cokernel i) [Mono u] (hW : W.IsIrreducibleLisse) :
    ∃ w : ℝ, W.IsPunctuallyPureOfWeight ι w := by
  have hc : (cokernel i).IsLisse := (IsLisse.kernel_cokernel h₁ h₂ i).2
  -- the preimage `P ⊆ 𝒢₂` of `W`, a kernel of a morphism of lisse sheaves
  have hP : (pullback (cokernel.π i) u).IsLisse := by
    have h := (IsLisse.kernel_cokernel (h₂.biprod hW.1) hc
      (biprod.desc (cokernel.π i) (-u))).1
    have hl := Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct (cokernel.π i) u
    have e := IsLimit.conePointUniqueUpToIso (kernelIsKernel _) hl
    exact h.of_iso e
  have hK : (kernel (pullback.snd (cokernel.π i) u)).IsLisse :=
    (IsLisse.kernel_cokernel hP hW.1 _).1
  -- `W` is the cokernel of `K ⟶ P`
  let e : cokernel (kernel.ι (pullback.snd (cokernel.π i) u)) ≅ W :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel _))
  have hirr : (cokernel (kernel.ι (pullback.snd (cokernel.π i) u))).IsIrreducibleLisse := by
    refine ⟨hW.1.of_iso e.symm, fun h ↦ hW.2.1 (h.of_iso e.symm), fun G f hf hG ↦ ?_⟩
    rcases hW.2.2 G (f ≫ e.hom) inferInstance hG with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using (inferInstance : IsIso ((f ≫ e.hom) ≫ e.inv)))
  obtain ⟨w, hw⟩ := hreal.exists_isPunctuallyPureOfWeight_cokernel h𝒢
    (kernel.ι (pullback.snd (cokernel.π i) u)) (pullback.fst (cokernel.π i) u ≫ j) hK hP hirr
  exact ⟨w, hw.of_epi e.hom⟩

/-- **Purity of real lisse sheaves on curves**, subobject form for any cokernel cofork: every
irreducible lisse subsheaf of a cokernel `c` of `𝒢₁ ⟶ 𝒢₂`, for lisse `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢` with `𝒢`
real, is punctually pure
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_of_mono_cokernel`). -/
theorem IsReal.exists_isPunctuallyPureOfWeight_of_mono_of_isColimit {𝒢 : WeilSheaf k₀ l C}
    (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂)
    (j : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse)
    {c : CokernelCofork i} (hc : IsColimit c) {W : WeilSheaf k₀ l C} (u : W ⟶ c.pt) [Mono u]
    (hW : W.IsIrreducibleLisse) :
    ∃ w : ℝ, W.IsPunctuallyPureOfWeight ι w := by
  have e := hc.coconePointUniqueUpToIso (cokernelIsCokernel i)
  have : Mono (u ≫ e.hom) := mono_comp _ _
  exact hreal.exists_isPunctuallyPureOfWeight_of_mono_cokernel h𝒢 i j h₁ h₂ (u ≫ e.hom) hW

/-- **Purity of real lisse sheaves on curves**, for the image of a subquotient under an exact
functor `G` to Weil sheaves on the curve: every irreducible lisse subsheaf of `G V`, where
`V = 𝒢₂ / 𝒢₁` and `G` preserves this cokernel, is punctually pure as soon as `G 𝒢₁ ⊆ G 𝒢₂ ⊆ G 𝒢`
are lisse and `G 𝒢` is real. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_of_mono_obj {D : Type*} [Category D]
    [HasZeroMorphisms D] (G : D ⥤ WeilSheaf k₀ l C) [G.PreservesZeroMorphisms]
    {𝒢 𝒢₁ 𝒢₂ V : D} (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) (π : 𝒢₂ ⟶ V) (hπ : i ≫ π = 0)
    (hV : IsColimit (CokernelCofork.ofπ π hπ)) [PreservesColimit (parallelPair i 0) G]
    [Mono (G.map i)] [Mono (G.map j)] (h𝒢 : (G.obj 𝒢).IsLisse) (hreal : (G.obj 𝒢).IsReal ι)
    (h₁ : (G.obj 𝒢₁).IsLisse) (h₂ : (G.obj 𝒢₂).IsLisse) {W : WeilSheaf k₀ l C}
    (u : W ⟶ G.obj V) [Mono u] (hW : W.IsIrreducibleLisse) :
    ∃ w : ℝ, W.IsPunctuallyPureOfWeight ι w :=
  hreal.exists_isPunctuallyPureOfWeight_of_mono_of_isColimit h𝒢 (G.map i) (G.map j) h₁ h₂
    (CokernelCofork.mapIsColimit _ hV G) u hW
end Curve

section CurvePoint

variable {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Algebra k₀ L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))]
  (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      Module.finrank k₀ L).asIso.hom =
    (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L)

include hj in
/-- The iterates of `j ≫ Fr^N = Fr_Y ≫ j`. -/
theorem comp_geometricGaloisFrobenius_pow_finrank_mul (n : ℕ) :
    j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (Module.finrank k₀ L * n)).asIso.hom =
      ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom ≫ j := by
  induction n with
  | zero =>
    rw [Nat.mul_zero, pow_zero, pow_zero]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
    rw [Nat.mul_succ, ← Aut.pow_hom_comp_pow_hom, reassoc_of% hj, ih, pow_succ, Aut.mul_asIso,
      Iso.trans_hom, Category.assoc]

include hj in
/-- A geometric point `s'` of `Ȳ` over a geometric point `s` of `X̄` fixed by `Fr^{N n}` up to
reparametrisation is fixed by `Fr_Yⁿ` up to reparametrisation, `j` being a monomorphism. -/
theorem comp_geometricGaloisFrobenius_pow_of_comp_eq [Mono j]
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hss' : s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫ s) {n : ℕ}
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (Module.finrank k₀ L * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (Module.finrank k₀ L * n)).asIso.hom ≫ s) :
    s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s' := by
  rw [← cancel_mono j, Category.assoc, ← comp_geometricGaloisFrobenius_pow_finrank_mul j hj,
    reassoc_of% hss', hs, Category.assoc, hss', specAlgHomAlgebraicClosureIso_hom,
    specGeometricFrobenius_pow_hom_comp_spec_map_algHom_assoc]

end CurvePoint

end AlgebraicGeometry.WeilSheaf
