/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorUnits
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The extension of `μ_m` by itself attached to a `ℤ/m`-torsor

Let `t` be a `ℤ/m`-torsor over a scheme `Y` with total space `π : P ⟶ Y`, and let
`V = π_* μ_m ⊆ π_* 𝔾ₘ` be the sheaf of `m`-th roots of unity on `P`, pushed forward to `Y`. The
generator `1 ∈ ℤ/m` acts on `V` by translation `τ`; put `D = τ - 𝟙`. Then
`K₁ = ker D` is the sheaf `μ_m` of the base (`AlgebraicGeometry.Scheme.EtaleTorsor.isIso_muUnit`)
and `K₂ = ker D²` is an extension

`0 ⟶ K₁ ⟶ K₂ --D--> K₁ ⟶ 0`

(`AlgebraicGeometry.Scheme.EtaleTorsor.extSeq_shortExact`). Locally, where the torsor is trivial,
`V` is the sheaf of functions `ℤ/m → μ_m`, `τ` is the shift, `K₁` the constant functions and `K₂`
the affine functions `a ↦ x + a • c`; the extension is the one by which `π₁` acts on `K₂` through
the monodromy character of `t`. Its connecting homomorphism `H¹(Y, μ_m) ⟶ H²(Y, μ_m)` is the cup
product with the class of `t`, up to sign.

The sheaf `V` maps onto `K₂` by `ρ = ∑_{i < m} i • τ^i`
(`AlgebraicGeometry.Scheme.EtaleTorsor.epi_rhoK`), which is how the second cohomology of the
extension is controlled by that of the total space `P`.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.pushforwardMu`: `π_* μ_m`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.muDiff`: `D = τ - 𝟙` on `π_* μ_m`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.extSeq`: the short complex `K₁ ⟶ K₂ ⟶ K₁`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.muUnit`: the identification `μ_m ⟶ K₁`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.extSeq_shortExact`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.isIso_muUnit`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.epi_rhoK`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

/-! ### The short complex `ker D ⟶ ker D² ⟶ ker D` -/

namespace CategoryTheory

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {V : 𝒜} (D : V ⟶ V)

/-- The inclusion `ker D ⟶ ker D²`. -/
noncomputable def kernelToKernelComp : kernel D ⟶ kernel (D ≫ D) :=
  kernel.lift _ (kernel.ι D) (by rw [kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
lemma kernelToKernelComp_ι : kernelToKernelComp D ≫ kernel.ι (D ≫ D) = kernel.ι D :=
  kernel.lift_ι _ _ _

/-- The map `ker D² ⟶ ker D` induced by `D`. -/
noncomputable def kernelCompToKernel : kernel (D ≫ D) ⟶ kernel D :=
  kernel.lift _ (kernel.ι (D ≫ D) ≫ D) (by rw [Category.assoc, kernel.condition])

@[reassoc (attr := simp)]
lemma kernelCompToKernel_ι : kernelCompToKernel D ≫ kernel.ι D = kernel.ι (D ≫ D) ≫ D :=
  kernel.lift_ι _ _ _

instance : Mono (kernelToKernelComp D) := mono_of_mono_fac (kernelToKernelComp_ι D)

/-- The short complex `ker D ⟶ ker D² --D--> ker D` of an endomorphism `D`. -/
@[simps]
noncomputable def kernelSqShortComplex : ShortComplex 𝒜 :=
  ShortComplex.mk (kernelToKernelComp D) (kernelCompToKernel D) (by
    rw [← cancel_mono (kernel.ι D)]
    simp)

/-- The short complex `ker D ⟶ ker D² --D--> ker D` is exact: an element of `ker D²` killed by
`D` lies in `ker D`. -/
lemma kernelSqShortComplex_exact : (kernelSqShortComplex D).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun x hx ↦ kernel.lift D (x ≫ kernel.ι (D ≫ D)) ?_) (fun x hx ↦ ?_) (fun x hx g hg ↦ ?_))
  · have := hx =≫ kernel.ι D
    simpa using this
  · rw [← cancel_mono (kernel.ι (D ≫ D))]
    simp
  · rw [← cancel_mono (kernel.ι D), kernel.lift_ι, ← hg, Category.assoc]
    simp

/-- If `D : ker D² ⟶ ker D` is an epimorphism, `ker D ⟶ ker D² ⟶ ker D` is short exact. -/
lemma kernelSqShortComplex_shortExact [Epi (kernelCompToKernel D)] :
    (kernelSqShortComplex D).ShortExact where
  exact := kernelSqShortComplex_exact D
  mono_f := inferInstanceAs (Mono (kernelToKernelComp D))
  epi_g := inferInstanceAs (Epi (kernelCompToKernel D))

end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

/-! ### Sections of kernels of étale sheaves -/

section Kernel

variable {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

lemma injective_kernel_ι_app (φ : F ⟶ G) (U : X.Etaleᵒᵖ) :
    Function.Injective ((kernel.ι φ).hom.app U) := by
  have : Mono ((sheafToPresheaf _ _).map (kernel.ι φ)) := inferInstance
  have : Mono ((kernel.ι φ).hom.app U) :=
    inferInstanceAs (Mono (((sheafToPresheaf _ _).map (kernel.ι φ)).app U))
  exact (AddCommGrpCat.mono_iff_injective _).1 this

lemma exists_kernel_ι_app_eq (φ : F ⟶ G) {U : X.Etale} (x : F.obj.obj (op U))
    (hx : φ.hom.app (op U) x = 0) :
    ∃ y : (kernel φ).obj.obj (op U), (kernel.ι φ).hom.app (op U) y = x := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj (op U)
  let e := PreservesKernel.iso E φ ≪≫ AddCommGrpCat.kernelIsoKer (E.map φ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E φ
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map φ)
  change (e.inv ≫ E.map (kernel.ι φ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

lemma kernel_ι_app_apply_eq_zero (φ : F ⟶ G) (U : X.Etaleᵒᵖ) (y : (kernel φ).obj.obj U) :
    φ.hom.app U ((kernel.ι φ).hom.app U y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← InducedCategory.comp_hom,
    kernel.condition]
  rfl

lemma app_apply_comp (φ : F ⟶ G) {H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) (U : X.Etaleᵒᵖ) (x : F.obj.obj U) :
    (φ ≫ ψ).hom.app U x = ψ.hom.app U (φ.hom.app U x) :=
  rfl

end Kernel

/-! ### The covering by the total space -/

section Cover

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}} (t : EtaleTorsor M Y)

/-- The étale `Y`-scheme `U ×_Y P`, over which the torsor has the tautological section. -/
noncomputable def coverObj (U : Y.Etale) : Y.Etale :=
  MorphismProperty.Over.mk ⊤ (pullback.fst U.hom t.π ≫ U.hom) (by
    have := U.prop
    have := t.etale
    infer_instance)

/-- The étale covering `U ×_Y P ⟶ U`. -/
noncomputable def coverArrow (U : Y.Etale) : t.coverObj U ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom t.π) rfl

lemma coverArrow_left (U : Y.Etale) : (t.coverArrow U).left = pullback.fst U.hom t.π := rfl

/-- The tautological section of the torsor over `U ×_Y P`. -/
lemma coverObj_section (U : Y.Etale) :
    pullback.snd U.hom t.π ≫ t.π = (t.coverObj U).hom :=
  pullback.condition.symm

/-- A sieve containing the covering `U ×_Y P ⟶ U` is a covering sieve. -/
lemma mem_smallEtaleTopology_of_coverArrow {U : Y.Etale} (R : Sieve U)
    (h : R (t.coverArrow U)) : R ∈ Y.smallEtaleTopology U := by
  refine GrothendieckTopology.superset_covering _ ?_
    ((ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ t.coverArrow U)).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨⟨⟩⟩
    exact h
  · have : Surjective (pullback.fst U.hom t.π) := by
      have := t.surjective
      infer_instance
    rw [Set.iUnion_const, coverArrow_left]
    exact Set.range_eq_univ.2 (pullback.fst U.hom t.π).surjective

end Cover

/-! ### The extension -/

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m] (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y)

lemma comp_nsmul_id {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) (n : ℕ) : f ≫ (n • 𝟙 G) = (n • 𝟙 F) ≫ f := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

/-- `D = τ - 𝟙` on `π_* 𝔾ₘ`, for the translation `τ` by the generator `1 ∈ ℤ/m`. -/
noncomputable def gmDiff : t.pushforwardGm ⟶ t.pushforwardGm :=
  t.pushforwardGmTranslate 1 - 𝟙 _

/-- The sheaf `π_* μ_m` of `m`-th roots of unity on the total space, as the `m`-torsion of
`π_* 𝔾ₘ`. -/
noncomputable abbrev pushforwardMu : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (m • 𝟙 t.pushforwardGm)

lemma nsmul_kernel_ι_pushforwardMu : m • kernel.ι (m • 𝟙 t.pushforwardGm) = 0 := by
  have := kernel.condition (m • 𝟙 t.pushforwardGm)
  rwa [Preadditive.comp_nsmul, Category.comp_id] at this

/-- `D = τ - 𝟙` on `π_* μ_m`. -/
noncomputable def muDiff : t.pushforwardMu ⟶ t.pushforwardMu :=
  kernel.lift _ (kernel.ι _ ≫ t.gmDiff) (by
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma muDiff_ι : t.muDiff ≫ kernel.ι _ = kernel.ι _ ≫ t.gmDiff :=
  kernel.lift_ι _ _ _

/-- The short complex `K₁ ⟶ K₂ --D--> K₁` with `K₁ = ker D` and `K₂ = ker D²` on `π_* μ_m`. -/
noncomputable abbrev extSeq : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  kernelSqShortComplex t.muDiff

/-- The map `μ_m ⟶ π_* μ_m` pulling back roots of unity from the base. -/
noncomputable def muUnitV : Y.rootsOfUnitySheaf m ⟶ t.pushforwardMu :=
  kernel.map _ _ t.pushforwardGmUnit t.pushforwardGmUnit (by
    rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp])

/-- The map `μ_m ⟶ K₁ = ker D`: roots of unity pulled back from the base are invariant. -/
noncomputable def muUnit : Y.rootsOfUnitySheaf m ⟶ kernel t.muDiff :=
  kernel.lift _ t.muUnitV (by
    rw [← cancel_mono (kernel.ι (m • 𝟙 t.pushforwardGm)), Category.assoc, muDiff_ι, muUnitV,
      kernel.lift_ι_assoc, Category.assoc, gmDiff, Preadditive.comp_sub,
      pushforwardGmUnit_comp_translate, Category.comp_id, sub_self, comp_zero, zero_comp])

/-! ### Local computations -/

section Algebra

variable {A : Type*} [AddCommGroup A]

omit [AddCommGroup A] in
/-- A function on `ℤ/m` invariant under the shift by `-1` is constant. -/
lemma apply_eq_apply_zero_of_forall_sub_one {F : ULift.{u + 1} (ZMod m) → A}
    (h : ∀ a, F (a - 1) = F a)
    (a : ULift.{u + 1} (ZMod m)) : F a = F 0 := by
  have key (k : ℕ) : F ⟨-(k : ZMod m)⟩ = F 0 := by
    induction k with
    | zero => exact congrArg F (ULift.ext (by simp))
    | succ k ih =>
      rw [← ih, ← h ⟨-(k : ZMod m)⟩]
      congr 1
      apply ULift.ext
      change -((k + 1 : ℕ) : ZMod m) = -(k : ZMod m) - 1
      push_cast
      ring
  rw [← key (-a.down).val, ZMod.natCast_zmod_val, neg_neg]

/-- The character `ℤ/m → A`, `k ↦ k • c`, of an element `c` with `m • c = 0`. -/
noncomputable def zmodChar (c : A) (hc : m • c = 0) : ZMod m →+ A :=
  ZMod.lift m ⟨zmultiplesHom A c, by simpa [natCast_zsmul] using hc⟩

omit [NeZero m] in
lemma zmodChar_one (c : A) (hc : m • c = 0) : zmodChar c hc 1 = c := by
  have := ZMod.lift_coe m ⟨zmultiplesHom A c, by simpa [natCast_zsmul] using hc⟩ 1
  simpa [zmodChar] using this

omit [NeZero m] in
lemma nsmul_zmodChar (c : A) (hc : m • c = 0) (k : ZMod m) : m • zmodChar c hc k = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

end Algebra

/-- Evaluation of morphisms of abelian sheaves at a section is additive in the morphism. -/
noncomputable def homAppAddHom {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (U : X.Etaleᵒᵖ) (x : F.obj.obj U) : (F ⟶ G) →+ G.obj.obj U where
  toFun f := f.hom.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

lemma gmDiff_app (U : Y.Etaleᵒᵖ) (x : t.pushforwardGm.obj.obj U) :
    t.gmDiff.hom.app U x = (t.pushforwardGmTranslate 1).hom.app U x - x :=
  map_sub (homAppAddHom U x) _ _

lemma nsmul_id_app {X : Scheme.{u}} {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (n : ℕ) (U : X.Etaleᵒᵖ) (x : F.obj.obj U) : (n • 𝟙 F).hom.app U x = n • x :=
  map_nsmul (homAppAddHom U x) n (𝟙 F)

section LocalTrivialization

variable {U : Y.Etale} (σ : U.left ⟶ t.P) (hσ : σ ≫ t.π = U.hom)

lemma localUnits_gmDiff (a : ULift.{u + 1} (ZMod m)) (x : t.pushforwardGm.obj.obj (op U)) :
    t.localUnits σ hσ a (t.gmDiff.hom.app (op U) x) =
      t.localUnits σ hσ (a - 1) x - t.localUnits σ hσ a x := by
  rw [gmDiff_app, map_sub, localUnits_translate]

include σ hσ in
/-- Over an étale `U` with a section of the torsor, an `m`-torsion section of `π_* 𝔾ₘ` killed by
`D` comes from a root of unity on `U`, and is `D` of an `m`-torsion section. -/
lemma exists_of_gmDiff_eq_zero (x : t.pushforwardGm.obj.obj (op U)) (hx : m • x = 0)
    (hDx : t.gmDiff.hom.app (op U) x = 0) :
    ∃ c : Y.gmSheaf.obj.obj (op U), m • c = 0 ∧ t.pushforwardGmUnit.hom.app (op U) c = x ∧
      ∃ y : t.pushforwardGm.obj.obj (op U), m • y = 0 ∧ t.gmDiff.hom.app (op U) y = x := by
  set F := fun a ↦ t.localUnits σ hσ a x
  have hF (a : ULift.{u + 1} (ZMod m)) : F a = F 0 := by
    refine apply_eq_apply_zero_of_forall_sub_one (fun a ↦ ?_) a
    have := t.localUnits_gmDiff σ hσ a x
    rw [hDx, map_zero] at this
    exact sub_eq_zero.1 this.symm
  set c := F 0
  have hc : m • c = 0 := by
    change m • t.localUnits σ hσ 0 x = 0
    rw [← map_nsmul, hx, map_zero]
  refine ⟨ULift.up c, ?_, ?_, ?_⟩
  · exact ULift.ext hc
  · refine t.localUnits_injective σ hσ fun a ↦ ?_
    rw [localUnits_unit]
    exact (hF a).symm
  · obtain ⟨y, hy⟩ := t.exists_localUnits σ hσ (fun a ↦ zmodChar c hc (-a.down))
    refine ⟨y, t.localUnits_injective σ hσ fun a ↦ ?_, t.localUnits_injective σ hσ fun a ↦ ?_⟩
    · rw [map_nsmul, hy, map_zero, nsmul_zmodChar]
    · rw [localUnits_gmDiff, hy, hy, ← map_sub]
      refine (?_ : _ = c).trans (hF a).symm
      convert zmodChar_one c hc using 2
      change -(a.down - 1) - -a.down = 1
      ring

end LocalTrivialization

/-! ### Exactness and the identification of `ker D` -/

lemma epi_extSeq_g : Epi t.extSeq.g := by
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology t.extSeq.g.hom := ⟨fun {U} s ↦ by
    apply t.mem_smallEtaleTopology_of_coverArrow
    set U' := t.coverObj U
    set s' := (kernel t.muDiff).obj.map (t.coverArrow U).op s
    set v := (kernel.ι t.muDiff).hom.app (op U') s'
    set w := (kernel.ι (m • 𝟙 t.pushforwardGm)).hom.app (op U') v
    have hw : m • w = 0 := by
      rw [← nsmul_id_app]
      exact kernel_ι_app_apply_eq_zero _ _ _
    have hv : t.muDiff.hom.app (op U') v = 0 := kernel_ι_app_apply_eq_zero _ _ _
    have hDw : t.gmDiff.hom.app (op U') w = 0 := by
      change (kernel.ι _ ≫ t.gmDiff).hom.app (op U') v = 0
      rw [← muDiff_ι, app_apply_comp, hv, map_zero]
    obtain ⟨-, -, -, y, hy, hDy⟩ := t.exists_of_gmDiff_eq_zero (pullback.snd U.hom t.π)
      (t.coverObj_section U) w hw hDw
    obtain ⟨v', hv'⟩ := exists_kernel_ι_app_eq (m • 𝟙 t.pushforwardGm) y
      (by rw [nsmul_id_app, hy])
    have hDv' : t.muDiff.hom.app (op U') v' = v := by
      apply injective_kernel_ι_app
      rw [← app_apply_comp, muDiff_ι, app_apply_comp, hv', hDy]
    obtain ⟨k, hk⟩ := exists_kernel_ι_app_eq (t.muDiff ≫ t.muDiff) v'
      (by rw [app_apply_comp, hDv', hv])
    refine ⟨k, injective_kernel_ι_app _ _ ?_⟩
    change (kernelCompToKernel t.muDiff ≫ kernel.ι _).hom.app _ k = v
    rw [kernelCompToKernel_ι, app_apply_comp, hk, hDv']⟩
  exact Sheaf.epi_of_isLocallySurjective t.extSeq.g

lemma isIso_muUnit : IsIso t.muUnit := by
  have hι : t.muUnit ≫ kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm) =
      kernel.ι (m • 𝟙 Y.gmSheaf) ≫ t.pushforwardGmUnit := by
    simp [muUnit, muUnitV]
  have : Mono t.pushforwardGmUnit := by
    have : Presheaf.IsLocallyInjective Y.smallEtaleTopology t.pushforwardGmUnit.hom :=
      ⟨fun {U} x y hxy ↦ by
        apply t.mem_smallEtaleTopology_of_coverArrow
        change Y.gmSheaf.obj.map (t.coverArrow U.unop).op x =
          Y.gmSheaf.obj.map (t.coverArrow U.unop).op y
        have h := congrArg (t.pushforwardGm.obj.map (t.coverArrow U.unop).op) hxy
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at h
        have h' := congrArg (t.localUnits (pullback.snd U.unop.hom t.π)
          (t.coverObj_section U.unop) 0) h
        rw [localUnits_unit, localUnits_unit] at h'
        exact ULift.ext h'⟩
    exact Sheaf.mono_of_isLocallyInjective _
  have : Mono t.muUnit := by
    have : Mono (t.muUnit ≫ kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm)) := by
      rw [hι]
      infer_instance
    exact mono_of_mono t.muUnit (kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm))
  have : Epi t.muUnit := by
    have : Presheaf.IsLocallySurjective Y.smallEtaleTopology t.muUnit.hom := ⟨fun {U} s ↦ by
      apply t.mem_smallEtaleTopology_of_coverArrow
      set U' := t.coverObj U
      set s' := (kernel t.muDiff).obj.map (t.coverArrow U).op s
      set v := (kernel.ι t.muDiff).hom.app (op U') s'
      set w := (kernel.ι (m • 𝟙 t.pushforwardGm)).hom.app (op U') v
      have hw : m • w = 0 := by
        rw [← nsmul_id_app]
        exact kernel_ι_app_apply_eq_zero _ _ _
      have hv : t.muDiff.hom.app (op U') v = 0 := kernel_ι_app_apply_eq_zero _ _ _
      have hDw : t.gmDiff.hom.app (op U') w = 0 := by
        change (kernel.ι _ ≫ t.gmDiff).hom.app (op U') v = 0
        rw [← muDiff_ι, app_apply_comp, hv, map_zero]
      obtain ⟨c, hc, hcw, -⟩ := t.exists_of_gmDiff_eq_zero (pullback.snd U.hom t.π)
        (t.coverObj_section U) w hw hDw
      obtain ⟨r, hr⟩ := exists_kernel_ι_app_eq (m • 𝟙 Y.gmSheaf) c (by rw [nsmul_id_app, hc])
      refine ⟨r, injective_kernel_ι_app _ _ (injective_kernel_ι_app _ _ ?_)⟩
      change (t.muUnit ≫ kernel.ι t.muDiff ≫ kernel.ι (m • 𝟙 t.pushforwardGm)).hom.app _ r = w
      rw [hι, app_apply_comp]
      exact (congrArg _ hr).trans hcw⟩
    exact Sheaf.epi_of_isLocallySurjective t.muUnit
  exact isIso_of_mono_of_epi _

lemma extSeq_shortExact : t.extSeq.ShortExact :=
  haveI : Epi (kernelCompToKernel t.muDiff) := t.epi_extSeq_g
  kernelSqShortComplex_shortExact t.muDiff


/-! ### The surjection `ρ : π_* μ_m ⟶ ker D²` -/

/-- Translation by `i • 1`. -/
noncomputable abbrev transl (i : ℕ) : t.pushforwardGm ⟶ t.pushforwardGm :=
  t.pushforwardGmTranslate (i • (1 : ULift.{u + 1} (ZMod m)))

lemma transl_succ (i : ℕ) : t.transl (i + 1) = t.transl i ≫ t.pushforwardGmTranslate 1 := by
  rw [transl, transl, succ_nsmul, pushforwardGmTranslate_add, pushforwardGmTranslate_comm]

lemma transl_self : t.transl m = 𝟙 _ := by
  have : m • (1 : ULift.{u + 1} (ZMod m)) = 0 :=
    ULift.ext (by change m • (1 : ZMod m) = 0; simp)
  rw [transl, this, pushforwardGmTranslate_zero]

/-- `ρ = ∑_{i < m} i • τ^i` on `π_* 𝔾ₘ`. -/
noncomputable def rhoW : t.pushforwardGm ⟶ t.pushforwardGm :=
  ∑ i ∈ Finset.range m, i • t.transl i

/-- The norm `N = ∑_{i < m} τ^{i + 1}`. -/
noncomputable def normW : t.pushforwardGm ⟶ t.pushforwardGm :=
  ∑ i ∈ Finset.range m, t.transl (i + 1)

lemma rhoW_comp_gmDiff : t.rhoW ≫ t.gmDiff = m • 𝟙 _ - t.normW := by
  have h1 : t.rhoW ≫ t.gmDiff =
      (∑ i ∈ Finset.range m, i • t.transl (i + 1)) - ∑ i ∈ Finset.range m, i • t.transl i := by
    simp only [rhoW, gmDiff, Preadditive.comp_sub, Preadditive.sum_comp, Preadditive.nsmul_comp,
      Category.comp_id, transl_succ]
  have h2 : ∑ i ∈ Finset.range m, i • t.transl (i + 1) =
      ∑ i ∈ Finset.range m, (i + 1) • t.transl (i + 1) - t.normW := by
    simp only [normW, succ_nsmul, Finset.sum_add_distrib, add_sub_cancel_right]
  have h3 : ∑ i ∈ Finset.range m, (i + 1) • t.transl (i + 1) =
      ∑ i ∈ Finset.range m, i • t.transl i + m • t.transl m := by
    have := Finset.sum_range_succ' (fun i ↦ i • t.transl i) m
    simp only [zero_nsmul, add_zero] at this
    rw [← this, Finset.sum_range_succ]
  rw [h1, h2, h3, transl_self]
  abel

lemma normW_comp_gmDiff : t.normW ≫ t.gmDiff = 0 := by
  have : t.normW ≫ t.gmDiff =
      ∑ i ∈ Finset.range m, (t.transl (i + 1 + 1) - t.transl (i + 1)) := by
    simp only [normW, gmDiff, Preadditive.comp_sub, Preadditive.sum_comp, Category.comp_id,
      ← transl_succ, Finset.sum_sub_distrib]
  rw [this, Finset.sum_range_sub (fun i ↦ t.transl (i + 1)), transl_succ, transl_self,
    zero_add, Category.id_comp]
  simp [transl]

lemma rhoW_comp_gmDiff_comp_gmDiff : t.rhoW ≫ t.gmDiff ≫ t.gmDiff = m • t.gmDiff := by
  rw [← Category.assoc, rhoW_comp_gmDiff, Preadditive.sub_comp, normW_comp_gmDiff, sub_zero,
    Preadditive.nsmul_comp, Category.id_comp]

/-- `ρ` on `π_* μ_m`. -/
noncomputable def rhoV : t.pushforwardMu ⟶ t.pushforwardMu :=
  kernel.lift _ (kernel.ι _ ≫ t.rhoW) (by
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc (attr := simp)]
lemma rhoV_ι : t.rhoV ≫ kernel.ι _ = kernel.ι _ ≫ t.rhoW :=
  kernel.lift_ι _ _ _

/-- `ρ : π_* μ_m ⟶ K₂ = ker D²`. -/
noncomputable def rhoK : t.pushforwardMu ⟶ kernel (t.muDiff ≫ t.muDiff) :=
  kernel.lift _ t.rhoV (by
    rw [← cancel_mono (kernel.ι (m • 𝟙 t.pushforwardGm)), Category.assoc, Category.assoc,
      muDiff_ι, muDiff_ι_assoc, rhoV_ι_assoc, rhoW_comp_gmDiff_comp_gmDiff,
      Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, t.nsmul_kernel_ι_pushforwardMu,
      zero_comp, zero_comp])


/-! ### Surjectivity of `ρ` -/

section Algebra

variable {A : Type*} [AddCommGroup A]

lemma zmodChar_apply (c : A) (hc : m • c = 0) (k : ZMod m) : zmodChar c hc k = k.val • c := by
  have h := ZMod.lift_coe m ⟨zmultiplesHom A c, by simpa [natCast_zsmul] using hc⟩ (k.val : ℤ)
  have hk : ((k.val : ℤ) : ZMod m) = k := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hk] at h
  rw [zmodChar, h]
  exact natCast_zsmul c k.val

/-- A function on `ℤ/m` whose differences `F (a - 1) - F a` are constant is affine. -/
lemma eq_sub_zmodChar_of_forall_sub_one {F : ULift.{u + 1} (ZMod m) → A} {e : A}
    (he : m • e = 0) (hF : ∀ a, F (a - 1) - F a = e) (a : ULift.{u + 1} (ZMod m)) :
    F a = F 0 - zmodChar e he a.down := by
  let G : ULift.{u + 1} (ZMod m) → A := fun a ↦ F a - (F 0 - zmodChar e he a.down)
  have hG : ∀ a, G (a - 1) = G a := fun a ↦ by
    have h1 : zmodChar e he (a - 1).down = zmodChar e he a.down - e := by
      change zmodChar e he (a.down - 1) = _
      rw [map_sub, zmodChar_one]
    simp only [G, h1]
    have := hF a
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  have := apply_eq_apply_zero_of_forall_sub_one hG a
  simp only [G, sub_self, show (0 : ULift.{u + 1} (ZMod m)).down = 0 from rfl, map_zero,
    sub_zero] at this
  exact sub_eq_zero.1 this

lemma sum_nsmul_single (a b : ULift.{u + 1} (ZMod m)) (z : A) (hz : m • z = 0) :
    ∑ i ∈ Finset.range m, i • (Pi.single b z : ULift.{u + 1} (ZMod m) → A)
      (a - i • (1 : ULift.{u + 1} (ZMod m))) = zmodChar z hz (a - b).down := by
  classical
  have hcast (i : ℕ) : (i • (1 : ULift.{u + 1} (ZMod m))).down = (i : ZMod m) := by
    change i • (1 : ZMod m) = _
    rw [nsmul_one]
  rw [Finset.sum_eq_single (a - b).down.val, zmodChar_apply]
  · congr 1
    have : a - (a - b).down.val • (1 : ULift.{u + 1} (ZMod m)) = b := by
      apply ULift.ext
      change a.down - ((a - b).down.val • (1 : ULift.{u + 1} (ZMod m))).down = b.down
      rw [hcast, ZMod.natCast_zmod_val]
      change a.down - (a.down - b.down) = b.down
      ring
    rw [this, Pi.single_eq_same]
  · intro i hi hne
    rw [Pi.single_eq_of_ne, smul_zero]
    intro h
    apply hne
    have h' : (i : ZMod m) = (a - b).down := by
      rw [← hcast]
      congr 1
      rw [← h, sub_sub_cancel]
    rw [← h', ZMod.val_natCast_of_lt (Finset.mem_range.1 hi)]
  · intro h
    exact absurd (Finset.mem_range.2 (ZMod.val_lt _)) h

end Algebra

lemma rhoW_app (U : Y.Etaleᵒᵖ) (x : t.pushforwardGm.obj.obj U) :
    t.rhoW.hom.app U x = ∑ i ∈ Finset.range m, i • (t.transl i).hom.app U x := by
  change homAppAddHom U x (∑ i ∈ Finset.range m, i • t.transl i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_nsmul (homAppAddHom U x) i _

lemma exists_rhoW_eq {U : Y.Etale} (σ : U.left ⟶ t.P) (hσ : σ ≫ t.π = U.hom)
    (x : t.pushforwardGm.obj.obj (op U)) (hx : m • x = 0)
    (hDDx : t.gmDiff.hom.app (op U) (t.gmDiff.hom.app (op U) x) = 0) :
    ∃ y : t.pushforwardGm.obj.obj (op U), m • y = 0 ∧ t.rhoW.hom.app (op U) y = x := by
  classical
  set F := fun a ↦ t.localUnits σ hσ a x
  have hFm (a : ULift.{u + 1} (ZMod m)) : m • F a = 0 := by
    change m • t.localUnits σ hσ a x = 0
    rw [← map_nsmul, hx, map_zero]
  -- the differences of `F` are constant
  set G := fun a ↦ t.localUnits σ hσ a (t.gmDiff.hom.app (op U) x)
  have hG (a : ULift.{u + 1} (ZMod m)) : G a = G 0 := by
    refine apply_eq_apply_zero_of_forall_sub_one (fun a ↦ ?_) a
    have := t.localUnits_gmDiff σ hσ a (t.gmDiff.hom.app (op U) x)
    rw [hDDx, map_zero] at this
    exact sub_eq_zero.1 this.symm
  set e := G 0
  have he : m • e = 0 := by
    change m • t.localUnits σ hσ 0 (t.gmDiff.hom.app (op U) x) = 0
    rw [← map_nsmul, ← map_nsmul, hx, map_zero, map_zero]
  have hF (a : ULift.{u + 1} (ZMod m)) : F a = F 0 - zmodChar e he a.down := by
    refine eq_sub_zmodChar_of_forall_sub_one he (fun a ↦ ?_) a
    exact (t.localUnits_gmDiff σ hσ a x).symm.trans (hG a)
  set c₀ := F 0 - e
  set c₁ := -F 0
  have hc₀ : m • c₀ = 0 := by simp only [c₀, nsmul_sub, hFm, he, sub_zero]
  have hc₁ : m • c₁ = 0 := by simp only [c₁, smul_neg, hFm, neg_zero]
  obtain ⟨y, hy⟩ := t.exists_localUnits σ hσ (Pi.single 0 c₀ + Pi.single 1 c₁)
  refine ⟨y, t.localUnits_injective σ hσ fun a ↦ ?_, t.localUnits_injective σ hσ fun a ↦ ?_⟩
  · rw [map_nsmul, hy, map_zero]
    simp only [Pi.add_apply, nsmul_add]
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp [hc₀, hc₁]
  · rw [rhoW_app, map_sum]
    simp only [map_nsmul, transl, localUnits_translate, hy, Pi.add_apply, nsmul_add,
      Finset.sum_add_distrib]
    rw [sum_nsmul_single a 0 c₀ hc₀, sum_nsmul_single a 1 c₁ hc₁]
    refine Eq.trans ?_ (hF a).symm
    change zmodChar c₀ hc₀ (a.down - 0) + zmodChar c₁ hc₁ (a.down - 1) = _
    rw [sub_zero, map_sub, zmodChar_one]
    have hlin (k : ZMod m) : zmodChar c₀ hc₀ k + zmodChar c₁ hc₁ k = -zmodChar e he k := by
      rw [zmodChar_apply, zmodChar_apply, zmodChar_apply, ← nsmul_add, ← smul_neg]
      congr 1
      simp only [c₀, c₁]
      abel
    calc zmodChar c₀ hc₀ a.down + (zmodChar c₁ hc₁ a.down - c₁)
        = (zmodChar c₀ hc₀ a.down + zmodChar c₁ hc₁ a.down) - c₁ := by abel
      _ = F 0 - zmodChar e he a.down := by rw [hlin]; simp only [c₁]; abel

lemma epi_rhoK : Epi t.rhoK := by
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology t.rhoK.hom := ⟨fun {U} s ↦ by
    apply t.mem_smallEtaleTopology_of_coverArrow
    set U' := t.coverObj U
    set s' := (kernel (t.muDiff ≫ t.muDiff)).obj.map (t.coverArrow U).op s
    set v := (kernel.ι (t.muDiff ≫ t.muDiff)).hom.app (op U') s'
    set w := (kernel.ι (m • 𝟙 t.pushforwardGm)).hom.app (op U') v
    have hw : m • w = 0 := by
      rw [← nsmul_id_app]
      exact kernel_ι_app_apply_eq_zero _ _ _
    have hv : (t.muDiff ≫ t.muDiff).hom.app (op U') v = 0 := kernel_ι_app_apply_eq_zero _ _ _
    have hDDw : t.gmDiff.hom.app (op U') (t.gmDiff.hom.app (op U') w) = 0 := by
      change (kernel.ι _ ≫ t.gmDiff ≫ t.gmDiff).hom.app (op U') v = 0
      rw [← muDiff_ι_assoc, ← muDiff_ι, ← Category.assoc, app_apply_comp, hv, map_zero]
    obtain ⟨y, hy, hρy⟩ := t.exists_rhoW_eq (pullback.snd U.hom t.π) (t.coverObj_section U)
      w hw hDDw
    obtain ⟨v', hv'⟩ := exists_kernel_ι_app_eq (m • 𝟙 t.pushforwardGm) y
      (by rw [nsmul_id_app, hy])
    refine ⟨v', injective_kernel_ι_app _ _ (injective_kernel_ι_app _ _ ?_)⟩
    change (t.rhoK ≫ kernel.ι _ ≫ kernel.ι (m • 𝟙 t.pushforwardGm)).hom.app _ v' = w
    rw [rhoK, kernel.lift_ι_assoc, rhoV_ι, app_apply_comp, hv', hρy]⟩
  exact Sheaf.epi_of_isLocallySurjective t.rhoK

/-! ### The connecting homomorphism -/

/-- The connecting homomorphism `H¹(Y, μ_m) ⟶ H²(Y, μ_m)` of the extension `0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0`
attached to the torsor. Up to sign it is the cup product with the class of the torsor. -/
noncomputable def cupMu :
    Sheaf.H (Y.rootsOfUnitySheaf m) 1 →+ Sheaf.H (Y.rootsOfUnitySheaf m) 2 :=
  haveI := t.isIso_muUnit
  ((Sheaf.H.map (inv t.muUnit) 2).comp (Sheaf.H.δSucc t.extSeq_shortExact 1)).comp
    (Sheaf.H.map t.muUnit 1)

end AlgebraicGeometry.Scheme.EtaleTorsor
