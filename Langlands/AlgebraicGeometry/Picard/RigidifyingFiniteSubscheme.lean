import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedClasses
import Langlands.AlgebraicGeometry.Units.FieldGlobalFunctions
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A finite subscheme detecting global functions after every base change -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifyingSubscheme

open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section Algebra

variable {k C : Type u} [Field k] [CommRing C] [Algebra k C] [Algebra.FiniteType k C]

/-- Powers of a maximal ideal of a finitely generated algebra over a field have
finite-dimensional quotients. -/
lemma finite_quotient_pow (m : Ideal C) [m.IsMaximal] (n : ℕ) :
    Module.Finite k (C ⧸ m ^ n) := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  let := Ideal.Quotient.field m
  have : Module.Finite k (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (C ⧸ m)
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  let φ : C ⧸ m ^ (n + 1) →ₐ[k] C ⧸ m :=
    Ideal.Quotient.factorₐ k (Ideal.pow_le_self n.succ_ne_zero)
  refine Module.finite_of_surjective_of_ker_le_nilradical φ
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self n.succ_ne_zero)) ?_
    (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hc : c ∈ m := by
    rw [RingHom.mem_ker] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  rw [mem_nilradical]
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hc _

omit [Algebra.FiniteType k C] in
/-- Finite-dimensional quotients are stable under intersection of ideals. -/
lemma finite_quotient_inf {I J : Ideal C} (hI : Module.Finite k (C ⧸ I))
    (hJ : Module.Finite k (C ⧸ J)) : Module.Finite k (C ⧸ (I ⊓ J)) := by
  let φ : C ⧸ (I ⊓ J) →ₐ[k] (C ⧸ I) × (C ⧸ J) :=
    (Ideal.Quotient.factorₐ k inf_le_left).prod (Ideal.Quotient.factorₐ k inf_le_right)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h₁ : Ideal.Quotient.mk I c = 0 := congrArg Prod.fst hx
    have h₂ : Ideal.Quotient.mk J c = 0 := congrArg Prod.snd hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂ ⊢
    exact ⟨h₁, h₂⟩
  exact Module.Finite.of_injective φ.toLinearMap hφ

/-- A nonzero element survives in some quotient of finite dimension (Krull's intersection
theorem in a localization at a maximal ideal containing its annihilator). -/
lemma exists_ideal_not_mem (v : C) (hv : v ≠ 0) :
    ∃ I : Ideal C, Module.Finite k (C ⧸ I) ∧ v ∉ I := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  let J : Ideal C := (Submodule.span C {v}).annihilator
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : C) ∈ J := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hv h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have : m.IsPrime := hm.isPrime
  by_contra hcon
  have hpow : ∀ n : ℕ, v ∈ m ^ n := fun n ↦ by
    by_contra h
    exact hcon ⟨m ^ n, finite_quotient_pow m n, h⟩
  let R := Localization.AtPrime m
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hmem : algebraMap C R v ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hpow n)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Submodule.mem_bot] at hmem
  obtain ⟨⟨s, hs⟩, hsv⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl R v).mp hmem
  exact hs (hJm ((Submodule.mem_annihilator_span_singleton _ _).mpr hsv))

/-- **Separating a finite-dimensional subspace.** In a finitely generated algebra over a
field, a finite-dimensional subspace meets some ideal of finite codimension only in `0`. -/
theorem exists_ideal_inf_eq_bot (V : Submodule k C) [FiniteDimensional k V] :
    ∃ I : Ideal C, Module.Finite k (C ⧸ I) ∧ V ⊓ I.restrictScalars k = ⊥ := by
  suffices h : ∀ n : ℕ, ∀ I₀ : Ideal C, Module.Finite k (C ⧸ I₀) →
      Module.finrank k ↥(V ⊓ I₀.restrictScalars k) ≤ n →
        ∃ I : Ideal C, Module.Finite k (C ⧸ I) ∧ V ⊓ I.restrictScalars k = ⊥ from
    h _ ⊤ (by infer_instance) le_rfl
  intro n
  induction n with
  | zero =>
    intro I₀ hI₀ hn
    exact ⟨I₀, hI₀, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)⟩
  | succ n ih =>
    intro I₀ hI₀ hn
    by_cases hbot : V ⊓ I₀.restrictScalars k = ⊥
    · exact ⟨I₀, hI₀, hbot⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨I₁, hI₁, hvI₁⟩ := exists_ideal_not_mem (k := k) v hv0
    refine ih (I₀ ⊓ I₁) (finite_quotient_inf hI₀ hI₁) ?_
    have hle : V ⊓ (I₀ ⊓ I₁).restrictScalars k ≤ V ⊓ I₀.restrictScalars k :=
      inf_le_inf_left _ (fun x hx ↦ (Submodule.mem_inf.mp hx).1)
    have hlt : V ⊓ (I₀ ⊓ I₁).restrictScalars k < V ⊓ I₀.restrictScalars k := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hv' : v ∈ V ⊓ (I₀ ⊓ I₁).restrictScalars k := heq ▸ hv
      exact hvI₁ (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv').2).2
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end Algebra

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f]

/-- Over an affine open `U` of a proper scheme over `k`, there is a finite `k`-scheme mapping
to `X` which detects the restrictions to `U` of global functions. -/
lemma exists_chart (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (Z : Scheme.{u}) (z : Z ⟶ X), IsFinite (z ≫ f) ∧
      ∀ a : Γ(X, ⊤), z.appTop a = 0 → U.ι.appTop a = 0 := by
  have : IsAffine U.toScheme := hU
  let fU : U.toScheme ⟶ Spec (CommRingCat.of k) := U.ι ≫ f
  let := GlobalFunctionsAlgebra.algebra f
  let := GlobalFunctionsAlgebra.algebra fU
  have hft : Algebra.FiniteType k Γ(U.toScheme, ⊤) := by
    have h₁ : (fU.appTop).hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    have h₂ : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    exact h₁.comp h₂
  have hfin : Module.Finite k Γ(X, ⊤) := FieldGlobalFunctions.finite_algebra f
  have hstr : structureRingHom f ≫ U.ι.appTop = structureRingHom fU := by
    simp [structureRingHom, fU]
  let ρ : Γ(X, ⊤) →ₗ[k] Γ(U.toScheme, ⊤) :=
    { toFun := U.ι.appTop
      map_add' := map_add _
      map_smul' := fun c a ↦ by
        change U.ι.appTop (structureRingHom f c * a) = structureRingHom fU c * U.ι.appTop a
        rw [map_mul, ← hstr]
        rfl }
  obtain ⟨I, hI, hVI⟩ := exists_ideal_inf_eq_bot (LinearMap.range ρ)
  let B := CommRingCat.of (Γ(U.toScheme, ⊤) ⧸ I)
  let π : Γ(U.toScheme, ⊤) ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk I)
  refine ⟨Spec B, Spec.map π ≫ inv U.toScheme.toSpecΓ ≫ U.ι, ?_, ?_⟩
  · have heq : (Spec.map π ≫ inv U.toScheme.toSpecΓ ≫ U.ι) ≫ f =
        Spec.map (structureRingHom fU ≫ π) := by
      rw [Category.assoc, Category.assoc, Spec.map_comp]
      change Spec.map π ≫ inv U.toScheme.toSpecΓ ≫ fU = _
      congr 1
      rw [IsIso.inv_comp_eq]
      exact (FieldGlobalUnits.toSpecΓ_over fU).symm
    rw [heq, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hI
  · intro a ha
    have hb : π (U.ι.appTop a) = 0 := by
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.inv_appTop] at ha
      have key : ((U.ι.appTop ≫ inv U.toScheme.toSpecΓ.appTop) ≫ (Spec.map π).appTop) ≫
          (Scheme.ΓSpecIso B).hom = U.ι.appTop ≫ π := by
        rw [Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality,
          ← Scheme.toSpecΓ_appTop, IsIso.inv_hom_id_assoc]
      have h := congrArg (fun m ↦ m a) key
      simp only [CommRingCat.comp_apply] at h
      rw [← h]
      change (Scheme.ΓSpecIso B).hom
        (((U.ι.appTop ≫ inv U.toScheme.toSpecΓ.appTop) ≫ (Spec.map π).appTop) a) = 0
      rw [ha, map_zero]
    have hmem : U.ι.appTop a ∈ LinearMap.range ρ ⊓ I.restrictScalars k :=
      ⟨⟨a, rfl⟩, Ideal.Quotient.eq_zero_iff_mem.mp hb⟩
    rw [hVI] at hmem
    exact hmem

/-- Finitely many affine charts are detected by one finite `k`-scheme. -/
lemma exists_finset (s : Finset X.affineOpens) :
    ∃ (Z : Scheme.{u}) (z : Z ⟶ X), IsFinite (z ≫ f) ∧
      ∀ a : Γ(X, ⊤), z.appTop a = 0 → ∀ U ∈ s, (U : X.Opens).ι.appTop a = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨Z, z, hz, -⟩ := exists_chart f ⊥ (isAffineOpen_bot X)
    exact ⟨Z, z, hz, fun _ _ U hU ↦ absurd hU (Finset.notMem_empty U)⟩
  | insert U s _ ih =>
    obtain ⟨Z₁, z₁, h₁, k₁⟩ := exists_chart f U U.2
    obtain ⟨Z₂, z₂, h₂, k₂⟩ := ih
    refine ⟨Z₁ ⨿ Z₂, coprod.desc z₁ z₂, ?_, ?_⟩
    · rw [coprod.desc_comp]
      infer_instance
    · intro a ha V hV
      have e₁ : z₁.appTop a = 0 := by
        rw [← coprod.inl_desc z₁ z₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha,
          map_zero]
      have e₂ : z₂.appTop a = 0 := by
        rw [← coprod.inr_desc z₁ z₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha,
          map_zero]
      rcases Finset.mem_insert.mp hV with rfl | hV
      · exact k₁ a e₁
      · exact k₂ a e₂ V hV

/-- **A finite `k`-scheme detecting global functions.** A proper scheme over a field
receives a morphism from a scheme finite over the field which is injective on global
functions. -/
theorem exists_finite_injective :
    ∃ (Z : Scheme.{u}) (z : Z ⟶ X), IsFinite (z ≫ f) ∧ Function.Injective z.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen)
    (fun x _ ↦ by
      have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]
        trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨U, hU⟩ := hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  obtain ⟨Z, z, hfin, hker⟩ := exists_finset f s
  refine ⟨Z, z, hfin, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ a 0
  intro x _
  obtain ⟨U, hUs, hxU⟩ : ∃ U ∈ s, x ∈ (U : X.Opens) := by
    simpa using hs (Set.mem_univ x)
  have h0 : (U : X.Opens).ι.appTop a = 0 := hker a ha U hUs
  let y : (U : X.Opens).toScheme := ⟨x, hxU⟩
  have hg := Scheme.Hom.germ_stalkMap_apply (U : X.Opens).ι ⊤ y trivial a
  change _ = (U : X.Opens).toScheme.presheaf.germ _ y _ ((U : X.Opens).ι.appTop a) at hg
  rw [h0, map_zero] at hg
  rw [map_zero]
  exact (ConcreteCategory.bijective_of_isIso ((U : X.Opens).ι.stalkMap y)).1
    (hg.trans (map_zero _).symm)

end Chart

section Injective

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (g : Z ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ X) (hz : z ≫ f = g) [IsProper f] [IsProper g]

open SubschemeRigidification

/-- **Injectivity after every base change.** If `z : Z ⟶ X` over `k` is injective on global
functions, with `X` and `Z` proper over `k`, then so is `T ×_k Z ⟶ T ×_k X` for every test
`T`. Pullback of functions is the base change of a split injection of `k`-vector spaces,
through the published comparison of direct images of structure sheaves. -/
theorem injective_zRel_appTop (hinj : Function.Injective z.appTop)
    (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective ((zRel f g z hz).app T).appTop := by
  let φ := FieldGlobalUnits.sectionsMap f g z hz
  have hφ : Function.Injective φ := fun x y h ↦ by
    apply hinj
    rwa [FieldGlobalUnits.sectionsMap_apply, FieldGlobalUnits.sectionsMap_apply] at h
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective φ.hom (LinearMap.ker_eq_bot.mpr hφ)
  let ρ' := ModuleCat.ofHom ρ
  have hφρ : φ ≫ ρ' = 𝟙 _ := by
    ext x
    exact LinearMap.congr_fun hρ x
  let q := (zRel f g z hz).app T
  have wq : q ≫ pullback.fst T.hom f = pullback.fst T.hom g := zRel_fst f g z hz T
  have hv : q ≫ pullback.snd T.hom f = pullback.snd T.hom g ≫ z := zRel_snd f g z hz T
  have hfa : IsPullback (pullback.snd T.hom f) (pullback.fst T.hom f) f T.hom :=
    (IsPullback.of_hasPullback T.hom f).flip
  have hff : IsPullback (pullback.snd T.hom g) (pullback.fst T.hom g) g T.hom :=
    (IsPullback.of_hasPullback T.hom g).flip
  let eF := FieldGlobalFunctions.directImageSheafMap f T.hom (pullback.snd T.hom f)
    (pullback.fst T.hom f) hfa.w
  let eG := FieldGlobalFunctions.directImageSheafMap g T.hom (pullback.snd T.hom g)
    (pullback.fst T.hom g) hff.w
  have : IsIso eF := FieldGlobalFunctions.isIso_directImageSheafMap f T.hom _ _ hfa
  have : IsIso eG := FieldGlobalFunctions.isIso_directImageSheafMap g T.hom _ _ hff
  let D := FieldGlobalUnits.directImageMap (pullback.fst T.hom f) (pullback.fst T.hom g) q wq
  have hnat := FieldGlobalUnits.directImageSheafMap_naturality f g z hz (pullback.fst T.hom f)
    (pullback.fst T.hom g) q wq T.hom (pullback.snd T.hom g) (pullback.snd T.hom f) hff.w
    hfa.w hv
  let F := tilde.functor (CommRingCat.of k) ⋙ Scheme.Modules.pullback T.hom
  have hD : D = inv eF ≫ F.map φ ≫ eG := by
    rw [IsIso.eq_inv_comp]
    exact hnat.symm
  let r := inv eG ≫ F.map ρ' ≫ eF
  have hDr : D ≫ r = 𝟙 _ := by
    rw [hD]
    simp only [r, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, hφρ, F.map_id, Category.id_comp, IsIso.inv_hom_id]
  intro x y hxy
  have h₁ : D.app ⊤ x = D.app ⊤ y := by
    rw [FieldGlobalUnits.directImageMap_top, FieldGlobalUnits.directImageMap_top]
    exact hxy
  have h₂ := congrArg (r.app ⊤) h₁
  have hid : ∀ w, r.app ⊤ (D.app ⊤ w) = w := fun w ↦ by
    change (D ≫ r).app ⊤ w = w
    rw [hDr]
    rfl
  rwa [hid, hid] at h₂

end Injective

end Langlands.AlgebraicGeometry.Picard.RigidifyingSubscheme
