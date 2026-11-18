import Langlands.Geometry.Analytic.SeparatedAnalytificationDensity
import Langlands.Geometry.Analytic.SchemeAnalytificationBasicOpenRangeProof
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # A Hausdorff analytification forces separatedness -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.SeparatedReverse

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

section Seminorm

variable {A D : Type*} [CommRing A] [CommRing D]

/-- The multiplicative seminorm `a ↦ ν (φ a)` pulled back along a ring homomorphism. -/
def comap (ν : MulRingSeminorm D) (φ : A →+* D) : MulRingSeminorm A where
  toFun a := ν (φ a)
  map_zero' := by simp
  add_le' a b := by simpa using map_add_le_add ν (φ a) (φ b)
  neg' a := by simp
  map_one' := by simp
  map_mul' a b := by simp

@[simp] theorem comap_apply (ν : MulRingSeminorm D) (φ : A →+* D) (a : A) :
    comap ν φ a = ν (φ a) := rfl

end Seminorm

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- Two points of the analytifications of affine opens `U` and `V` whose seminorms come
from one seminorm `ν` through compatible maps have the same image in the glued space,
provided `ν` does not vanish at the section `u` cutting out a principal open
`W = D(u) ⊆ U ∩ V`. -/
theorem ι_eq_of_seminorm (U V : X.affineOpens) (u : Γ(X, U.val))
    (hWV : ((X.affineBasicOpen u : X.affineOpens) : X.Opens) ≤ V)
    {D L : Type*} [CommRing D] [CommRing L]
    (φ₁ : CoordinateRing (structureMap f U) →+* D) (φ₂ : CoordinateRing (structureMap f V) →+* D)
    (θ : CoordinateRing (structureMap f (X.affineBasicOpen u)) →+* L) (j : D →+* L)
    (hj : Function.Injective j)
    (h₁ : ∀ a, θ (restriction f (X.affineBasicOpen_le u) a) = j (φ₁ a))
    (h₂ : ∀ b, θ (restriction f hWV b) = j (φ₂ b))
    (ν : MulRingSeminorm D) (hν : ν (φ₁ (CenterRange.basicOpenGenerator f U u)) ≠ 0)
    (a : LocalSpace K f U) (b : LocalSpace K f V)
    (ha : ∀ x, AffineAnalytification.pointSeminorm K (chartPresentation K f U) a x = ν (φ₁ x))
    (hb : ∀ y, AffineAnalytification.pointSeminorm K (chartPresentation K f V) b y = ν (φ₂ y)) :
    ι K f U a = ι K f V b := by
  set u' := CenterRange.basicOpenGenerator f U u with hu'
  have hW : a ∈ Set.range (localMap K f (X.affineBasicOpen_le u)) := by
    rw [OpenGluing.range_localMap_basicOpen K f U u, Set.mem_preimage, SetLike.mem_coe,
      CenterRange.localCenter_mem_basicOpen, ha]
    exact hν
  obtain ⟨w, rfl⟩ := hW
  have hw : ∀ t, AffineAnalytification.pointSeminorm K
      (chartPresentation K f (X.affineBasicOpen u)) w
      (restriction f (X.affineBasicOpen_le u) t) = ν (φ₁ t) := fun t => by
    rw [← AffineAnalytification.pointSeminorm_baseMap, ← ha]
    rfl
  have key : localMap K f hWV w = b := by
    apply AffineAnalytification.SeminormComparison.pointSeminorm_injective K
      (chartPresentation K f V)
    ext y
    change AffineAnalytification.pointSeminorm K _
      (AffineAnalytification.baseMap K _ _ (restriction f hWV) w) y = _
    rw [AffineAnalytification.pointSeminorm_baseMap, hb]
    let := (restriction f (X.affineBasicOpen_le u)).toRingHom.toAlgebra
    have := CenterRange.isLocalization_restriction_basicOpen f U u
    obtain ⟨⟨x, s, hs⟩, hx⟩ := IsLocalization.surj (Submonoid.powers u') (restriction f hWV y)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hs
    change restriction f hWV y * restriction f (X.affineBasicOpen_le u) (u' ^ n) =
      restriction f (X.affineBasicOpen_le u) x at hx
    have e1 := congrArg (AffineAnalytification.pointSeminorm K
      (chartPresentation K f (X.affineBasicOpen u)) w) hx
    rw [map_mul, hw, hw] at e1
    have e2 : φ₂ y * φ₁ (u' ^ n) = φ₁ x := hj (by
      rw [map_mul, ← h₁, ← h₂, ← h₁, ← map_mul, hx])
    have e3 := congrArg ν e2
    rw [map_mul] at e3
    have hne : ν (φ₁ (u' ^ n)) ≠ 0 := by
      rw [map_pow, map_pow]
      exact pow_ne_zero _ hν
    exact mul_right_cancel₀ hne (e1.trans e3.symm)
  rw [ι_localMap, ← key, ι_localMap]

/-- A seminorm extending the norm of `K` through a `K`-algebra map gives a point of the
analytification of an affine open. -/
theorem exists_pointSeminorm_eq (U : X.affineOpens) {D : Type*} [CommRing D] [Algebra K D]
    (φ : CoordinateRing (structureMap f U) →ₐ[K] D) (ν : MulRingSeminorm D)
    (hν : ∀ c : K, ν (algebraMap K D c) = ‖c‖) :
    ∃ a : LocalSpace K f U, ∀ x,
      AffineAnalytification.pointSeminorm K (chartPresentation K f U) a x = ν (φ x) := by
  have hmem : comap ν φ.toRingHom ∈
      Set.range (AffineAnalytification.pointSeminorm K (chartPresentation K f U)) := by
    rw [AffineAnalytification.SeminormComparison.range_pointSeminorm]
    intro c
    change ν (φ (algebraMap K _ c)) = ‖c‖
    rw [φ.commutes, hν]
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, fun x => by rw [ha]; rfl⟩

/-- **Closure transfer.** If the glued space is Hausdorff, then for a domain `D` of finite
type over `K` receiving compatible maps from the coordinate rings of `U`, `V` and of a
principal open `D(u) ⊆ U ∩ V`, and for every proper ideal `I` of `D`, there are points of
the analytifications of `U` and `V` with the same image in the glued space whose
seminorms vanish on the preimages of `I`. -/
theorem exists_ι_eq [T2Space (Space K f)] (U V : X.affineOpens) (u : Γ(X, U.val))
    (hWV : ((X.affineBasicOpen u : X.affineOpens) : X.Opens) ≤ V)
    {D L : Type*} [CommRing D] [IsDomain D] [Algebra K D] [Algebra.FiniteType K D]
    [CommRing L]
    (φ₁ : CoordinateRing (structureMap f U) →ₐ[K] D)
    (φ₂ : CoordinateRing (structureMap f V) →ₐ[K] D)
    (θ : CoordinateRing (structureMap f (X.affineBasicOpen u)) →+* L) (j : D →+* L)
    (hj : Function.Injective j)
    (h₁ : ∀ a, θ (restriction f (X.affineBasicOpen_le u) a) = j (φ₁ a))
    (h₂ : ∀ b, θ (restriction f hWV b) = j (φ₂ b))
    (I : Ideal D) (hI : I ≠ ⊤) (hg : φ₁ (CenterRange.basicOpenGenerator f U u) ≠ 0) :
    ∃ (a : LocalSpace K f U) (b : LocalSpace K f V), ι K f U a = ι K f V b ∧
      (∀ x, φ₁ x ∈ I →
        AffineAnalytification.pointSeminorm K (chartPresentation K f U) a x = 0) ∧
      (∀ y, φ₂ y ∈ I →
        AffineAnalytification.pointSeminorm K (chartPresentation K f V) b y = 0) := by
  obtain ⟨η, hηK, hηI, hηcl⟩ :=
    SeparatedAnalytificationDensity.exists_mulRingSeminorm_mem_closure (K := K) I hI hg
  set E₁ := fun (x : LocalSpace K f U) (a : CoordinateRing (structureMap f U)) =>
    AffineAnalytification.pointSeminorm K (chartPresentation K f U) x a with hE₁
  set E₂ := fun (x : LocalSpace K f V) (a : CoordinateRing (structureMap f V)) =>
    AffineAnalytification.pointSeminorm K (chartPresentation K f V) x a with hE₂
  have hE : IsInducing (Prod.map E₁ E₂) :=
    (AffineAnalytification.SeminormComparison.isEmbedding_pointSeminorm K
      (chartPresentation K f U)).isInducing.prodMap
      (AffineAnalytification.SeminormComparison.isEmbedding_pointSeminorm K
        (chartPresentation K f V)).isInducing
  have hC : IsClosed {p : LocalSpace K f U × LocalSpace K f V | ι K f U p.1 = ι K f V p.2} :=
    isClosed_eq ((ι K f U).continuous.comp continuous_fst)
      ((ι K f V).continuous.comp continuous_snd)
  obtain ⟨Z, hZ, hCZ⟩ := hE.isClosed_iff.mp hC
  let ρ : (D → ℝ) → (CoordinateRing (structureMap f U) → ℝ) ×
      (CoordinateRing (structureMap f V) → ℝ) :=
    fun h => (fun x => h (φ₁ x), fun y => h (φ₂ y))
  have hρ : Continuous ρ :=
    (continuous_pi fun x => continuous_apply (φ₁ x)).prodMk
      (continuous_pi fun y => continuous_apply (φ₂ y))
  have key : ∀ ν : MulRingSeminorm D, (∀ c : K, ν (algebraMap K D c) = ‖c‖) →
      ∀ (a : LocalSpace K f U) (b : LocalSpace K f V),
      (∀ x, AffineAnalytification.pointSeminorm K (chartPresentation K f U) a x = ν (φ₁ x)) →
      (∀ y, AffineAnalytification.pointSeminorm K (chartPresentation K f V) b y = ν (φ₂ y)) →
      ((a, b) ∈ Prod.map E₁ E₂ ⁻¹' Z ↔ ρ ⇑ν ∈ Z) := by
    intro ν _ a b ha hb
    have : Prod.map E₁ E₂ (a, b) = ρ ⇑ν := by
      ext x
      · exact ha x
      · exact hb x
    rw [Set.mem_preimage, this]
  have hS : {h : D → ℝ | ∃ ν : MulRingSeminorm D,
      (∀ c : K, ν (algebraMap K D c) = ‖c‖) ∧ ν (φ₁ (CenterRange.basicOpenGenerator f U u)) ≠ 0 ∧
        ⇑ν = h} ⊆ ρ ⁻¹' Z := by
    rintro _ ⟨ν, hνK, hνg, rfl⟩
    obtain ⟨a, ha⟩ := exists_pointSeminorm_eq K f U φ₁ ν hνK
    obtain ⟨b, hb⟩ := exists_pointSeminorm_eq K f V φ₂ ν hνK
    have hab : ι K f U a = ι K f V b :=
      ι_eq_of_seminorm K f U V u hWV φ₁.toRingHom φ₂.toRingHom θ j hj h₁ h₂ ν hνg a b ha hb
    rw [Set.mem_preimage, ← key ν hνK a b ha hb, hCZ]
    exact hab
  have hη : ρ ⇑η ∈ Z := closure_minimal hS (hZ.preimage hρ) hηcl
  obtain ⟨a, ha⟩ := exists_pointSeminorm_eq K f U φ₁ η hηK
  obtain ⟨b, hb⟩ := exists_pointSeminorm_eq K f V φ₂ η hηK
  refine ⟨a, b, ?_, fun x hx => by rw [ha]; exact hηI _ hx, fun y hy => by rw [hb]; exact hηI _ hy⟩
  have hab := (key η hηK a b ha hb).mpr hη
  rw [hCZ] at hab
  exact hab

section Valuative

variable {K}

/-- A morphism from an affine scheme whose image lies in an affine open `U` factors as
`Spec` of a ring map out of the global sections of `U`, followed by `affineOpenMap U`. -/
theorem exists_eq_spec_map_comp (U : X.affineOpens) {R : CommRingCat.{u}} (l : Spec R ⟶ X)
    (hl : Set.range l ⊆ ((U : X.Opens) : Set X)) :
    ∃ ψ : Γ((U : X.Opens), ⊤) ⟶ R, l = Spec.map ψ ≫ affineOpenMap U := by
  have hl' : Set.range l ⊆ Set.range (U : X.Opens).ι := by
    rwa [Scheme.Opens.range_ι]
  let l' := IsOpenImmersion.lift (U : X.Opens).ι l hl'
  refine ⟨Spec.preimage (l' ≫ (U : X.Opens).toScheme.isoSpec.hom), ?_⟩
  rw [Spec.map_preimage, affineOpenMap, Category.assoc, Iso.hom_inv_id_assoc,
    IsOpenImmersion.lift_fac]

instance (U : X.affineOpens) : IsOpenImmersion (affineOpenMap U) := by
  rw [affineOpenMap]
  infer_instance

/-- `affineOpenMap` is compatible with restriction of global sections. -/
theorem spec_map_comp_affineOpenMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    Spec.map (X.homOfLE h).appTop ≫ affineOpenMap U = affineOpenMap V := by
  rw [affineOpenMap, affineOpenMap, Scheme.isoSpec_inv_naturality_assoc, X.homOfLE_ι]

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- `affineOpenMap U` lies over `Spec K` through the scalar action on the coordinate
ring of `U`. -/
theorem affineOpenMap_comp (U : X.affineOpens) :
    affineOpenMap U ≫ f = Spec.algebraMap K (CoordinateRing (structureMap f U)) := by
  have h := (Iso.eq_inv_comp (coordinateIso (structureMap f U))).mpr
    (coordinateIso_hom_over (structureMap f U))
  rw [affineOpenMap, Category.assoc]
  exact h.symm

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- Two factorizations through `affineOpenMap` of a common morphism, one through `U` and
one through a smaller affine open `W`, are related by restriction. -/
theorem restriction_eq_of_spec_map {U W : X.affineOpens} (h : (W : X.Opens) ≤ U)
    {R T : CommRingCat.{u}} (ψ : Γ((U : X.Opens), ⊤) ⟶ R) (θ : Γ((W : X.Opens), ⊤) ⟶ T)
    (ρ : R ⟶ T) (e : Spec.map ρ ≫ Spec.map ψ ≫ affineOpenMap U = Spec.map θ ≫ affineOpenMap W)
    (a : CoordinateRing (structureMap f U)) :
    θ.hom (restriction f h a) = ρ.hom (ψ.hom a) := by
  rw [← spec_map_comp_affineOpenMap h, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, cancel_mono] at e
  have e' := Spec.map_injective e
  exact (ConcreteCategory.congr_hom e' a).symm

variable (K) in
/-- **Uniqueness part of the valuative criterion.** If the analytification of `X` is
Hausdorff, then every valuative square over `f` has at most one lift. -/
theorem valuativeCriterion_uniqueness [T2Space (Space K f)] :
    ValuativeCriterion.Uniqueness f := by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp only
  have hcover : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let cp : Spec (CommRingCat.of S.R) := IsLocalRing.closedPoint S.R
  have hrange : ∀ (l : Spec (CommRingCat.of S.R) ⟶ X) (U : X.Opens), l cp ∈ U →
      Set.range l ⊆ (U : Set X) := by
    rintro l U h _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map l.continuous).mem_open U.2 h
  obtain ⟨U, hU⟩ := hcover (l₁ cp)
  obtain ⟨V, hV⟩ := hcover (l₂ cp)
  obtain ⟨ψ₁, hψ₁⟩ := exists_eq_spec_map_comp U l₁ (hrange l₁ U hU)
  obtain ⟨ψ₂, hψ₂⟩ := exists_eq_spec_map_comp V l₂ (hrange l₂ V hV)
  -- the generic point
  let ξ : Spec (CommRingCat.of S.K) := (default : PrimeSpectrum S.K)
  have hmem : ∀ (l : Spec (CommRingCat.of S.R) ⟶ X) (U : X.Opens), l cp ∈ U →
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ → S.i₁ ξ ∈ U := by
    intro l U h e
    rw [← e, Scheme.Hom.comp_apply]
    exact hrange l U h ⟨_, rfl⟩
  have hξU := hmem l₁ U hU hl₁
  have hξV := hmem l₂ V hV hl₂
  obtain ⟨u, huV, hu⟩ := U.2.exists_basicOpen_le ⟨S.i₁ ξ, hξV⟩ hξU
  have hWU : ((X.affineBasicOpen u : X.affineOpens) : X.Opens) ≤ U := X.affineBasicOpen_le u
  have hWV : ((X.affineBasicOpen u : X.affineOpens) : X.Opens) ≤ V := huV
  obtain ⟨θ, hθ⟩ := exists_eq_spec_map_comp (X.affineBasicOpen u) S.i₁ (by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum S.K) y ξ]
    exact hu)
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map ψ₁ ≫ affineOpenMap U =
      Spec.map θ ≫ affineOpenMap (X.affineBasicOpen u) := by
    rw [← hψ₁, ← hθ, hl₁]
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map ψ₂ ≫ affineOpenMap V =
      Spec.map θ ≫ affineOpenMap (X.affineBasicOpen u) := by
    rw [← hψ₂, ← hθ, hl₂]
  -- the `K`-algebra structure of `R`
  have hK : ∀ c : K, ψ₂.hom (algebraMap K (CoordinateRing (structureMap f V)) c) =
      ψ₁.hom (algebraMap K (CoordinateRing (structureMap f U)) c) := by
    have e : Spec.map ψ₁ ≫ Spec.algebraMap K (CoordinateRing (structureMap f U)) =
        Spec.map ψ₂ ≫ Spec.algebraMap K (CoordinateRing (structureMap f V)) := by
      rw [← affineOpenMap_comp f U, ← affineOpenMap_comp f V, ← Category.assoc,
        ← Category.assoc, ← hψ₁, ← hψ₂, hl₁', hl₂']
    have e' : Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing (structureMap f U))) ≫
        ψ₁) = Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing (structureMap f V))) ≫
        ψ₂) :=
      (Spec.map_comp _ _).trans (e.trans (Spec.map_comp _ _).symm)
    intro c
    exact (ConcreteCategory.congr_hom (Spec.map_injective e') c).symm
  let : Algebra K S.R :=
    (ψ₁.hom.comp (algebraMap K (CoordinateRing (structureMap f U)))).toAlgebra
  let ψ₁' : CoordinateRing (structureMap f U) →ₐ[K] S.R :=
    { ψ₁.hom with commutes' := fun _ => rfl }
  let ψ₂' : CoordinateRing (structureMap f V) →ₐ[K] S.R :=
    { ψ₂.hom with commutes' := fun c => hK c }
  -- the finitely generated subalgebra `D`
  let D : Subalgebra K S.R := ψ₁'.range ⊔ ψ₂'.range
  have hDfg : D.FG := by
    refine Subalgebra.FG.sup ?_ ?_
    · rw [← Algebra.map_top]
      exact Subalgebra.FG.map _ Algebra.FiniteType.out
    · rw [← Algebra.map_top]
      exact Subalgebra.FG.map _ Algebra.FiniteType.out
  have : Algebra.FiniteType K D := (Subalgebra.fg_iff_finiteType D).mp hDfg
  let φ₁ : CoordinateRing (structureMap f U) →ₐ[K] D :=
    ψ₁'.codRestrict D (fun x =>
      (le_sup_left : ψ₁'.range ≤ D) (AlgHom.mem_range_self ψ₁' x))
  let φ₂ : CoordinateRing (structureMap f V) →ₐ[K] D :=
    ψ₂'.codRestrict D (fun x =>
      (le_sup_right : ψ₂'.range ≤ D) (AlgHom.mem_range_self ψ₂' x))
  let j : D →+* S.K := (algebraMap S.R S.K).comp (D.val : D →+* S.R)
  have hj : Function.Injective j :=
    (IsFractionRing.injective S.R S.K).comp Subtype.val_injective
  have h₁ : ∀ a, θ.hom (restriction f (X.affineBasicOpen_le u) a) = j (φ₁ a) := fun a =>
    restriction_eq_of_spec_map f (X.affineBasicOpen_le u) ψ₁ θ _ e₁ a
  have h₂ : ∀ b, θ.hom (restriction f hWV b) = j (φ₂ b) := fun b =>
    restriction_eq_of_spec_map f hWV ψ₂ θ _ e₂ b
  let I : Ideal D := (IsLocalRing.maximalIdeal S.R).comap D.val
  have hI : I ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal S.R).ne_top
  have hunit : IsUnit (restriction f (X.affineBasicOpen_le u)
      (CenterRange.basicOpenGenerator f U u)) := by
    let := (restriction f (X.affineBasicOpen_le u)).toRingHom.toAlgebra
    have := CenterRange.isLocalization_restriction_basicOpen f U u
    exact IsLocalization.Away.algebraMap_isUnit (CenterRange.basicOpenGenerator f U u)
  have hg : φ₁ (CenterRange.basicOpenGenerator f U u) ≠ 0 := by
    intro h0
    have h1 := h₁ (CenterRange.basicOpenGenerator f U u)
    rw [h0, map_zero] at h1
    exact (hunit.map θ.hom).ne_zero h1
  obtain ⟨a, b, hab, -, hb⟩ := exists_ι_eq K f U V u hWV φ₁ φ₂ θ.hom j hj h₁ h₂ I hI hg
  -- the closed point of `Spec R` under `l₂` specializes into `U`
  have hzU : center K f (ι K f V b) ∈ (U : X.Opens) := hab ▸ center_ι_mem K f U a
  have hspec : l₂ cp ⤳ center K f (ι K f V b) := by
    rw [center_ι, localCenter_apply, hψ₂, Scheme.Hom.comp_apply]
    apply Specializes.map _ (affineOpenMap V).continuous
    refine (PrimeSpectrum.le_iff_specializes (R := CoordinateRing (structureMap f V)) _ _).mp ?_
    intro y hy
    change y ∈ (AffineAnalytification.center K (chartPresentation K f V) b).asIdeal
    rw [AffineAnalytification.center_asIdeal, AffineAnalytification.mem_kernel]
    exact hb y hy
  have hx₂U : l₂ cp ∈ (U : X.Opens) := hspec.mem_open (U : X.Opens).2 hzU
  obtain ⟨ψ₃, hψ₃⟩ := exists_eq_spec_map_comp U l₂ (hrange l₂ U hx₂U)
  have e : Spec.map (ψ₁ ≫ CommRingCat.ofHom (algebraMap S.R S.K)) ≫ affineOpenMap U =
      Spec.map (ψ₃ ≫ CommRingCat.ofHom (algebraMap S.R S.K)) ≫ affineOpenMap U := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, ← hψ₁, ← hψ₃, hl₁, hl₂]
  rw [cancel_mono] at e
  have e' := Spec.map_injective e
  have hψ : ψ₁ = ψ₃ := by
    ext x
    exact IsFractionRing.injective S.R S.K (ConcreteCategory.congr_hom e' x)
  rw [hψ₁, hψ₃, hψ]

variable (K) in
/-- **Hausdorff implies separated.** If the analytification of a scheme locally of finite
type over `K` is Hausdorff, the scheme is separated over `K`. -/
theorem isSeparated_of_t2Space [T2Space (Space K f)] : IsSeparated f := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  exact IsSeparated.of_valuativeCriterion f (valuativeCriterion_uniqueness K f)

end Valuative

end Langlands.Analytic.SchemeAnalytification.SeparatedReverse
