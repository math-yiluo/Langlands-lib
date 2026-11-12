import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartOpenness
import Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartReduction
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.Localization.InvSubmonoid

/-! # Affine charts through finite-type field points with surjective residue maps -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open Langlands.AlgebraicGeometry.Deformation PicardGroupoid

/-- A finite-type ring map to a field that is surjective on stalks becomes surjective after
inverting one element not mapping to zero. -/
lemma exists_surjective_away {A K : Type u} [CommRing A] [Field K] (χ : A →+* K)
    (h1 : χ.SurjectiveOnStalks) (h2 : χ.FiniteType) :
    ∃ b : A, χ b ≠ 0 ∧ ∀ t : K, ∃ x : A, ∃ n : ℕ, χ x = t * χ b ^ n := by
  classical
  letI := χ.toAlgebra
  have hfr : ∀ s : K, ∃ x r : A, χ r ≠ 0 ∧ χ r * s = χ x := by
    intro s
    obtain ⟨x, r, c, hc, hr, e⟩ :=
      (RingHom.surjective_localRingHom_iff (f := χ) ⊥).mp (h1 ⊥ Ideal.isPrime_bot) s
    have hc0 : c ≠ 0 := fun h => hc (h ▸ Submodule.zero_mem _)
    refine ⟨x, r, fun h => hr (h ▸ Submodule.zero_mem _), ?_⟩
    apply mul_left_cancel₀ hc0
    rw [← mul_assoc, e]
  choose x r hr hxr using hfr
  obtain ⟨S, hS⟩ := h2.out
  let b : A := ∏ s ∈ S, r s
  have hb : χ b ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hr s
  refine ⟨b, hb, ?_⟩
  let T : Subalgebra A K :=
    { carrier := {t | ∃ y : A, ∃ n : ℕ, χ y = t * χ b ^ n}
      mul_mem' := by
        rintro t₁ t₂ ⟨y₁, n₁, h₁⟩ ⟨y₂, n₂, h₂⟩
        exact ⟨y₁ * y₂, n₁ + n₂, by rw [map_mul, h₁, h₂, pow_add]; ring⟩
      add_mem' := by
        rintro t₁ t₂ ⟨y₁, n₁, h₁⟩ ⟨y₂, n₂, h₂⟩
        exact ⟨y₁ * b ^ n₂ + y₂ * b ^ n₁, n₁ + n₂, by
          rw [map_add, map_mul, map_mul, map_pow, map_pow, h₁, h₂, pow_add]; ring⟩
      algebraMap_mem' := fun a => ⟨a, 0, by simp; rfl⟩ }
  have hST : (S : Set K) ⊆ T := by
    intro s hs
    refine ⟨x s * ∏ s' ∈ S.erase s, r s', 1, ?_⟩
    rw [pow_one, map_mul, ← hxr s, map_prod]
    change χ (r s) * s * ∏ s' ∈ S.erase s, χ (r s') = s * χ (∏ s' ∈ S, r s')
    rw [map_prod, ← Finset.mul_prod_erase S (fun s' => χ (r s')) hs]
    ring
  intro t
  have ht : t ∈ Algebra.adjoin A (S : Set K) := by rw [hS]; trivial
  exact Algebra.adjoin_le hST ht

section Chart

variable {R : Type u} [CommRing R]

/-- An affine open of a scheme over `Spec R`, as an affine chart `affineBase R Γ(W) ⟶ T`
(the `R`-algebra structure on `Γ(W)` is the one induced by the structure morphism). -/
lemma exists_affineOpen_chart (T : Over (Spec (CommRingCat.of R))) {W : T.left.Opens}
    (hW : IsAffineOpen W) :
    ∃ (_ : Algebra R Γ(T.left, W)) (ι : affineBase R Γ(T.left, W) ⟶ T), ι.left = hW.fromSpec := by
  let φ := Spec.preimage (hW.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, W) := φ.hom.toAlgebra
  refine ⟨this, Over.homMk hW.fromSpec ?_, rfl⟩
  change hW.fromSpec ≫ T.hom = Spec.map (CommRingCat.ofHom φ.hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- **Affine charts through a finite-type field point.** A field point `p` of a scheme `T`
locally of finite type over `R`, which is surjective on stalks and locally of finite type,
factors through an open affine chart `affineBase R A ⟶ T` with `A` of finite type over `R`,
via a surjective `R`-algebra map `A → K`. -/
theorem exists_affineChart (T : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType T.hom]
    {K : Type u} [Field K] [Algebra R K] (p : ArtinianTest.residueBase R K ⟶ T)
    [SurjectiveOnStalks p.left] [LocallyOfFiniteType p.left] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (ι : affineBase R A ⟶ T)
      (χ : A →ₐ[R] K), IsOpenImmersion ι.left ∧ Algebra.FiniteType R A ∧
        Function.Surjective χ ∧ affineBaseMap χ ≫ ι = p := by
  let pt : (ArtinianTest.residueBase R K).left := (default : PrimeSpectrum K)
  obtain ⟨_, ⟨W, hW', rfl⟩, hxW, -⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left pt)) isOpen_univ
  have hW : IsAffineOpen W := hW'
  obtain ⟨_, ι₁, hι₁⟩ := exists_affineOpen_chart T hW
  have : IsOpenImmersion ι₁.left := by rw [hι₁]; infer_instance
  have hrange : Set.range p.left ⊆ Set.range ι₁.left := by
    rintro _ ⟨z, rfl⟩
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hz]
    obtain ⟨y, hy⟩ : p.left pt ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hxW
    refine ⟨y, ?_⟩
    have := congrArg (fun φ : (affineBase R Γ(T.left, W)).left ⟶ T.left => φ y) hι₁
    exact this.trans hy
  obtain ⟨χ₁, hχ₁⟩ := exists_affineBaseMap_eq (R := R) (A := Γ(T.left, W)) (B := K)
    (pointLift ι₁ p hrange)
  have hcomp : affineBaseMap χ₁ ≫ ι₁ = p := by
    rw [hχ₁]
    exact pointLift_comp ι₁ p hrange
  have hleft : (affineBaseMap χ₁).left ≫ ι₁.left = p.left := by
    rw [← Over.comp_left, hcomp]
  -- the residue map is surjective on stalks and of finite type
  have h1 : χ₁.toRingHom.SurjectiveOnStalks := by
    haveI : SurjectiveOnStalks ((affineBaseMap χ₁).left ≫ ι₁.left) := by
      rw [hleft]; infer_instance
    haveI := SurjectiveOnStalks.of_comp (affineBaseMap χ₁).left ι₁.left
    exact (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)
      (φ := CommRingCat.ofHom χ₁.toRingHom)).mp this
  have h2 : χ₁.toRingHom.FiniteType := by
    haveI : LocallyOfFiniteType ((affineBaseMap χ₁).left ≫ ι₁.left) := by
      rw [hleft]; infer_instance
    haveI := locallyOfFiniteType_of_comp (affineBaseMap χ₁).left ι₁.left
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom χ₁.toRingHom)).mp this
  have hft₁ : Algebra.FiniteType R Γ(T.left, W) := by
    haveI : LocallyOfFiniteType (ι₁.left ≫ T.hom) := inferInstance
    rw [Over.w ι₁] at this
    rw [← RingHom.finiteType_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap R Γ(T.left, W)))).mp this
  obtain ⟨b, hb, hbs⟩ := exists_surjective_away χ₁.toRingHom h1 h2
  -- the localized chart
  let A := Localization.Away b
  have hu : ∀ y : Submonoid.powers b, IsUnit (χ₁ y) := by
    rintro ⟨_, n, rfl⟩
    have hb' : χ₁ b ≠ 0 := hb
    show IsUnit (χ₁ (b ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr hb').pow n
  let χ : A →ₐ[R] K := IsLocalization.liftAlgHom (M := Submonoid.powers b) (S := A) hu
  have hχ : χ.comp (IsScalarTower.toAlgHom R Γ(T.left, W) A) = χ₁ := by
    ext y
    exact IsLocalization.lift_eq (M := Submonoid.powers b) (S := A) hu y
  refine ⟨A, inferInstance, inferInstance,
    affineBaseMap (IsScalarTower.toAlgHom R Γ(T.left, W) A) ≫ ι₁, χ, ?_, ?_, ?_, ?_⟩
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(T.left, W) A)) ≫ ι₁.left)
    infer_instance
  · exact Algebra.FiniteType.trans hft₁ inferInstance
  · intro t
    obtain ⟨y, n, hy⟩ := hbs t
    refine ⟨IsLocalization.mk' A y (⟨b ^ n, n, rfl⟩ : Submonoid.powers b), ?_⟩
    change IsLocalization.lift hu (IsLocalization.mk' A y _) = t
    rw [IsLocalization.lift_mk'_spec]
    change χ₁ y = χ₁ (b ^ n) * t
    rw [map_pow, mul_comm]
    exact hy
  · rw [← Category.assoc, ← affineBaseMap_comp, hχ, hcomp]

end Chart

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
