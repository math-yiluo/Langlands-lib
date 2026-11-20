import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Langlands.Geometry.Analytic.TruncatedComparisonFlatness
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Jacobson.Ring

/-! # Artinian tests for affine open immersions -/

noncomputable section

universe u v

namespace Langlands.Analytic.ArtinianOpenImmersionTests

open CategoryTheory _root_.AlgebraicGeometry Langlands.AlgebraicGeometry

section Quotients

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- A finite-type algebra over a field has finite-dimensional quotients by
positive powers of its maximal ideals. -/
theorem finite_maximalPowerQuotient (m : Ideal A) [m.IsMaximal] {n : ℕ} (hn : n ≠ 0) :
    Module.Finite K (A ⧸ m ^ n) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  let hle : m ^ n ≤ m := Ideal.pow_le_self hn
  let π : (A ⧸ m ^ n) →ₐ[K] A ⧸ m := Ideal.Quotient.factorₐ K hle
  apply Module.finite_of_surjective_of_ker_le_nilradical π
    (Ideal.Quotient.factor_surjective hle) _ (IsNoetherian.noetherian _)
  intro b hb
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : b ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hb
  rw [mem_nilradical]
  exact ⟨n, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hb' n⟩

end Quotients

/-- A quotient by a positive power of a maximal ideal is local. -/
theorem isLocalRing_maximalPowerQuotient {A : Type v} [CommRing A]
    (m : Ideal A) [m.IsMaximal] {n : ℕ} (hn : n ≠ 0) : IsLocalRing (A ⧸ m ^ n) := by
  let q := Ideal.Quotient.mk (m ^ n)
  have hle : m ^ n ≤ m := Ideal.pow_le_self hn
  have hmax : (m.map q).IsMaximal := by
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
      ((DoubleQuot.quotQuotEquivQuotOfLE hle).isField (Field.toIsField _))
  refine IsLocalRing.of_unique_max_ideal ⟨m.map q, hmax, fun j hj => ?_⟩
  let : j.IsMaximal := hj
  rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective j]
  congr 1
  symm
  apply (inferInstance : m.IsMaximal).eq_of_le
    (Ideal.comap_isMaximal_of_surjective q Ideal.Quotient.mk_surjective).ne_top
  intro a ha
  have hpow : a ^ n ∈ j.comap q := by
    change q (a ^ n) ∈ j
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha n)]
    exact j.zero_mem
  exact (Ideal.comap_isPrime q j).mem_of_pow_mem _ hpow

section Affine

variable {K A B : Type u} [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] (g : A →ₐ[K] B)

/-- The algebra map of the affine base change along a quotient. -/
abbrev truncationMap (I : Ideal A) : (A ⧸ I) →ₐ[K] B ⧸ I.map g.toRingHom :=
  Ideal.quotientMapₐ (I.map g.toRingHom) g Ideal.le_comap_map

/-- A closed point has closed image under a map of finite-type affine
schemes over a field. -/
theorem isMaximal_comap (m : Ideal B) [m.IsMaximal] : (m.comap g.toRingHom).IsMaximal := by
  let : Algebra A B := g.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite A (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing A _
  have h := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (⊥ : Ideal (B ⧸ m))
  change (Ideal.comap (algebraMap A (B ⧸ m)) ⊥).IsMaximal at h
  rw [IsScalarTower.algebraMap_eq A B (B ⧸ m), ← Ideal.comap_comap] at h
  change ((RingHom.ker (Ideal.Quotient.mk m)).comap g.toRingHom).IsMaximal at h
  simpa only [Ideal.mk_ker] using h

omit [Algebra.FiniteType K A] in
set_option backward.isDefEq.respectTransparency false in
private theorem surjective_truncationMap [Mono (Spec.map (CommRingCat.ofHom g.toRingHom))]
    (I : Ideal A) [IsArtinianRing (A ⧸ I)] : Function.Surjective (truncationMap g I) := by
  let φ := CommRingCat.ofHom (truncationMap g I).toRingHom
  let t := Spec.map φ
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_map g.toRingHom I)).flip
  let : Mono t := h.mono_snd_of_mono inferInstance
  let : LocallyOfFiniteType t := by
    have hf : (truncationMap g I).toRingHom.FiniteType := by
      let : Algebra (A ⧸ I) (B ⧸ I.map g.toRingHom) := (truncationMap g I).toRingHom.toAlgebra
      let : IsScalarTower K (A ⧸ I) (B ⧸ I.map g.toRingHom) :=
        IsScalarTower.of_algebraMap_eq fun a => ((truncationMap g I).commutes a).symm
      exact RingHom.finiteType_algebraMap.mpr (Algebra.FiniteType.of_restrictScalars_finiteType K _ _)
    exact HasRingHomProperty.Spec_iff.mpr hf
  let : LocallyQuasiFinite t := inferInstance
  let : QuasiCompact t := quasiCompact_of_compactSpace t
  let : IsFinite t := IsFinite.of_locallyQuasiFinite t
  let : Mono φ.op := (Functor.mono_map_iff_mono Scheme.Spec φ.op).mp (inferInstanceAs (Mono t))
  let : Epi φ := show Epi φ.op.unop by infer_instance
  exact (RingHom.surjective_iff_epi_and_finite (f := φ)).mpr
    ⟨inferInstance, (IsFinite.SpecMap_iff φ).mp (inferInstanceAs (IsFinite t))⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite-type map inducing a monomorphism of affine schemes is an open
immersion if the quotient comparison is injective at every positive-order
infinitesimal thickening of each closed point of its source. -/
theorem isOpenImmersion_of_injective_truncations
    [Mono (Spec.map (CommRingCat.ofHom g.toRingHom))]
    (hinj : ∀ (m : Ideal B) [m.IsMaximal] (n : ℕ), n ≠ 0 →
      Function.Injective (truncationMap g ((m.comap g.toRingHom) ^ n))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
  let : Algebra A B := g.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  let s := Spec.map (CommRingCat.ofHom g.toRingHom)
  let : Flat s := by
    apply Flat.SpecMap_iff.mpr
    apply RingHom.flat_algebraMap_iff.mpr
    apply TruncatedComparison.flat_of_forall_maximal
    intro m hm
    let : m.IsMaximal := hm
    let p := m.comap g.toRingHom
    let : p.IsMaximal := isMaximal_comap g m
    have hbij (n : ℕ) (hn : n ≠ 0) : Function.Bijective (truncationMap g (p ^ n)) := by
      let : Module.Finite K (A ⧸ p ^ n) := finite_maximalPowerQuotient (K := K) p hn
      let : IsArtinianRing (A ⧸ p ^ n) := IsArtinianRing.of_finite K _
      exact ⟨hinj m n hn, surjective_truncationMap g (p ^ n)⟩
    have hmap : p.map g.toRingHom = m := by
      have h₁ : Function.Bijective (truncationMap g p) :=
        (congrArg (fun I : Ideal A => Function.Bijective (truncationMap g I)) (pow_one p)).mp
          (hbij 1 one_ne_zero)
      let e := RingEquiv.ofBijective (truncationMap g p).toRingHom h₁
      let : Field (A ⧸ p) := Ideal.Quotient.field p
      have hm' := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
        (e.symm.isField (Field.toIsField _))
      exact hm'.eq_of_le hm.ne_top Ideal.map_comap_le
    apply TruncatedComparison.flat_localization (𝔫 := p) (𝔪 := m) (show p ≤ m.comap _ from le_rfl)
    intro n
    cases n with
    | zero =>
      have : Subsingleton (A ⧸ p ^ 0) := by simp
      have : Subsingleton (B ⧸ m ^ 0) := by simp
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    | succ n =>
      have h (J : Ideal B) (heq : (p ^ (n + 1)).map g.toRingHom = J)
          (hle : p ^ (n + 1) ≤ J.comap g.toRingHom) :
          Function.Bijective (Ideal.quotientMap J g.toRingHom hle) := by
        subst J
        exact hbij (n + 1) (Nat.succ_ne_zero n)
      exact h (m ^ (n + 1)) (by rw [Ideal.map_pow, hmap]) _
  let : LocallyOfFiniteType s := HasRingHomProperty.Spec_iff.mpr
    (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType A B))
  let : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  exact IsOpenImmersion.of_flat_of_mono s

end Affine

end Langlands.Analytic.ArtinianOpenImmersionTests
