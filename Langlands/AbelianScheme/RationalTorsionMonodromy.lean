import Langlands.AbelianScheme.RationalTorsionExtension
import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.Tate.PrimeAdicEvaluationKernel
import Langlands.AbelianScheme.Tate.RestrictedProductProof
import Langlands.LinearAlgebra.CongruentQuasiUnipotent

/-! # Rational torsion and geometric monodromy

Let `B` be an abelian variety over a field `K` and `n` a positive integer invertible in `K`.
If all `n`-torsion points of `B` with values in an algebraic closure of `K` are `K`-rational,
then the same holds with values in any algebraically closed field over `K`. After base change
to a field `L` over `K`, the finite étale fundamental group of `Spec L` at a geometric point
then acts trivially on the `k`-torsion points for every positive divisor `k` of `n`.
Consequently, for a prime `ℓ` whose powers are all invertible on `Spec L` and a natural number
`a` with `ℓ ^ a ∣ n`, every element of the fundamental group acts on the integral `ℓ`-adic Tate
module by an endomorphism congruent to the identity modulo `ℓ ^ a`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.RationalTorsionMonodromy

open Langlands.AbelianScheme.RationalTorsionExtension
open Langlands.AlgebraicGeometry.FiniteEtale

section Points

/-- The spectrum of a field extension is an epimorphism of schemes. -/
theorem epi_specAlgebraMap (F A : Type u) [Field F] [Field A] [Algebra F A] :
    Epi (Spec.algebraMap F A) := by
  have hff : (algebraMap F A).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap F A))).mpr hff
  have : Flat (Spec.algebraMap F A) := h.1
  have : Surjective (Spec.algebraMap F A) := h.2
  exact Flat.epi_of_flat_of_surjective _

/-- A morphism of spectra of fields is the spectrum map of the algebra structure it
defines. -/
theorem specAlgebraMap_preimage {F A : Type u} [Field F] [Field A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of F)) :
    letI := (Spec.preimage s).hom.toAlgebra
    Spec.algebraMap F A = s := by
  let := (Spec.preimage s).hom.toAlgebra
  change Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- Every morphism from the spectrum of a field to the spectrum of a field is an
epimorphism. -/
theorem epi_of_spec_field {F A : Type u} [Field F] [Field A]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of F)) : Epi s := by
  let := (Spec.preimage s).hom.toAlgebra
  have h := epi_specAlgebraMap F A
  rwa [specAlgebraMap_preimage s] at h

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- A point of a finite `K`-scheme with values in an algebraically closed field `Ω` over
`K` factors through a point with values in `AlgebraicClosure K`, for a `K`-embedding of
`AlgebraicClosure K` into `Ω`. -/
theorem exists_algebraicClosure_pointFactorization [IsFinite f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) (hx : x ≫ f = Spec.algebraMap K Ω) :
    ∃ (emb : AlgebraicClosure K →ₐ[K] Ω) (y : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X),
      y ≫ f = Spec.algebraMap K (AlgebraicClosure K) ∧
        Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ y = x := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := coordinateAlgebra f
  have : Module.Finite K Γ(X, ⊤) :=
    RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  set Kbar := AlgebraicClosure K
  let emb : Kbar →ₐ[K] Ω := IsAlgClosed.lift
  let : Algebra Kbar Ω := emb.toRingHom.toAlgebra
  have : IsScalarTower K Kbar Ω :=
    IsScalarTower.of_algebraMap_eq fun r => (emb.commutes r).symm
  obtain ⟨ψ, hψ⟩ := exists_algHom_factor_of_splits K Γ(X, ⊤) Kbar Ω
    (IsAlgClosed.splits _) (pointAlgHom f Ω x hx)
  let ψ' : Γ(X, ⊤) ⟶ CommRingCat.of Kbar := CommRingCat.ofHom ψ.toRingHom
  refine ⟨emb, Spec.map ψ' ≫ X.isoSpec.inv, ?_, ?_⟩
  · apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Kbar)).hom).1
    rw [Scheme.Hom.comp_appTop, Category.assoc, specMap_isoSpec_inv_appTop, Spec.algebraMap,
      Scheme.ΓSpecIso_naturality]
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
    rw [Iso.inv_hom_id_assoc]
    ext r
    exact ψ.commutes r
  · change Spec.algebraMap Kbar Ω ≫ _ = x
    apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1
    rw [Scheme.Hom.comp_appTop, Category.assoc, Spec.algebraMap, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, specMap_isoSpec_inv_appTop]
    ext a
    exact congrArg (fun g : Γ(X, ⊤) →ₐ[K] Ω => g a) hψ

end Points

section Rational

variable {K : Type u} [Field K] (B : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ)

/-- For a positive integer `n` invertible in `K`, rationality of the geometric `n`-torsion
over `AlgebraicClosure K` gives rationality of the `n`-torsion points with values in any
algebraically closed field over `K`. -/
theorem exists_section_of_hasRationalGeometricTorsion
    (hB : HasRationalGeometricTorsion B n) (hn : 0 < n) (hu : IsUnit (n : K))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K))
    (x : Over.mk t ⟶ B.X) (hx : x ^ (n : ℤ) = 1) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ B.X, Over.homMk t ≫ y = x := by
  have hu' : IsUnit ((n : ℕ) : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨hfin, -⟩ := torsionFiniteEtale (Spec (CommRingCat.of K)) B n hn hu'
  obtain ⟨z, hz⟩ :=
    ((GroupScheme.existsUnique_torsion_lift_iff B.toGrp (n : ℤ) _ x).mpr hx).exists
  let : Algebra K Ω := (Spec.preimage t).hom.toAlgebra
  have ht : Spec.algebraMap K Ω = t := specAlgebraMap_preimage t
  have hzK : z.left ≫ (GroupScheme.torsion B.toGrp (n : ℤ)).X.hom = Spec.algebraMap K Ω := by
    rw [Over.w z, ht]
    rfl
  obtain ⟨emb, y, hyK, hy⟩ := exists_algebraicClosure_pointFactorization
    (GroupScheme.torsion B.toGrp (n : ℤ)).X.hom Ω z.left hzK
  let yo : Over.mk (Spec.algebraMap K (AlgebraicClosure K)) ⟶
      (GroupScheme.torsion B.toGrp (n : ℤ)).X := Over.homMk y hyK
  have hmem : yo ≫ (GroupScheme.torsionι B.toGrp (n : ℤ)).hom.hom ∈
      GroupScheme.torsionPoints B.toGrp (n : ℤ)
        (Over.mk (Spec.algebraMap K (AlgebraicClosure K))) :=
    (GroupScheme.torsionPointsEquiv B.toGrp (n : ℤ) _ yo).property
  obtain ⟨yK, hyK'⟩ := hB _ hmem
  refine ⟨yK, ?_⟩
  have h1 : Spec.algebraMap K (AlgebraicClosure K) ≫ yK.left =
      y ≫ (GroupScheme.torsionι B.toGrp (n : ℤ)).hom.hom.left :=
    congrArg CommaMorphism.left hyK'
  have h2 : Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ Spec.algebraMap K (AlgebraicClosure K) =
      t := by
    rw [← ht, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext r
    exact emb.commutes r
  apply Over.OverMorphism.ext
  change t ≫ yK.left = x.left
  rw [← hz, Over.comp_left, ← hy, Category.assoc, ← h1, ← Category.assoc, h2]

/-- For a positive integer `n` invertible in `K` with `HasRationalGeometricTorsion B n`:
after base change to a field `L` over `K`, every `n`-torsion point of `B` with values in an
algebraically closed field over `L` is the restriction of an `L`-point. -/
theorem exists_section_baseChange_of_hasRationalGeometricTorsion
    (hB : HasRationalGeometricTorsion B n) (hn : 0 < n) (hu : IsUnit (n : K))
    (L : Type u) [Field L] [Algebra K L] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L))
    (x : Over.mk s ⟶ ((baseChange (Spec.algebraMap K L)).obj B).X)
    (hx : x ^ (n : ℤ) = 1) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
        ((baseChange (Spec.algebraMap K L)).obj B).X, Over.homMk s ≫ y = x := by
  have hx' : (GroupScheme.baseChangePointsEquiv (Spec.algebraMap K L) B.toGrp (Over.mk s) x) ^
      (n : ℤ) = 1 := by
    rw [← map_zpow]
    change (GroupScheme.baseChangePointsEquiv (Spec.algebraMap K L) B.toGrp (Over.mk s))
      (x ^ (n : ℤ)) = 1
    rw [hx, map_one]
  obtain ⟨yK, hyK⟩ := exists_section_of_hasRationalGeometricTorsion B n hB hn hu Ω
    (s ≫ Spec.algebraMap K L)
    (GroupScheme.baseChangePointsEquiv (Spec.algebraMap K L) B.toGrp (Over.mk s) x) hx'
  let c : (Over.map (Spec.algebraMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk (Spec.algebraMap K L) (by simp)
  refine ⟨(GroupScheme.baseChangePointsEquiv (Spec.algebraMap K L) B.toGrp
    (Over.mk (𝟙 (Spec (CommRingCat.of L))))).symm (c ≫ yK), ?_⟩
  apply (GroupScheme.baseChangePointsEquiv (Spec.algebraMap K L) B.toGrp (Over.mk s)).injective
  rw [GroupScheme.baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply, ← hyK,
    ← Category.assoc]
  congr 1

end Rational

section Monodromy

variable {L : Type u} [Field L] {Ω : Type u} [Field Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L))
  (hfin : ∀ Y : Cover (Spec (CommRingCat.of L)), Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme (Spec (CommRingCat.of L)))
  (n : ℕ)

/-- Every `n`-torsion point of `A` with values in `Ω` over `s` is the restriction of a
point of `A` over `L`. -/
def TorsionPointsRational : Prop :=
  ∀ x : Over.mk s ⟶ A.X, x ^ (n : ℤ) = 1 →
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ A.X, Over.homMk s ≫ y = x

/-- The geometric monodromy fixes every `k`-torsion point of `A`, for a positive divisor `k`
of `n` invertible on `Spec L`, when every `n`-torsion point is rational. -/
theorem levelMonodromy_eq_self (hA : TorsionPointsRational s A n) (k : ℕ) (hk : 0 < k)
    (hkn : k ∣ n) (huk : IsUnit (k : Γ(Spec (CommRingCat.of L), ⊤)))
    (g : FundamentalGroup s hfin) (x : Tate.Level A (Over.mk s) k) :
    Tate.levelMonodromy s hfin htor A k hk huk g x = x := by
  obtain ⟨p, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp (Over.mk s) k).surjective x
  have hx0 : (p.toMul ≫ (GroupScheme.torsionι A.toGrp (k : ℤ)).hom.hom) ^ (k : ℤ) = 1 :=
    (GroupScheme.mem_torsionPoints A.toGrp (k : ℤ) _ _).mp
      (GroupScheme.torsionPointsEquiv A.toGrp (k : ℤ) _ p.toMul).property
  have hx0n : (p.toMul ≫ (GroupScheme.torsionι A.toGrp (k : ℤ)).hom.hom) ^ (n : ℤ) = 1 := by
    obtain ⟨c, rfl⟩ := hkn
    rw [Nat.cast_mul, zpow_mul, hx0, one_zpow]
  obtain ⟨y, hy⟩ := hA _ hx0n
  let a : Over.mk s ⟶ Over.mk (𝟙 (Spec (CommRingCat.of L))) := Over.homMk s (by simp)
  have hepi : Epi a := by
    have : Epi a.left := epi_of_spec_field s
    exact Over.epi_of_epi_left _
  have hyk : y ^ (k : ℤ) = 1 := by
    apply (cancel_epi a).mp
    rw [GrpObj.comp_zpow]
    change (Over.homMk s ≫ y) ^ (k : ℤ) = a ≫ 1
    rw [hy, hx0, MonObj.comp_one]
  obtain ⟨y', hy'⟩ :=
    ((GroupScheme.existsUnique_torsion_lift_iff A.toGrp (k : ℤ) _ y).mpr hyk).exists
  have hp : p.toMul = a ≫ y' := by
    apply (cancel_mono (GroupScheme.torsionι A.toGrp (k : ℤ)).hom.hom).mp
    rw [Category.assoc, hy', hy]
  have := Tate.torsionKernel_isFinite htor A k hk huk
  have := Tate.torsionKernel_etale htor A k hk huk
  have hfinY : IsFinite (Over.mk (𝟙 (Spec (CommRingCat.of L)))).hom :=
    inferInstanceAs (IsFinite (𝟙 (Spec (CommRingCat.of L))))
  have hetY : Etale (Over.mk (𝟙 (Spec (CommRingCat.of L)))).hom :=
    inferInstanceAs (Etale (𝟙 (Spec (CommRingCat.of L))))
  have hact : act s hfin (GroupScheme.kernel (GroupScheme.multiplication A.toGrp k)).X g
      p.toMul = p.toMul := by
    rw [hp, act_naturality]
    congr 1
    apply Over.OverMorphism.ext
    have h1 := Over.w (act s hfin (Over.mk (𝟙 (Spec (CommRingCat.of L)))) g a)
    simp only [Over.mk_hom] at h1
    exact h1
  change GroupScheme.Tate.finiteLevelMonodromy A.toGrp s hfin k g
    (GroupScheme.Tate.kernelLevelEquiv A.toGrp (Over.mk s) k p) = _
  rw [GroupScheme.Tate.finiteLevelMonodromy_kernel, hact]
  rfl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Every element of the fundamental group acts on the integral `ℓ`-adic Tate module of `A`
by an endomorphism congruent to the identity modulo `ℓ ^ a`, when the powers of the prime `ℓ`
are invertible on `Spec L`, `ℓ ^ a` divides `n` and every `n`-torsion point is rational. -/
theorem monodromyMap_sub_one_valuesDivisible (hA : TorsionPointsRational s A n)
    (hℓ : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (CommRingCat.of L), ⊤)))
    (a : ℕ) (ha : ℓ ^ a ∣ n) (g : FundamentalGroup s hfin) :
    LinearAlgebra.CongruentQuasiUnipotent.ValuesDivisible (ℓ ^ a)
      (Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hℓ g - 1) := by
  intro x
  have h0 : Tate.PrimeAdic.evaluation A (Over.mk s) ℓ a
      ((Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hℓ g - 1) x) = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub,
      Tate.PrimeAdic.evaluation_monodromyMap,
      levelMonodromy_eq_self s hfin htor A n hA (ℓ ^ a) _ ha, sub_self]
  obtain ⟨y, hy⟩ :=
    GroupScheme.Tate.PrimeAdic.exists_smul_eq_of_evaluation_eq_zero A.toGrp (Over.mk s) ℓ _ a h0
  exact ⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩

end Monodromy

/-- For a positive integer `n` invertible in `K`, rationality of the geometric `n`-torsion
of `B` gives rationality of the `n`-torsion points of its base change to any field `L` over
`K`, at every geometric point of `Spec L`. -/
theorem torsionPointsRational_baseChange {K : Type u} [Field K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ)
    (hB : HasRationalGeometricTorsion B n) (hn : 0 < n) (hu : IsUnit (n : K))
    (L : Type u) [Field L] [Algebra K L] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of L)) :
    TorsionPointsRational s ((baseChange (Spec.algebraMap K L)).obj B) n :=
  fun x hx => exists_section_baseChange_of_hasRationalGeometricTorsion B n hB hn hu L Ω s x hx

section TateModule

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The integral `ℓ`-adic Tate module has no `ℓ`-torsion. -/
theorem integral_eq_zero_of_nsmul_eq_zero (x : Tate.PrimeAdic.Integral A T ℓ)
    (h : ℓ • x = 0) : x = 0 :=
  GroupScheme.Tate.PrimeAdic.eq_zero_of_prime_smul_eq_zero A.toGrp T ℓ x
    (by rwa [Nat.cast_smul_eq_nsmul])

/-- No nonzero element of the integral `ℓ`-adic Tate module is divisible by every power of
`ℓ`. -/
theorem integral_eq_zero_of_forall_dvd (x : Tate.PrimeAdic.Integral A T ℓ)
    (h : ∀ j : ℕ, ∃ y : Tate.PrimeAdic.Integral A T ℓ, x = ℓ ^ j • y) : x = 0 := by
  apply Subtype.ext
  funext j
  obtain ⟨y, rfl⟩ := h j
  change Tate.PrimeAdic.evaluation A T ℓ j (ℓ ^ j • y) = 0
  rw [map_nsmul]
  exact GroupScheme.Tate.level_nsmul_eq_zero A.toGrp T (ℓ ^ j) _

variable {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
  (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(S, ⊤)))

/-- The integral monodromy of a power is the power of the integral monodromy. -/
theorem monodromyMap_pow (g : FundamentalGroup s hfin) (m : ℕ) :
    Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hu (g ^ m) =
      Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hu g ^ m := by
  induction m with
  | zero =>
    ext x
    simp [Tate.PrimeAdic.monodromyMap_one]
  | succ m ih =>
    ext x
    rw [pow_succ, Tate.PrimeAdic.monodromyMap_mul, ih, pow_succ, Module.End.mul_apply]

/-- The rational monodromy is the scalar extension of the integral monodromy. -/
theorem rationalMonodromyRepresentation_toLinearMap (g : FundamentalGroup s hfin) :
    (Tate.PrimeAdic.rationalMonodromyRepresentation s hfin htor A ℓ hu g).toLinearMap =
      (Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hu g).baseChange ℚ_[ℓ] := rfl

/-- An endomorphism of the integral `ℓ`-adic Tate module is nilpotent exactly when its
scalar extension to the rational Tate module is. -/
theorem isNilpotent_baseChange_iff (f : Module.End ℤ_[ℓ] (Tate.PrimeAdic.Integral A T ℓ)) :
    IsNilpotent (f.baseChange ℚ_[ℓ]) ↔ IsNilpotent f := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [← LinearMap.baseChange_pow] at hN
    ext x
    apply GroupScheme.Tate.PrimeAdic.toRational_injective A.toGrp T ℓ
    have hx := LinearMap.congr_fun hN ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x)
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply] at hx
    rw [GroupScheme.Tate.PrimeAdic.toRational_apply, hx, LinearMap.zero_apply, map_zero]
  · rintro ⟨N, hN⟩
    exact ⟨N, by rw [← LinearMap.baseChange_pow, hN, LinearMap.baseChange_zero]⟩

/-- An element acts unipotently on the rational `ℓ`-adic Tate module exactly when it acts
unipotently on the integral one. -/
theorem isNilpotent_rationalMonodromy_sub_one_iff (g : FundamentalGroup s hfin) :
    IsNilpotent
        ((Tate.PrimeAdic.rationalMonodromyRepresentation s hfin htor A ℓ hu g).toLinearMap - 1) ↔
      IsNilpotent (Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hu g - 1) := by
  rw [rationalMonodromyRepresentation_toLinearMap, ← LinearMap.baseChange_one,
    ← LinearMap.baseChange_sub, isNilpotent_baseChange_iff]

/-- The `m`-th power of an element acts unipotently on the rational `ℓ`-adic Tate module
exactly when the `m`-th power of its integral monodromy is unipotent. -/
theorem isNilpotent_rationalMonodromy_pow_sub_one_iff (g : FundamentalGroup s hfin) (m : ℕ) :
    IsNilpotent
        ((Tate.PrimeAdic.rationalMonodromyRepresentation s hfin htor A ℓ hu (g ^ m)).toLinearMap -
          1) ↔
      IsNilpotent (Tate.PrimeAdic.monodromyMap s hfin htor A ℓ hu g ^ m - 1) := by
  rw [isNilpotent_rationalMonodromy_sub_one_iff, monodromyMap_pow]

end TateModule

end Langlands.AbelianScheme.RationalTorsionMonodromy
