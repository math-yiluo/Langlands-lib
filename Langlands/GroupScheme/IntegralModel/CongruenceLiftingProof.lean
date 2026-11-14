import Langlands.GroupScheme.IntegralModel.CongruenceLifting
import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Henselian lifting at every positive congruence level -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel

namespace CongruenceLifting

variable {R A S : Type u} [CommRing R] [HenselianLocalRing R]
  [CommRing A] [IsLocalRing A] [Algebra R A] [CommRing S] [Algebra R S]

/-- Étale points over a local quotient with nilpotent maximal ideal lift
through the Henselian base. -/
theorem exists_lift_of_etale [Algebra.Etale R S]
    (hA : Function.Surjective (algebraMap R A))
    (hm : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : S →ₐ[R] A) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R A).comp σ = φ := by
  let K := IsLocalRing.ResidueField A
  let : Algebra R K :=
    ((IsLocalRing.residue A).comp (algebraMap R A)).toAlgebra
  let π : A →ₐ[R] K := ⟨IsLocalRing.residue A, fun _ => rfl⟩
  have hK : Function.Surjective (algebraMap R K) :=
    IsLocalRing.residue_surjective.comp hA
  obtain ⟨σ, hσ⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_etale hK (π.comp φ)
  refine ⟨σ, Algebra.FormallyUnramified.lift_unique' π ?_ _ _ ?_⟩
  · change IsNilpotent (RingHom.ker (IsLocalRing.residue A))
    rwa [IsLocalRing.ker_residue]
  · ext x
    exact AlgHom.congr_fun hσ x

/-- Lift polynomial coordinates and specialize an étale polynomial algebra. -/
theorem exists_lift_of_polynomial {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Algebra.Etale (MvPolynomial (Fin n) R) S]
    (hA : Function.Surjective (algebraMap R A))
    (hm : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : S →ₐ[R] A) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R A).comp σ = φ := by
  classical
  let P := MvPolynomial (Fin n) R
  let c : Fin n → A := fun i => φ (algebraMap P S (MvPolynomial.X i))
  choose a ha using fun i => hA (c i)
  let θ : P →ₐ[R] R := MvPolynomial.aeval a
  let : Algebra P R := θ.toRingHom.toAlgebra
  have : IsScalarTower R P R := .of_algebraMap_eq fun r => (θ.commutes r).symm
  let : Algebra P A := (φ.toRingHom.comp (algebraMap P S)).toAlgebra
  have : IsScalarTower R P A := .of_algebraMap_eq fun r => by
    change algebraMap R A r = φ (algebraMap P S (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply R P S, φ.commutes]
  have hθ : (algebraMap R A).comp θ.toRingHom =
      φ.toRingHom.comp (algebraMap P S) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change algebraMap R A (θ (MvPolynomial.C r)) =
        φ (algebraMap P S (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, θ.commutes,
        ← IsScalarTower.algebraMap_apply R P S, φ.commutes]
      rfl
    · intro i
      change algebraMap R A (θ (MvPolynomial.X i)) = c i
      rw [MvPolynomial.aeval_X]
      exact ha i
  let πP : R →ₐ[P] A :=
    ⟨algebraMap R A, fun q => congrArg (fun h : P →+* A => h q) hθ⟩
  let φP : S →ₐ[P] A := ⟨φ.toRingHom, fun _ => rfl⟩
  let B := R ⊗[P] S
  let ψ : S →ₐ[R] B :=
    (Algebra.TensorProduct.includeRight (R := P) (A := R)).restrictScalars R
  let ρ : B →ₐ[R] A :=
    (Algebra.TensorProduct.lift πP φP (fun _ _ => Commute.all _ _)).restrictScalars R
  obtain ⟨τ, hτ⟩ := exists_lift_of_etale hA hm ρ
  refine ⟨τ.comp ψ, ?_⟩
  ext x
  have h := AlgHom.congr_fun hτ (ψ x)
  change algebraMap R A (τ (ψ x)) = ρ (ψ x) at h
  change algebraMap R A (τ (ψ x)) = _
  rw [h]
  change Algebra.TensorProduct.lift πP φP (fun _ _ => Commute.all _ _) (1 ⊗ₜ[P] x) = φ x
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- Smooth algebra points over a local quotient with nilpotent maximal ideal
lift through the Henselian base. -/
theorem exists_lift_of_smooth [Algebra.Smooth R S]
    (hA : Function.Surjective (algebraMap R A))
    (hm : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : S →ₐ[R] A) :
    ∃ σ : S →ₐ[R] R, (Algebra.ofId R A).comp σ = φ := by
  let 𝔮 : Ideal S := RingHom.ker ((IsLocalRing.residue A).comp φ.toRingHom)
  have : 𝔮.IsPrime := RingHom.ker_isPrime _
  obtain ⟨g, hg, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := 𝔮)
  let Sg := Localization.Away g
  have hgu : IsUnit (φ g) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hg
  let φgRing : Sg →+* A := IsLocalization.Away.lift g hgu
  have hφg : φgRing.comp (algebraMap S Sg) = φ.toRingHom := IsLocalization.lift_comp _
  let φg : Sg →ₐ[R] A :=
    ⟨φgRing, fun r => by
      rw [IsScalarTower.algebraMap_apply R S Sg]
      change (φgRing.comp (algebraMap S Sg)) (algebraMap R S r) = _
      rw [hφg]
      exact φ.commutes r⟩
  obtain ⟨τ, hτ⟩ := exists_lift_of_polynomial (n := n) hA hm φg
  refine ⟨τ.comp (IsScalarTower.toAlgHom R S Sg), ?_⟩
  ext x
  have h1 := AlgHom.congr_fun hτ (algebraMap S Sg x)
  have h2 := RingHom.congr_fun hφg x
  exact h1.trans h2

/-- Scheme points over a local quotient with nilpotent maximal ideal lift
through a smooth morphism over the Henselian base. -/
theorem exists_section_of_smooth
    (hA : Function.Surjective (algebraMap R A))
    (hm : IsNilpotent (IsLocalRing.maximalIdeal A)) {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Smooth p] (b : Spec (CommRingCat.of A) ⟶ U)
    (hb : b ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ σ = b := by
  obtain ⟨V, hV, hyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := b (IsLocalRing.closedPoint A)) (U := ⊤) trivial
  have hrange : Set.range b ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map b.continuous).mem_open V.isOpen hyV
  let bV : Spec (CommRingCat.of A) ⟶ Spec Γ(U, V) := IsOpenImmersion.lift hV.fromSpec b hrange
  have hbV : bV ≫ hV.fromSpec = b := IsOpenImmersion.lift_fac _ _ _
  let g : CommRingCat.of R ⟶ Γ(U, V) := Spec.preimage (hV.fromSpec ≫ p)
  have hg : Spec.map g = hV.fromSpec ≫ p := Spec.map_preimage _
  let φ : Γ(U, V) ⟶ CommRingCat.of A := Spec.preimage bV
  have hφ : Spec.map φ = bV := Spec.map_preimage _
  let : Algebra R Γ(U, V) := g.hom.toAlgebra
  have : Algebra.Smooth R Γ(U, V) := by
    have h : Smooth (Spec.map g) := by
      rw [hg]
      infer_instance
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)
  have hgφ : g ≫ φ = CommRingCat.ofHom (algebraMap R A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hg, ← Category.assoc, hbV, hb]
  let φA : Γ(U, V) →ₐ[R] A :=
    { toRingHom := φ.hom
      commutes' := fun r =>
        congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of A => h.hom r) hgφ }
  obtain ⟨τ, hτ⟩ := exists_lift_of_smooth hA hm φA
  let τC : Γ(U, V) ⟶ CommRingCat.of R := CommRingCat.ofHom τ.toRingHom
  refine ⟨Spec.map τC ≫ hV.fromSpec, ?_, ?_⟩
  · have hτg : g ≫ τC = 𝟙 _ := by
      ext r
      exact τ.commutes r
    rw [Category.assoc, ← hg, ← Spec.map_comp, hτg, Spec.map_id]
  · have hτφ : τC ≫ CommRingCat.ofHom (algebraMap R A) = φ := by
      ext x
      exact AlgHom.congr_fun hτ x
    rw [← Category.assoc, ← Spec.map_comp, hτφ, hφ, hbV]

variable (R)

/-- A positive maximal-ideal-power quotient is nonzero. -/
theorem congruenceRing_nontrivial (n : ℕ+) : Nontrivial (congruenceRing R n) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.pow_le_self n.ne_zero)

/-- The maximal ideal of the congruence quotient is nilpotent, without a
Noetherian hypothesis. -/
theorem congruenceRing_maximalIdeal_isNilpotent (n : ℕ+)
    [IsLocalRing (congruenceRing R n)] :
    IsNilpotent (IsLocalRing.maximalIdeal (congruenceRing R n)) := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (congruenceQuotient R n)
    Ideal.Quotient.mk_surjective]
  refine ⟨(n : ℕ), ?_⟩
  rw [← Ideal.map_pow]
  exact Ideal.map_quotient_self ((IsLocalRing.maximalIdeal R) ^ (n : ℕ))

end CongruenceLifting

/-- KP Lemma 8.1.3: integral sections of a smooth group scheme over a
Henselian local ring surject onto every positive congruence level. -/
theorem henselianCongruenceLifting : HenselianCongruenceLiftingStatement.{u} := by
  intro R _ _ Y hY n y
  let : Smooth Y.X.hom := hY
  let : Nontrivial (congruenceRing R n) := CongruenceLifting.congruenceRing_nontrivial R n
  let : IsLocalRing (congruenceRing R n) :=
    IsLocalRing.of_surjective' (congruenceQuotient R n) Ideal.Quotient.mk_surjective
  have hm := CongruenceLifting.congruenceRing_maximalIdeal_isNilpotent R n
  have hy : y.left ≫ pullback.snd Y.X.hom (congruenceBaseMap R n) = 𝟙 _ := Over.w y
  let b : Spec (CommRingCat.of (congruenceRing R n)) ⟶ Y.X.left :=
    y.left ≫ pullback.fst Y.X.hom (congruenceBaseMap R n)
  have hb : b ≫ Y.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (congruenceRing R n))) := by
    simp only [b, Category.assoc, pullback.condition]
    rw [← Category.assoc, hy]
    exact Category.id_comp (congruenceBaseMap R n)
  obtain ⟨σ, hσ, hσb⟩ := CongruenceLifting.exists_section_of_smooth
    Ideal.Quotient.mk_surjective hm Y.X.hom b hb
  refine ⟨Over.homMk σ (by simpa using hσ), ?_⟩
  apply Over.OverMorphism.ext
  rw [baseChangeSectionHom_left]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact hσb
  · rw [pullback.lift_snd]
    exact hy.symm

end Langlands.GroupScheme.IntegralModel
