import Langlands.CommutativeAlgebra.EtaleLocalSections

/-! # Preserving a rational point in an etale specialization -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.PointedEtaleLocalSections

open Algebra Langlands.CommutativeAlgebra.EtaleLocalSections

/-- An etale algebra over a polynomial algebra can be specialized etale-locally
on the base while preserving any supplied rational point of its fibre. -/
theorem exists_etale_factor_of_polynomial {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {n : ℕ} [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Etale (MvPolynomial (Fin n) R) S] (𝔭 : Ideal R) [𝔭.IsPrime]
    (φ : S →ₐ[R] 𝔭.ResidueField) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Etale R R' ∧
      ∃ (ψ : S →ₐ[R] R') (ρ : R' →ₐ[R] 𝔭.ResidueField), ρ.comp ψ = φ := by
  classical
  let P := MvPolynomial (Fin n) R
  let κ := 𝔭.ResidueField
  let c : Fin n → κ := fun i => φ (algebraMap P S (MvPolynomial.X i))
  obtain ⟨b, -, β, hβ, hc⟩ := exists_away_lift 𝔭 (Finset.univ.image c)
  have hc' : ∀ i, ∃ a : Localization.Away b, β a = c i := fun i =>
    hc _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  choose a ha using hc'
  let Rb := Localization.Away b
  let θ : P →ₐ[R] Rb := MvPolynomial.aeval a
  let : Algebra P Rb := θ.toRingHom.toAlgebra
  have : IsScalarTower R P Rb := .of_algebraMap_eq fun r => (θ.commutes r).symm
  let : Algebra P κ := (φ.toRingHom.comp (algebraMap P S)).toAlgebra
  have : IsScalarTower R P κ := .of_algebraMap_eq fun r => by
    change algebraMap R κ r = φ (algebraMap P S (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply R P S, φ.commutes]
  have hβθ : β.comp θ.toRingHom = φ.toRingHom.comp (algebraMap P S) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change β (θ (MvPolynomial.C r)) = φ (algebraMap P S (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, θ.commutes,
        ← IsScalarTower.algebraMap_apply R P S, φ.commutes]
      exact congrArg (fun h : R →+* κ => h r) hβ
    · intro i
      change β (θ (MvPolynomial.X i)) = c i
      dsimp only [θ]
      rw [MvPolynomial.aeval_X]
      exact ha i
  let βP : Rb →ₐ[P] κ := ⟨β, fun q => congrArg (fun h : P →+* κ => h q) hβθ⟩
  let φP : S →ₐ[P] κ := ⟨φ.toRingHom, fun _ => rfl⟩
  let R' := Rb ⊗[P] S
  let ψ : S →ₐ[R] R' := (Algebra.TensorProduct.includeRight (R := P) (A := Rb)).restrictScalars R
  let ρ : R' →ₐ[R] κ :=
    (Algebra.TensorProduct.lift βP φP (fun _ _ => Commute.all _ _)).restrictScalars R
  refine ⟨R', inferInstance, inferInstance, Etale.comp R Rb R', ψ, ρ, ?_⟩
  ext x
  change Algebra.TensorProduct.lift βP φP (fun _ _ => Commute.all _ _) (1 ⊗ₜ[P] x) = φ x
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- A rational point of a smooth algebra factors through an etale base algebra,
with an exactly preserved residue-field-valued point. -/
theorem exists_etale_factor_of_smooth {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Smooth R S] (𝔭 : Ideal R) [𝔭.IsPrime]
    (φ : S →ₐ[R] 𝔭.ResidueField) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Etale R R' ∧
      ∃ (ψ : S →ₐ[R] R') (ρ : R' →ₐ[R] 𝔭.ResidueField), ρ.comp ψ = φ := by
  let 𝔮 : Ideal S := RingHom.ker φ.toRingHom
  have : 𝔮.IsPrime := RingHom.ker_isPrime _
  obtain ⟨g, hg, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := 𝔮)
  let Sg := Localization.Away g
  have hgu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φgRing : Sg →+* 𝔭.ResidueField := IsLocalization.Away.lift g hgu
  have hφg : φgRing.comp (algebraMap S Sg) = φ.toRingHom := IsLocalization.lift_comp _
  let φg : Sg →ₐ[R] 𝔭.ResidueField :=
    ⟨φgRing, fun r => by
      rw [IsScalarTower.algebraMap_apply R S Sg]
      change (φgRing.comp (algebraMap S Sg)) (algebraMap R S r) = _
      rw [hφg]
      exact φ.commutes r⟩
  obtain ⟨R', _, _, hR', ψ, ρ, hfac⟩ :=
    exists_etale_factor_of_polynomial (n := n) 𝔭 φg
  refine ⟨R', inferInstance, inferInstance, hR',
    ψ.comp (IsScalarTower.toAlgHom R S Sg), ρ, ?_⟩
  ext x
  have h1 := congrArg (fun h : Sg →ₐ[R] 𝔭.ResidueField => h (algebraMap S Sg x)) hfac
  have h2 := congrArg (fun h : S →+* 𝔭.ResidueField => h x) hφg
  exact h1.trans h2

end Langlands.CommutativeAlgebra.PointedEtaleLocalSections
