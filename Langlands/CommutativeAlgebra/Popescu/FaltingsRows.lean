import Langlands.CommutativeAlgebra.Popescu.FaltingsTensor

/-! # The Jacobi–Zariski rows for `ℤ → A → κ(A)` in characteristic `p` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open MvPolynomial

open scoped TensorProduct

/-- In characteristic `p`, `H₁(L_{T/ℤ}) → H₁(L_{T/R})` is zero for a field `T` over `R`: it
factors through `H₁(L_{T/𝔽_p}) = 0`. -/
theorem map_int_eq_zero_of_charP (p : ℕ) [hp : Fact p.Prime] {R T : Type*} [CommRing R] [Field T]
    [Algebra R T] [CharP R p] [Algebra ℤ R] [Algebra ℤ T]
    [@IsScalarTower ℤ R T Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (y : Algebra.H1Cotangent ℤ T) : Algebra.H1Cotangent.map ℤ R T T y = 0 := by
  have : CharP T p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap R T), CharP.cast_eq_zero, map_zero])
  let _ := ZMod.algebra R p
  let _ := ZMod.algebra T p
  have : IsScalarTower (ZMod p) R T := .of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := T) (RingHom.ext_int _ _)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := R) (RingHom.ext_int _ _)
  have h0 : Subsingleton (Algebra.H1Cotangent (ZMod p) T) :=
    FieldH1.subsingleton_h1Cotangent_of_perfectField (ZMod p) T
  have hfac : Algebra.H1Cotangent.map ℤ R T T y =
      Algebra.H1Cotangent.map (ZMod p) R T T (Algebra.H1Cotangent.map ℤ (ZMod p) T T y) := by
    simp only [Algebra.H1Cotangent.map]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply]
    exact LinearMap.congr_fun (Algebra.Extension.H1Cotangent.map_eq _ _) y
  rw [hfac, Subsingleton.elim (Algebra.H1Cotangent.map ℤ (ZMod p) T T y) 0, map_zero]

/-- In characteristic `p`, the connecting map `δ : H₁(L_{T/R}) → T ⊗_R Ω_{R/ℤ}` is injective
for a field `T`. -/
theorem δ_injective_of_charP (p : ℕ) [Fact p.Prime] {R T : Type*} [CommRing R] [Field T]
    [Algebra R T] [CharP R p] [Algebra ℤ R] [Algebra ℤ T]
    [@IsScalarTower ℤ R T Algebra.toSMul Algebra.toSMul Algebra.toSMul] :
    Function.Injective (Algebra.H1Cotangent.δ ℤ R T) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ ℤ R T y).mp hy
  exact map_int_eq_zero_of_charP p z

/-- If `R → T` is surjective, `T ⊗_R Ω_{R/ℤ} → Ω_{T/ℤ}` is surjective. -/
theorem mapBaseChange_surjective_of_surjective {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Algebra ℤ R] [Algebra ℤ T]
    [@IsScalarTower ℤ R T Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (h : Function.Surjective (algebraMap R T)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange ℤ R T) := by
  have : Subsingleton Ω[T⁄R] := KaehlerDifferential.subsingleton_of_surjective R T h
  intro y
  have hy : KaehlerDifferential.map ℤ R T T y = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := ((KaehlerDifferential.exact_mapBaseChange_map ℤ R T) y).mp hy
  exact ⟨x, hx⟩

/-- The default hom of canonical presentations `S[T] → S'[T]` is the map of coefficients. -/
theorem defaultHom_base_toAlgHom {S S' T : Type*} [CommRing S] [CommRing S'] [CommRing T]
    [Algebra S S'] [Algebra S T] [Algebra S' T] [IsScalarTower S S' T] (g : MvPolynomial T S) :
    (Algebra.Generators.defaultHom (Algebra.Generators.self S T)
      (Algebra.Generators.self S' T)).toAlgHom g = MvPolynomial.map (algebraMap S S') g := by
  induction g using MvPolynomial.induction_on with
  | C s =>
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, hp, Algebra.Generators.Hom.toAlgHom_X, MvPolynomial.map_X]
    rfl

/-- The map `T ⊗_S Ω_{S/R} → T ⊗_{S'} Ω_{S'/R}` induced by `S → S'`. -/
noncomputable abbrev baseMap (R S S' T : Type*) [CommRing R] [CommRing S] [CommRing S']
    [CommRing T] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [Algebra S T]
    [Algebra S' T] [IsScalarTower S S' T] :
    T ⊗[S] Ω[S⁄R] →ₗ[T] T ⊗[S'] Ω[S'⁄R] :=
  LinearMap.liftBaseChange T
    (((TensorProduct.mk S' T Ω[S'⁄R]) 1).restrictScalars S ∘ₗ
      (KaehlerDifferential.map R R S S').restrictScalars S)

/-- Naturality of `δAux` in the middle ring. -/
theorem δAux_map {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [Algebra S T]
    [Algebra S' T] [IsScalarTower S S' T] [Algebra R T] [IsScalarTower R S T]
    [IsScalarTower R S' T] (g : MvPolynomial T S) :
    Algebra.Generators.H1Cotangent.δAux R (Algebra.Generators.self S' T)
        (MvPolynomial.map (algebraMap S S') g) =
      baseMap R S S' T (Algebra.Generators.H1Cotangent.δAux R (Algebra.Generators.self S T) g) := by
  induction g using MvPolynomial.induction_on with
  | C s =>
    rw [MvPolynomial.map_C, Algebra.Generators.H1Cotangent.δAux_C,
      Algebra.Generators.H1Cotangent.δAux_C, LinearMap.liftBaseChange_tmul, one_smul]
    simp [KaehlerDifferential.map_D]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.map_X, Algebra.Generators.H1Cotangent.δAux_mul,
      Algebra.Generators.H1Cotangent.δAux_X, smul_zero, zero_add, hp,
      Algebra.Generators.H1Cotangent.δAux_mul, Algebra.Generators.H1Cotangent.δAux_X, smul_zero,
      zero_add]
    simp only [← @IsScalarTower.algebraMap_smul (Algebra.Generators.self S T).Ring T,
      ← @IsScalarTower.algebraMap_smul (Algebra.Generators.self S' T).Ring T,
      Algebra.Generators.algebraMap_apply, aeval_X, Algebra.Generators.self_val, id_eq]
    rw [map_smul]

theorem aeval_map_eq_zero {S S' T : Type*} [CommRing S] [CommRing S'] [CommRing T]
    [Algebra S S'] [Algebra S T] [Algebra S' T] [IsScalarTower S S' T] (g : MvPolynomial T S)
    (hg : aeval (fun t : T => t) g = 0) :
    aeval (fun t : T => t) (MvPolynomial.map (algebraMap S S') g) = 0 := by
  rw [MvPolynomial.aeval_map_algebraMap, hg]

/-- Naturality of the Jacobi–Zariski connecting map `δ : H₁(L_{T/S}) → T ⊗_S Ω_{S/R}` in `S`. -/
theorem δ_map_base {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [Algebra S T]
    [Algebra S' T] [IsScalarTower S S' T] [Algebra R T] [IsScalarTower R S T]
    [IsScalarTower R S' T] (x : Algebra.H1Cotangent S T) :
    Algebra.H1Cotangent.δ R S' T (Algebra.H1Cotangent.map S S' T T x) =
      baseMap R S S' T (Algebra.H1Cotangent.δ R S T x) := by
  obtain ⟨xv, hx⟩ := x
  obtain ⟨⟨g, hg⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective xv
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : MvPolynomial T S, g₀ = g := ⟨g, rfl⟩
  have hg' : MvPolynomial.map (algebraMap S S') g₀ ∈
      (Algebra.Generators.self S' T).toExtension.ker := aeval_map_eq_zero (S' := S') g₀ hg
  have hy1 : (Algebra.H1Cotangent.map S S' T T
      (⟨Algebra.Extension.Cotangent.mk ⟨g₀, hg⟩, hx⟩ :
        LinearMap.ker (Algebra.Generators.self S T).toExtension.cotangentComplex)).1 =
      Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self S' T).toExtension)
        ⟨_, hg'⟩ := by
    change Algebra.Extension.Cotangent.map _ (Algebra.Extension.Cotangent.mk
      (P := (Algebra.Generators.self S T).toExtension) ⟨g₀, hg⟩) = _
    rw [Algebra.Extension.Cotangent.map_mk]
    congr 2
    exact defaultHom_base_toAlgHom g₀
  rw [show Algebra.H1Cotangent.map S S' T T
      (⟨Algebra.Extension.Cotangent.mk ⟨g₀, hg⟩, hx⟩ :
        LinearMap.ker (Algebra.Generators.self S T).toExtension.cotangentComplex) =
      (⟨_, hy1 ▸ (Algebra.H1Cotangent.map S S' T T ⟨_, hx⟩).2⟩ :
        LinearMap.ker (Algebra.Generators.self S' T).toExtension.cotangentComplex) from
    Subtype.ext hy1]
  unfold Algebra.H1Cotangent.δ
  exact (Algebra.Generators.H1Cotangent.δ_eq_δAux (Algebra.Generators.self S' T)
    (Algebra.Generators.self R S') ⟨_, hg'⟩ _).trans ((δAux_map (R := R) g₀).trans
    (congrArg (baseMap R S S' T)
      (Algebra.Generators.H1Cotangent.δ_eq_δAux (Algebra.Generators.self S T)
        (Algebra.Generators.self R S) ⟨g₀, hg⟩ hx).symm))

end Faltings

end Langlands.CommutativeAlgebra.Popescu
