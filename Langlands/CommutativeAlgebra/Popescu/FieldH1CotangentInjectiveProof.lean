import Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentInjectiveStatement
import Langlands.CommutativeAlgebra.Popescu.FieldH1CotangentTools

/-! # Proof of Stacks 07E2 (first map): `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` is injective -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace FieldH1

open MvPolynomial

open scoped TensorProduct

theorem aeval_rename_eq_zero {S T T' : Type*} [CommRing S] [CommRing T] [CommRing T']
    [Algebra S T] [Algebra S T'] [Algebra T T'] [IsScalarTower S T T'] (g : MvPolynomial T S)
    (hg : aeval (fun t : T => t) g = 0) :
    aeval (fun t : T' => t) (rename (algebraMap T T') g) = 0 := by
  rw [aeval_rename]
  change aeval (algebraMap T T' ∘ fun t : T => t) g = 0
  rw [MvPolynomial.aeval_algebraMap_apply, hg, map_zero]

/-- Naturality of the Jacobi–Zariski connecting map `δ : H₁(L_{T/S}) → T ⊗_S Ω_{S/R}` in `T`. -/
theorem δ_map {R S T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing T']
    [Algebra R S] [Algebra S T] [Algebra S T'] [Algebra T T'] [IsScalarTower S T T']
    [Algebra R T] [Algebra R T'] [IsScalarTower R S T] [IsScalarTower R S T']
    (x : Algebra.H1Cotangent S T) :
    Algebra.H1Cotangent.δ R S T' (Algebra.H1Cotangent.map S S T T' x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange S T T' T' Ω[S⁄R]
        ((1 : T') ⊗ₜ[T] Algebra.H1Cotangent.δ R S T x) := by
  obtain ⟨xv, hx⟩ := x
  obtain ⟨⟨g, hg⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective xv
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : MvPolynomial T S, g₀ = g := ⟨g, rfl⟩
  have hg' : rename (algebraMap T T') g₀ ∈ (Algebra.Generators.self S T').toExtension.ker :=
    aeval_rename_eq_zero (T' := T') g₀ hg
  have hy1 : (Algebra.H1Cotangent.map S S T T'
      (⟨Algebra.Extension.Cotangent.mk ⟨g₀, hg⟩, hx⟩ :
        LinearMap.ker (Algebra.Generators.self S T).toExtension.cotangentComplex)).1 =
      Algebra.Extension.Cotangent.mk (P := (Algebra.Generators.self S T').toExtension)
        ⟨_, hg'⟩ := by
    change Algebra.Extension.Cotangent.map _ (Algebra.Extension.Cotangent.mk
      (P := (Algebra.Generators.self S T).toExtension) ⟨g₀, hg⟩) = _
    rw [Algebra.Extension.Cotangent.map_mk]
    congr 2
    exact defaultHom_self_toAlgHom g₀
  rw [show Algebra.H1Cotangent.map S S T T'
      (⟨Algebra.Extension.Cotangent.mk ⟨g₀, hg⟩, hx⟩ :
        LinearMap.ker (Algebra.Generators.self S T).toExtension.cotangentComplex) =
      (⟨_, hy1 ▸ (Algebra.H1Cotangent.map S S T T' ⟨_, hx⟩).2⟩ :
        LinearMap.ker (Algebra.Generators.self S T').toExtension.cotangentComplex) from
    Subtype.ext hy1]
  unfold Algebra.H1Cotangent.δ
  exact (Algebra.Generators.H1Cotangent.δ_eq_δAux (Algebra.Generators.self S T')
    (Algebra.Generators.self R S) ⟨_, hg'⟩ _).trans ((δAux_rename (R := R) g₀).trans
    (congrArg (fun z =>
      TensorProduct.AlgebraTensorModule.cancelBaseChange S T T' T' Ω[S⁄R] ((1 : T') ⊗ₜ[T] z))
      (Algebra.Generators.H1Cotangent.δ_eq_δAux (Algebra.Generators.self S T)
        (Algebra.Generators.self R S) ⟨g₀, hg⟩ hx).symm))

/-- `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` is injective as soon as `H₁(L_{L/F}) = 0` for some base
`F → K`: then `δ : H₁(L_{L/K}) → L ⊗_K Ω_{K/F}` is injective, and `δ` is natural in `L → M`. -/
theorem liftBaseChange_map_injective_of_base {F : Type*} {K L M : Type u} [CommRing F] [Field K]
    [Field L] [Field M] [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower F K L] [IsScalarTower F K M] [IsScalarTower K L M]
    (hL : Subsingleton (Algebra.H1Cotangent F L)) :
    Function.Injective ((Algebra.H1Cotangent.map K K L M).liftBaseChange M) := by
  have hδL : Function.Injective (Algebra.H1Cotangent.δ F K L) := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ F K L h).mp hh
    rw [Subsingleton.elim y 0, map_zero]
  let β := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M Ω[K⁄F]
  have hcomm : ∀ w, Algebra.H1Cotangent.δ F K M
      ((Algebra.H1Cotangent.map K K L M).liftBaseChange M w) =
      β ((Algebra.H1Cotangent.δ F K L).baseChange M w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul m h =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, δ_map, LinearMap.baseChange_tmul, ← map_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hinj : Function.Injective ((Algebra.H1Cotangent.δ F K L).baseChange M) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hδL
  intro a b hab
  apply hinj
  apply β.injective
  rw [← hcomm, ← hcomm, hab]

/-- **Stacks 07E2** (injectivity of the first map). -/
theorem fieldH1CotangentInjective : FieldH1CotangentInjectiveStatement.{u} := by
  intro K L M _ _ _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | hp0
  · have : Fact p.Prime := ⟨hprime⟩
    have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
    let _ := ZMod.algebra K p
    let _ := ZMod.algebra L p
    let _ := ZMod.algebra M p
    have : IsScalarTower (ZMod p) K L := .of_algebraMap_eq' (RingHom.ext_zmod _ _)
    have : IsScalarTower (ZMod p) K M := .of_algebraMap_eq' (RingHom.ext_zmod _ _)
    exact liftBaseChange_map_injective_of_base (F := ZMod p)
      (subsingleton_h1Cotangent_of_perfectField (ZMod p) L)
  · subst hp0
    have : CharZero K := CharP.charP_to_charZero K
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    have : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
    have : IsScalarTower ℚ K L := .of_algebraMap_eq' (RingHom.ext_rat _ _)
    have : IsScalarTower ℚ K M := .of_algebraMap_eq' (RingHom.ext_rat _ _)
    exact liftBaseChange_map_injective_of_base (F := ℚ)
      (subsingleton_h1Cotangent_of_perfectField ℚ L)

end FieldH1

end Langlands.CommutativeAlgebra.Popescu
