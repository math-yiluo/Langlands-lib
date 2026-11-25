/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraUnitScalarTensor

/-!
# Tensor powers of a strict pair trivialized by a scalar

Let `P` be a monoidal endofunctor and `K = (T, φ)` a pair with `φ : P T ≅ T`. The tensor powers
`K^{⊗ d} = (T^{⊗ d}, φ_d)` are built by `φ_{d+1} = μ⁻¹ ≫ (φ_d ⊗ φ)`
(`CategoryTheory.Endofunctor.IsoAlgebra.tensorPowPair`), as the Tate twists
`ℚ̄_ℓ(d) = ℚ̄_ℓ(1)^{⊗ d}` with their pullback isomorphisms
(`AlgebraicGeometry.ProEtale.upperStarTateTwistNatIso`). If `K` is isomorphic to the unit with
structure `ε⁻¹ ≫ s` for a scalar `s : 𝟙 ≅ 𝟙` (`unitScalarPair P s`), then `K^{⊗ d}` is
isomorphic to the unit with structure `ε⁻¹ ≫ s^d`
(`CategoryTheory.Endofunctor.IsoAlgebra.tensorPowPairIso`): the Frobenius acts on `ℚ̄_ℓ(d)` by
`χ_ℓ(σ)^d` as soon as it acts on `ℚ̄_ℓ(1)` by `χ_ℓ(σ)`.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C ⥤ C) [P.Monoidal]

/-- The `d`-th power `s^d = s ≫ ⋯ ≫ s` of a scalar `s : 𝟙 ≅ 𝟙`. -/
def scalarPow (s : 𝟙_ C ≅ 𝟙_ C) : ℕ → (𝟙_ C ≅ 𝟙_ C)
  | 0 => Iso.refl _
  | d + 1 => scalarPow s d ≪≫ s

/-- The tensor powers `K^{⊗ d}` of a pair `K = (T, φ)`: `K^{⊗ 0} = (𝟙, ε⁻¹)` and
`K^{⊗ (d+1)} = K^{⊗ d} ⊗ K = (T^{⊗ d} ⊗ T, μ⁻¹ ≫ (φ_d ⊗ φ))`. -/
def tensorPowPair (K : IsoAlgebra P) : ℕ → IsoAlgebra P
  | 0 => mk (𝟙_ C) (Functor.Monoidal.εIso P).symm
  | d + 1 => (tensorWith P K.str).obj (tensorPowPair K d)

@[simp]
lemma tensorPowPair_zero (K : IsoAlgebra P) :
    tensorPowPair P K 0 = mk (𝟙_ C) (Functor.Monoidal.εIso P).symm :=
  rfl

@[simp]
lemma tensorPowPair_succ (K : IsoAlgebra P) (d : ℕ) :
    tensorPowPair P K (d + 1) = (tensorWith P K.str).obj (tensorPowPair P K d) :=
  rfl

/-- Tensoring with a pair `K` isomorphic to `(𝟙, ε⁻¹ ≫ s)` is tensoring with `(𝟙, ε⁻¹ ≫ s)`. -/
def tensorWithIsoOfIsoUnitScalar {K : IsoAlgebra P} {s : 𝟙_ C ≅ 𝟙_ C}
    (e : K ≅ unitScalarPair P s) :
    tensorWith P K.str ≅ tensorWith P ((Functor.Monoidal.εIso P).symm ≪≫ s) :=
  NatIso.ofComponents (fun M ↦ isoMk (tensorIso (Iso.refl M.carrier) ((forget P).mapIso e)) (by
    have he : P.map e.hom.hom.f ≫ (η P ≫ s.hom) = K.obj.str ≫ e.hom.hom.f := e.hom.hom.h
    change P.map (𝟙 M.carrier ⊗ₘ e.hom.hom.f) ≫ (δ P _ _ ≫ (M.obj.str ⊗ₘ (η P ≫ s.hom))) =
      (δ P _ _ ≫ (M.obj.str ⊗ₘ K.obj.str)) ≫ (𝟙 M.carrier ⊗ₘ e.hom.hom.f)
    rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
      tensorHom_comp_tensorHom, P.map_id, Category.id_comp, he, Category.assoc,
      tensorHom_comp_tensorHom, Category.comp_id]))
    (fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
      have key : ∀ {A A' B B' : C} (a : A ⟶ A') (b : B ⟶ B'),
          (a ⊗ₘ 𝟙 B) ≫ (𝟙 A' ⊗ₘ b) = (𝟙 A ⊗ₘ b) ≫ (a ⊗ₘ 𝟙 B') := fun a b ↦ by
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
          Category.comp_id, Category.id_comp, Category.comp_id]
      change (f.hom.f ⊗ₘ 𝟙 K.carrier) ≫ (𝟙 _ ⊗ₘ e.hom.hom.f) =
        (𝟙 _ ⊗ₘ e.hom.hom.f) ≫ (f.hom.f ⊗ₘ 𝟙 (𝟙_ C))
      exact key _ _)))

/-- **Tensor powers of a trivialized pair**: if `K ≅ (𝟙, ε⁻¹ ≫ s)`, then
`K^{⊗ d} ≅ (𝟙, ε⁻¹ ≫ s^d)`. -/
def tensorPowPairIso {K : IsoAlgebra P} {s : 𝟙_ C ≅ 𝟙_ C} (e : K ≅ unitScalarPair P s) :
    ∀ d : ℕ, tensorPowPair P K d ≅ unitScalarPair P (scalarPow s d)
  | 0 => isoMk (Iso.refl _) (by
      change P.map (𝟙 _) ≫ (η P ≫ (𝟙 _)) = η P ≫ 𝟙 _
      rw [P.map_id, Category.id_comp])
  | d + 1 => (tensorWith P K.str).mapIso (tensorPowPairIso e d) ≪≫
      (tensorWithIsoOfIsoUnitScalar P e).app (unitScalarPair P (scalarPow s d)) ≪≫
      unitScalarPairTensorIso P (scalarPow s d) s

/-- The underlying statement of `tensorPowPairIso`: an isomorphism `T^{⊗ d} ≅ 𝟙` carrying the
structure `φ_d` of the `d`-th tensor power to `ε⁻¹ ≫ s^d`. -/
theorem exists_iso_tensorPowPair_carrier {K : IsoAlgebra P} {s : 𝟙_ C ≅ 𝟙_ C}
    (e : K ≅ unitScalarPair P s) (d : ℕ) :
    ∃ ê : (tensorPowPair P K d).carrier ≅ 𝟙_ C,
      P.map ê.hom ≫ (η P ≫ (scalarPow s d).hom) = (tensorPowPair P K d).obj.str ≫ ê.hom :=
  ⟨(forget P).mapIso (tensorPowPairIso P e d), (tensorPowPairIso P e d).hom.hom.h⟩

section Conj

variable {C : Type u} [Category.{v} C] {P L : C ⥤ C} (u : P ≅ L)

/-- **Transport of a trivialized pair along `u : P ≅ L`.** A pair `(T, u⁻¹ ≫ φ)` for `L`, obtained
from a pair `(T, φ)` for `P`, is isomorphic to `(R, σ ≫ r)` as soon as `ê : T ≅ R` carries `φ` to
`ψ ≫ sd` (the datum on `R` for `P`), where `σ = u⁻¹ ≫ ψ` and `r = sd`. -/
def isoMkOfConj {T R : C} (φ : P.obj T ≅ T) (ψ : P.obj R ⟶ R) (sd : R ⟶ R) (σ : L.obj R ≅ R)
    (r : R ≅ R) (ê : T ≅ R) (hê : P.map ê.hom ≫ (ψ ≫ sd) = φ.hom ≫ ê.hom)
    (hunit : σ.hom = u.inv.app R ≫ ψ) (hr : r.hom = sd) :
    mk T ((u.app T).symm ≪≫ φ) ≅ mk R (σ ≪≫ r) :=
  isoMk ê (by
    have hn : L.map ê.hom ≫ u.inv.app R = u.inv.app T ≫ P.map ê.hom := u.inv.naturality ê.hom
    change L.map ê.hom ≫ (σ.hom ≫ r.hom) = ((u.app T).symm.hom ≫ φ.hom) ≫ ê.hom
    rw [hunit, hr]
    simp only [Iso.symm_hom, Iso.app_inv, Category.assoc]
    rw [reassoc_of% hn, hê])

end Conj

end CategoryTheory.Endofunctor.IsoAlgebra
