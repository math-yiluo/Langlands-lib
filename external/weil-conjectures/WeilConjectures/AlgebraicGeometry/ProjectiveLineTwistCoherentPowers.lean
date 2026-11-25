/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Coherent tensor powers of twists on the projective line

Source: Stacks Project, Constructions, Tags 01MS and 01MU.
(blueprint: lem-sc-p1-twist-coherent-powers).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def positivePowers {X : Scheme.{u}} (L : ℤ → X.Modules)
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0) :
    ∀ a : ℕ, (L 1).tensorPow a ≅ L (a : ℤ)
  | 0 => e₀
  | a + 1 => by
      letI := hiso (a : ℤ) 1
      exact (β_ _ _) ≪≫
        whiskerRightIso (positivePowers L μ hiso e₀ a) (L 1) ≪≫
        asIso (μ (a : ℤ) 1) ≪≫ eqToIso (congrArg L (by omega))

private noncomputable def negativePowers {X : Scheme.{u}} (L : ℤ → X.Modules)
    (D : X.Modules) (ev : L 1 ⊗ D ≅ 𝟙_ X.Modules)
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0) :
    ∀ a : ℕ, D.tensorPow a ≅ L (-(a : ℤ))
  | 0 => e₀
  | a + 1 => by
      letI := hiso (-((a + 1 : ℕ) : ℤ)) 1
      let F := (BraidedCategory.tensorRightEquivalence (L 1) D ev).functor
      exact F.preimageIso ((β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso ev (D.tensorPow a) ≪≫ (λ_ _) ≪≫
        negativePowers L D ev μ hiso e₀ a ≪≫
        eqToIso (congrArg L (by omega)) ≪≫ (asIso (μ (-((a + 1 : ℕ) : ℤ)) 1)).symm)

private theorem negativePowers_succ {X : Scheme.{u}} (L : ℤ → X.Modules)
    (D : X.Modules) (ev : L 1 ⊗ D ≅ 𝟙_ X.Modules)
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0) (a : ℕ) :
    (negativePowers L D ev μ hiso e₀ (a + 1)).hom ▷ L 1 ≫
        μ (-((a + 1 : ℕ) : ℤ)) 1 ≫ eqToHom (congrArg L (by omega)) =
      (β_ (D.tensorPow (a + 1)) (L 1)).hom ≫ (α_ (L 1) D (D.tensorPow a)).inv ≫
        ev.hom ▷ D.tensorPow a ≫ (λ_ _).hom ≫
          (negativePowers L D ev μ hiso e₀ a).hom := by
  have := hiso (-((a + 1 : ℕ) : ℤ)) 1
  let F := (BraidedCategory.tensorRightEquivalence (L 1) D ev).functor
  let q := (β_ (D.tensorPow (a + 1)) (L 1)) ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso ev (D.tensorPow a) ≪≫ (λ_ _) ≪≫
    negativePowers L D ev μ hiso e₀ a ≪≫
    eqToIso (congrArg L (by omega)) ≪≫ (asIso (μ (-((a + 1 : ℕ) : ℤ)) 1)).symm
  have h := F.map_preimage q.hom
  change (negativePowers L D ev μ hiso e₀ (a + 1)).hom ▷ L 1 = q.hom at h
  rw [h]
  dsimp only [q]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, eqToIso.hom,
    Category.assoc, asIso_inv, IsIso.inv_hom_id_assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem positivePowers_square {X : Scheme.{u}} (L : ℤ → X.Modules)
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0)
    (σ : 𝟙_ X.Modules ⟶ L (0 + (1 : ℕ))) (a : ℕ) :
    (ρ_ ((L 1).tensorPow a)).inv ≫ (L 1).tensorPow a ◁ σ ≫
        (positivePowers L μ hiso e₀ a).hom ▷ _ ≫ μ (a : ℤ) 1 =
      (ρ_ ((L 1).tensorPow a)).inv ≫ (L 1).tensorPow a ◁ σ ≫
        (β_ _ _).hom ≫ (positivePowers L μ hiso e₀ (a + 1)).hom ≫
          eqToHom (congrArg L (by omega)) := by
  change (ρ_ ((L 1).tensorPow a)).inv ≫ (L 1).tensorPow a ◁ σ ≫
      (positivePowers L μ hiso e₀ a).hom ▷ L 1 ≫ μ (a : ℤ) 1 =
    (ρ_ ((L 1).tensorPow a)).inv ≫ (L 1).tensorPow a ◁ σ ≫
      (β_ ((L 1).tensorPow a) (L 1)).hom ≫
        (positivePowers L μ hiso e₀ (a + 1)).hom ≫ eqToHom (congrArg L (by omega))
  dsimp only [positivePowers]
  simp only [Iso.trans_hom, whiskerRightIso_hom, asIso_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, SymmetricCategory.symmetry_assoc]

private theorem negativePowers_square {X : Scheme.{u}} (L : ℤ → X.Modules)
    (D : X.Modules) (ev : L 1 ⊗ D ≅ 𝟙_ X.Modules)
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0)
    (σ : 𝟙_ X.Modules ⟶ L (0 + (1 : ℕ))) (a : ℕ) :
    (ρ_ (D.tensorPow (a + 1))).inv ≫ D.tensorPow (a + 1) ◁ σ ≫
        (negativePowers L D ev μ hiso e₀ (a + 1)).hom ▷ _ ≫
          μ (-((a + 1 : ℕ) : ℤ)) 1 ≫ eqToHom (congrArg L (by omega)) =
      (ρ_ (D.tensorPow (a + 1))).inv ≫ D.tensorPow (a + 1) ◁ σ ≫ (β_ _ _).hom ≫
        (α_ (L 1) D (D.tensorPow a)).inv ≫ ev.hom ▷ D.tensorPow a ≫
          (λ_ _).hom ≫ (negativePowers L D ev μ hiso e₀ a).hom := by
  change (ρ_ (D.tensorPow (a + 1))).inv ≫ D.tensorPow (a + 1) ◁ σ ≫
      (negativePowers L D ev μ hiso e₀ (a + 1)).hom ▷ L 1 ≫
        μ (-((a + 1 : ℕ) : ℤ)) 1 ≫ eqToHom (congrArg L (by omega)) =
    (ρ_ (D.tensorPow (a + 1))).inv ≫ D.tensorPow (a + 1) ◁ σ ≫
      (β_ (D.tensorPow (a + 1)) (L 1)).hom ≫ (α_ (L 1) D (D.tensorPow a)).inv ≫
        ev.hom ▷ D.tensorPow a ≫ (λ_ _).hom ≫ (negativePowers L D ev μ hiso e₀ a).hom
  have h := negativePowers_succ L D ev μ hiso e₀ a
  simpa only [Category.assoc] using congrArg
    (fun f ↦ (ρ_ (D.tensorPow (a + 1))).inv ≫ D.tensorPow (a + 1) ◁ σ ≫ f) h

private theorem coherentPowers {X : Scheme.{u}} (L : ℤ → X.Modules)
    [(L 1).IsInvertible]
    (μ : ∀ n m : ℤ, L n ⊗ L m ⟶ L (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) (e₀ : 𝟙_ X.Modules ≅ L 0)
    (ι : Type) (σ : ι → (𝟙_ X.Modules ⟶ L 1)) :
    ∃ (ePos : ∀ a : ℕ, (L 1).tensorPow a ≅ L (a : ℤ))
      (eNeg : ∀ a : ℕ, (dual (L 1)).tensorPow a ≅ L (-(a : ℤ))),
      (ePos 0).hom = e₀.hom ∧ ePos 0 = eNeg 0 ∧
      (∀ (a : ℕ) (i : ι),
        (ρ_ _).inv ≫ (L 1).tensorPow a ◁ σ i ≫
            (ePos a).hom ▷ _ ≫ μ (a : ℤ) 1 =
          (ρ_ _).inv ≫ (L 1).tensorPow a ◁ σ i ≫
            (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (congrArg L (by omega))) ∧
      (∀ (a : ℕ) (i : ι),
        (ρ_ _).inv ≫ (dual (L 1)).tensorPow (a + 1) ◁ σ i ≫
            (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
              eqToHom (congrArg L (by omega)) =
          (ρ_ _).inv ≫ (dual (L 1)).tensorPow (a + 1) ◁ σ i ≫ (β_ _ _).hom ≫
            (α_ (L 1) (dual (L 1)) ((dual (L 1)).tensorPow a)).inv ≫
            dualEvaluation (L 1) ▷ (dual (L 1)).tensorPow a ≫
            (λ_ _).hom ≫ (eNeg a).hom) := by
  let ePos := positivePowers L μ hiso e₀
  let ev := asIso (dualEvaluation (L 1))
  let eNeg := negativePowers L (dual (L 1)) ev μ hiso e₀
  refine ⟨ePos, eNeg, rfl, rfl, ?_, ?_⟩
  · intro a i
    exact positivePowers_square L μ hiso e₀ (σ i) a
  · intro a i
    exact negativePowers_square L (dual (L 1)) ev μ hiso e₀ (σ i) a

private theorem unitToTwist_one {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Proj.unitToTwistZero (𝒜 := 𝒜) =
      Proj.unitToTwist (SetLike.GradedOne.one_mem (A := 𝒜)) ≫
        eqToHom (congrArg (Proj.twist 𝒜) (by norm_num)) := by
  ext U : 3
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  apply Subtype.ext
  simp only [eqToHom_refl, Category.comp_id]
  change (s.1 x).val = (s.1 x).val * Localization.mk 1 1
  rw [Localization.mk_one_eq_algebraMap, map_one, mul_one]

private theorem twistOne_invertible (k : Type u) [Field k] :
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).IsInvertible := by
  apply Proj.isInvertible_twist _ 1
  intro x
  have hx : x ∈ ⨆ i : Fin 2,
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) := by
    rw [Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
      (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, MvPolynomial.isHomogeneous_X k i, hi⟩

/-- Multiplication isomorphisms with the pointwise product formula give normalized,
coherent identifications of positive and negative tensor powers with the twists.

Source: Stacks Project, Constructions, Tags 01MS and 01MU; Step 2 of
lem-sc-p1-twist-multiplication.
(blueprint: lem-sc-p1-twist-coherent-powers).

Proof: Start both families in degree zero with the canonical unit isomorphism,
which sends 1 to 1. Define the positive successor by braiding O(1) past its
previous tensor power and then applying multiplication. On each coordinate
chart this sends the tensor power of the coordinate basis to its ordinary power.
The perfect multiplication pairing O(1) tensor O(-1) to O(0), followed by the
inverse unit isomorphism, identifies O(-1) with the dual of O(1): locally it
sends the inverse coordinate basis to the dual basis. Define the negative family
by iterating multiplication of this inverse twist. In each coordinate chart the
negative successor square evaluates a coordinate against its dual basis and
reduces x_i^(-(a+1)) x_i to x_i^(-a). Both sides therefore agree on the local
tensor basis. The positive square similarly expresses associativity and
commutativity of fraction multiplication. The two charts cover, so these local
identities are global morphism identities. At a=0 both families use exactly
the same unit isomorphism, giving the specified normalization. No scalar choices
remain, and negative exponents are handled by localization of the coordinate. -/
theorem projectiveLine_twist_coherent_powers (k : Type u) [Field k]
    (μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m))
    (hiso : ∀ n m : ℤ, IsIso (μ n m)) :
    (∃ (ePos : ∀ a : ℕ,
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a : ℤ))
        (eNeg : ∀ a : ℕ,
          (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-(a : ℤ))),
        (ePos 0).hom =
            Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                (SetLike.GradedOne.one_mem (A := MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫
              eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by norm_num)) ∧
        ePos 0 = eNeg 0 ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (ePos a).hom ▷ _ ≫ μ (a : ℤ) 1 =
            (ρ_ _).inv ≫
              (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ◁
                Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (congrArg
                (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega))) ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
                eqToHom (congrArg
                  (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) (by omega)) =
            (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (β_ _ _).hom ≫
              (α_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1))
                ((dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                  a)).inv ≫
              dualEvaluation (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1) ▷
                (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≫
              (λ_ _).hom ≫ (eNeg a).hom)) := by
  have := twistOne_invertible k
  obtain ⟨ePos, eNeg, h₀, hsame, hpos, hneg⟩ := coherentPowers
    (X := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k))
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) μ hiso
    (Proj.unitIsoTwistZero (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)) (Fin 2)
    (fun i ↦ Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k) (d := 1)
      (MvPolynomial.X_mem_homogeneousSubmodule_one k i))
  exact ⟨ePos, eNeg,
    h₀.trans (unitToTwist_one (A := MvPolynomial (Fin 2) k)
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)),
    hsame, hpos, hneg⟩

end AlgebraicGeometry
