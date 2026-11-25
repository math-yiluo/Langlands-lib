/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistProductMorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.ProjHomogeneousSectionTensorPowersLocus

/-!
# Multiplication and coordinate loci of twists on the projective line

Source: Stacks Project, Constructions, Tags 01MS, 01MU, 01MV and 01NG
(blueprint: lem-sc-p1-twist-multiplication).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem degree_one_cover (k : Type u) [Field k]
    (x : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :
    ∃ f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 1,
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f := by
  have h := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
    (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    (MvPolynomial.adjoin_range_X_eq_top (Fin 2) k)
  have hx : x ∈ ⨆ i : Fin 2, Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) := by
    rw [h]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, MvPolynomial.isHomogeneous_X k i, hi⟩

private theorem coordinate_locus (k : Type u) [Field k] (i : Fin 2) :
    nonvanishingLocus (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
      (Hom.app (Proj.unitToTwist (MvPolynomial.X_mem_homogeneousSubmodule_one k i)) ⊤
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k), ⊤))) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) :
        Set (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k))) := by
  exact (proj_homogeneous_section_tensor_powers_locus k (d := 1) Nat.zero_lt_one
      (MvPolynomial.X_mem_homogeneousSubmodule_one k i)).symm

private theorem multiplication_isIso (k : Type u) [Field k]
    (μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m))
    (hmul : (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x)))
    (n m : ℤ) : IsIso (μ n m) := by
  apply Hom.isIso_of_forall_bijective_app
  intro x
  obtain ⟨f, hf, hx⟩ := degree_one_cover k x
  refine ⟨Proj.basicOpen _ f, hx, ?_⟩
  intro W hW
  let s := (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n).presheaf.map
    (homOfLE hW).op (Proj.twistPowSection n hf)
  let t := (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m).presheaf.map
    (homOfLE hW).op (Proj.twistPowSection m hf)
  let v := (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m)).presheaf.map
    (homOfLE hW).op (Proj.twistPowSection (n + m) hf)
  have hs : IsFreeGenerator s := (Proj.isFreeGenerator_twistPowSection n hf).map hW
  have ht : IsFreeGenerator t := (Proj.isFreeGenerator_twistPowSection m hf).map hW
  have hv : IsFreeGenerator v :=
    (Proj.isFreeGenerator_twistPowSection (n + m) hf).map hW
  have hst : (μ n m).app W (tmulSection s t) = v := by
    refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
    rw [hmul]
    exact Proj.val_twistPowSection_mul n hf rfl ⟨y.1, hW y.2⟩
  have hgen := (hs.tmulSection ht).bijective
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := hgen.2 a
    obtain ⟨q, rfl⟩ := hgen.2 b
    have hrq : r = q := hv.bijective.1 (by
      simpa only [Hom.app_smul, hst] using hab)
    exact congrArg (fun c ↦ c • tmulSection s t) hrq
  · intro z
    obtain ⟨r, hr⟩ := hv.bijective.2 z
    refine ⟨r • tmulSection s t, ?_⟩
    simpa only [Hom.app_smul, hst] using hr

set_option backward.isDefEq.respectTransparency.types true in
/-- Twists on `Proj k[x₀,x₁]`: multiplication is an isomorphism, tensor powers of `O(1)`
(and of its dual in negative degree) identify coherently with the twists, and the
nonvanishing locus of each coordinate section is its standard chart.

Source: Stacks Project, Constructions, Tags 01MS, 01MU, 01MV and 01NG
(blueprint: lem-sc-p1-twist-multiplication).

Proof: The polynomial variables generate the algebra, so their basic opens cover
by Proj.iSup_basicOpen_eq_top'. Apply Proj.isInvertible_twist to this degree-one
cover. Obtain the pointwise multiplication morphisms from
lem-sc-p1-twist-product-morphism. On each degree-one chart the source has free
basis f^n tensor f^m and the target has free basis f^(n+m). The multiplication
formula and Proj.val_twistPowSection_mul identify these bases. Thus multiplication
is bijective on sections over all subopens of the chart, and
Hom.isIso_of_forall_bijective_app makes it globally an isomorphism. Apply
lem-sc-p1-twist-coherent-powers for the normalized positive and negative families.
Finally apply lem-sc-p1-homogeneous-section-tensor-powers-locus with d=1 and
f=X_i to identify the coordinate nonvanishing loci. No polynomial chart gluing
or chart ring isomorphism is needed. -/
theorem projectiveLine_twist_multiplication (k : Type u) [Field k] :
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).IsInvertible ∧
    ∃ μ : ∀ n m : ℤ,
        Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n ⊗
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⟶
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n + m),
      (∀ n m : ℤ, IsIso (μ n m)) ∧
      (∀ (n m : ℤ) (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
        (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, U))
        (t : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m, U)) (x : U),
        (((μ n m).app U (tmulSection s t)).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * (t.1 x)) ∧
      (∃ (ePos : ∀ a : ℕ,
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (a : ℤ))
        (eNeg : ∀ a : ℕ,
          (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow a ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-(a : ℤ))),
        (ePos 0).hom =
            Proj.unitToTwist (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                (SetLike.GradedOne.one_mem (A := MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫
              eqToHom (by congr 1) ∧
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
              (β_ _ _).hom ≫ (ePos (a + 1)).hom ≫ eqToHom (by congr 1)) ∧
        (∀ (a : ℕ) (i : Fin 2),
          (ρ_ _).inv ≫
              (dual (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)).tensorPow
                (a + 1) ◁ Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i) ≫
              (eNeg (a + 1)).hom ▷ _ ≫ μ (-((a + 1 : ℕ) : ℤ)) 1 ≫
                eqToHom (by congr 1; omega) =
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
              (λ_ _).hom ≫ (eNeg a).hom)) ∧
      (∀ i : Fin 2,
        nonvanishingLocus (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1)
            (Scheme.Modules.Hom.app
              (Proj.unitToTwist
                  (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k)
                  (MvPolynomial.X_mem_homogeneousSubmodule_one k i)) ⊤
              (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k), ⊤))) =
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (MvPolynomial.X i) : Set (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)))) := by
  obtain ⟨μ, hmul⟩ := projectiveLine_twist_product_morphism k
  have hμ : ∀ n m : ℤ, IsIso (μ n m) := multiplication_isIso k μ hmul
  exact ⟨Proj.isInvertible_twist _ 1 (degree_one_cover k), μ, hμ, hmul,
    projectiveLine_twist_coherent_powers k μ hμ, coordinate_locus k⟩

end AlgebraicGeometry
