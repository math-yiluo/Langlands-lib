/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The Koszul sequence of the homogeneous coordinates

Multiplication by the homogeneous coordinate `Tᵢ` is a morphism `𝒪(m) ⟶ 𝒪(m + 1)` on
`ℙ(n; S)`, an isomorphism over the standard open `D₊(Tᵢ)`. On the projective line `ℙ¹_S` the
Koszul complex of the two coordinates `x₀, x₁` is a short exact sequence
`0 → 𝒪(m) → 𝒪(m + 1)² → 𝒪(m + 2) → 0`.

## Main definitions and results

- `AlgebraicGeometry.ProjectiveSpace.twistMulX`: multiplication by `Tᵢ`.
- `AlgebraicGeometry.ProjectiveLine.koszul`: the Koszul complex `𝒪(m) → 𝒪(m + 1)² → 𝒪(m + 2)`.
- `AlgebraicGeometry.ProjectiveLine.koszul_shortExact`: it is short exact.

Exactness is checked on the two standard opens, where it is split by
`AlgebraicGeometry.isIso_of_koszul`, using the local criteria
`AlgebraicGeometry.Scheme.Modules.mono_of_restrict` and
`AlgebraicGeometry.Scheme.Modules.epi_of_surjective_stalk`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

section Koszul

variable {D : Type*} [Category D] [Preadditive D]

/-- **The local splitting of the Koszul complex.** Let `E` be a direct sum of two copies of `B`,
with inclusions `i₀, i₁` and projections `q₀, q₁`, let `a₀, a₁ : A ⟶ B` and `b₀, b₁ : B ⟶ C`
with `a₀ ≫ b₁ = a₁ ≫ b₀`, and assume that `a₀` and `b₀` are isomorphisms. If `c : E ⟶ Q` is an
epimorphism killing `a₁ ≫ i₀ - a₀ ≫ i₁`, then the morphism `Q ⟶ C` induced by `(b₀, b₁)` is an
isomorphism. -/
lemma isIso_of_koszul {A B C E Q : D} (i₀ i₁ : B ⟶ E) (q₀ q₁ : E ⟶ B)
    (hq : q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 E) (a₀ a₁ : A ⟶ B) (b₀ b₁ : B ⟶ C) [IsIso a₀] [IsIso b₀]
    (hab : a₀ ≫ b₁ = a₁ ≫ b₀) (c : E ⟶ Q) [Epi c] (hc : a₁ ≫ i₀ ≫ c = a₀ ≫ i₁ ≫ c)
    (v : E ⟶ C) (hv₀ : i₀ ≫ v = b₀) (hv₁ : i₁ ≫ v = b₁) (v' : Q ⟶ C) (hv' : c ≫ v' = v) :
    IsIso v' := by
  have h₁ : b₁ ≫ inv b₀ ≫ i₀ ≫ c = i₁ ≫ c := by
    rw [← cancel_epi a₀, reassoc_of% hab, IsIso.hom_inv_id_assoc, hc]
  refine ⟨inv b₀ ≫ i₀ ≫ c, ?_, by simp [hv', hv₀]⟩
  rw [← cancel_epi c, reassoc_of% hv', Category.comp_id]
  conv_lhs => rw [← Category.id_comp v, ← hq]
  simp only [Preadditive.add_comp, Category.assoc, hv₀, hv₁, IsIso.hom_inv_id_assoc, h₁]
  rw [← Category.assoc q₀, ← Category.assoc q₁, ← Preadditive.add_comp, hq, Category.id_comp]

end Koszul

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- **Multiplication by the homogeneous coordinate `Tᵢ`**, as a morphism `𝒪(m) ⟶ 𝒪(m + 1)` on
`ℙ(n; S)`: the pullback of the multiplication by `Tᵢ` on the integral model `Proj ℤ[Tᵢ]`. -/
def twistMulX (i : n) (m : ℤ) : twist n S m ⟶ twist n S (m + 1) :=
  (Scheme.Modules.pullback (toProjInt n S)).map
    (Proj.twistMul m (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))

/-- Multiplication by `Tᵢ` is an isomorphism over the standard open `D₊(Tᵢ)`. -/
instance isIso_restrict_twistMulX (i : n) (m : ℤ) :
    IsIso ((restrictFunctor (standardOpen n S i).ι).map (twistMulX n S i m)) :=
  isIso_restrictFunctor_map_pullback_map (toProjInt n S) _

/-- Multiplications by two homogeneous coordinates commute. -/
lemma twistMulX_comp_twistMulX (i j : n) (m : ℤ) :
    twistMulX n S i m ≫ twistMulX n S j (m + 1) = twistMulX n S j m ≫ twistMulX n S i (m + 1) := by
  rw [twistMulX, twistMulX, twistMulX, twistMulX, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (Scheme.Modules.pullback (toProjInt n S)).map
    (Proj.twistMul_comp_twistMul m _ _)

end ProjectiveSpace

namespace ProjectiveLine

open ProjectiveSpace Scheme.Modules

variable (S : Scheme.{u}) (m : ℤ)

/-- Multiplication by the homogeneous coordinate `xᵢ`, `𝒪(m) ⟶ 𝒪(m + 1)` on `ℙ¹_S`. -/
abbrev mulX (i : Fin 2) :
    twist (ULift.{u} (Fin 2)) S m ⟶ twist (ULift.{u} (Fin 2)) S (m + 1) :=
  twistMulX (ULift.{u} (Fin 2)) S ⟨i⟩ m

/-- The first map `(x₁, -x₀) : 𝒪(m) ⟶ 𝒪(m + 1) ⊕ 𝒪(m + 1)` of the Koszul complex of the
homogeneous coordinates `x₀, x₁` of `ℙ¹_S`. -/
def koszulLeft : twist (ULift.{u} (Fin 2)) S m ⟶
    twist (ULift.{u} (Fin 2)) S (m + 1) ⊞ twist (ULift.{u} (Fin 2)) S (m + 1) :=
  biprod.lift (mulX S m 1) (-mulX S m 0)

/-- The second map `(x₀, x₁) : 𝒪(m + 1) ⊕ 𝒪(m + 1) ⟶ 𝒪(m + 2)` of the Koszul complex of the
homogeneous coordinates `x₀, x₁` of `ℙ¹_S`. -/
def koszulRight : twist (ULift.{u} (Fin 2)) S (m + 1) ⊞ twist (ULift.{u} (Fin 2)) S (m + 1) ⟶
    twist (ULift.{u} (Fin 2)) S (m + 1 + 1) :=
  biprod.desc (mulX S (m + 1) 0) (mulX S (m + 1) 1)

@[reassoc (attr := simp)]
lemma koszulLeft_comp_koszulRight : koszulLeft S m ≫ koszulRight S m = 0 := by
  simp only [koszulLeft, koszulRight, biprod.lift_desc, Preadditive.neg_comp]
  rw [twistMulX_comp_twistMulX]
  exact add_neg_cancel _

/-- **The Koszul complex** `0 → 𝒪(m) → 𝒪(m + 1)² → 𝒪(m + 2) → 0` of the homogeneous
coordinates on `ℙ¹_S`. -/
@[simps!]
def koszul : ShortComplex (ProjectiveLine S).Modules :=
  ShortComplex.mk _ _ (koszulLeft_comp_koszulRight S m)

lemma koszulLeft_comp_neg_snd :
    koszulLeft S m ≫ (-biprod.snd) = mulX S m 0 := by
  simp [koszulLeft]

lemma ulift_fin_two_cases (k : ULift.{u} (Fin 2)) : k = ULift.up 0 ∨ k = ULift.up 1 := by
  obtain ⟨k⟩ := k
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

instance mono_koszulLeft : Mono (koszulLeft S m) := by
  refine mono_of_restrict _ (standardOpen _ S) (iSup_standardOpen _ S) fun k ↦ ?_
  set F := restrictFunctor (standardOpen (ULift.{u} (Fin 2)) S k).ι
  rcases ulift_fin_two_cases k with rfl | rfl
  · exact mono_of_mono_fac (show F.map (koszulLeft S m) ≫ F.map (-biprod.snd) =
      F.map (mulX S m 0) by rw [← F.map_comp, koszulLeft_comp_neg_snd])
  · exact mono_of_mono_fac (show F.map (koszulLeft S m) ≫ F.map biprod.fst =
      F.map (mulX S m 1) by
        rw [← F.map_comp, koszulLeft, biprod.lift_fst])

/-- The morphism `coker (x₁, -x₀) ⟶ 𝒪(m + 2)` induced by `(x₀, x₁)`. -/
abbrev koszulCokernelDesc : cokernel (koszulLeft S m) ⟶ twist (ULift.{u} (Fin 2)) S (m + 1 + 1) :=
  cokernel.desc _ _ (koszulLeft_comp_koszulRight S m)

instance isIso_restrict_koszulCokernelDesc (k : ULift.{u} (Fin 2)) :
    IsIso ((restrictFunctor (standardOpen _ S k).ι).map (koszulCokernelDesc S m)) := by
  set F := restrictFunctor (standardOpen (ULift.{u} (Fin 2)) S k).ι
  set O := twist (ULift.{u} (Fin 2)) S (m + 1)
  have hq : F.map (biprod.fst : O ⊞ O ⟶ O) ≫ F.map biprod.inl +
      F.map (biprod.snd : O ⊞ O ⟶ O) ≫ F.map biprod.inr = 𝟙 _ := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  have hc : (mulX S m 1 ≫ biprod.inl - mulX S m 0 ≫ biprod.inr) ≫
      cokernel.π (koszulLeft S m) = 0 := by
    rw [← cokernel.condition (koszulLeft S m), koszulLeft, biprod.lift_eq, Preadditive.neg_comp,
      sub_eq_add_neg]
  rw [Preadditive.sub_comp, sub_eq_zero, Category.assoc, Category.assoc] at hc
  have hc' := congrArg F.map hc
  simp only [F.map_comp] at hc'
  have hab := congrArg F.map (twistMulX_comp_twistMulX (ULift.{u} (Fin 2)) S ⟨0⟩ ⟨1⟩ m)
  simp only [F.map_comp] at hab
  rcases ulift_fin_two_cases k with rfl | rfl
  · exact isIso_of_koszul (F.map biprod.inl) (F.map biprod.inr) (F.map biprod.fst)
      (F.map biprod.snd) hq (F.map (mulX S m 0)) (F.map (mulX S m 1))
      (F.map (mulX S (m + 1) 0)) (F.map (mulX S (m + 1) 1)) hab
      (F.map (cokernel.π _)) hc' (F.map (koszulRight S m))
      (by rw [← F.map_comp, koszulRight, biprod.inl_desc])
      (by rw [← F.map_comp, koszulRight, biprod.inr_desc])
      _ (by rw [← F.map_comp, cokernel.π_desc])
  · exact isIso_of_koszul (F.map biprod.inr) (F.map biprod.inl) (F.map biprod.snd)
      (F.map biprod.fst) ((add_comm _ _).trans hq) (F.map (mulX S m 1))
      (F.map (mulX S m 0))
      (F.map (mulX S (m + 1) 1)) (F.map (mulX S (m + 1) 0)) hab.symm
      (F.map (cokernel.π _)) hc'.symm (F.map (koszulRight S m))
      (by rw [← F.map_comp, koszulRight, biprod.inr_desc])
      (by rw [← F.map_comp, koszulRight, biprod.inl_desc])
      _ (by rw [← F.map_comp, cokernel.π_desc])

instance isIso_koszulCokernelDesc : IsIso (koszulCokernelDesc S m) := by
  have : Mono (koszulCokernelDesc S m) :=
    mono_of_restrict _ (standardOpen _ S) (iSup_standardOpen _ S) fun _ ↦ inferInstance
  have : Epi (koszulCokernelDesc S m) := by
    refine epi_of_surjective_stalk _ fun x ↦ ?_
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen (ULift.{u} (Fin 2)) S).ge (Set.mem_univ x))
    exact (bijective_stalk_of_isIso_restrict _ x hk).2
  exact isIso_of_mono_of_epi _

/-- **The Koszul complex is exact**: `0 → 𝒪(m) → 𝒪(m + 1)² → 𝒪(m + 2) → 0` is a short exact
sequence on `ℙ¹_S`. -/
theorem koszul_shortExact : (koszul S m).ShortExact := by
  have hg : koszulRight S m = cokernel.π (koszulLeft S m) ≫ koszulCokernelDesc S m :=
    (cokernel.π_desc _ _ _).symm
  have : Epi (koszul S m).g := by
    change Epi (koszulRight S m)
    rw [hg]
    infer_instance
  have hf : Mono (koszul S m).f := mono_koszulLeft S m
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) hf this
  exact IsColimit.ofIsoColimit (cokernelIsCokernel (koszulLeft S m))
    (Cofork.ext (asIso (koszulCokernelDesc S m)) (cokernel.π_desc _ _ _))

end ProjectiveLine

end AlgebraicGeometry
