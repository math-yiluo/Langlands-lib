/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.Modules.FlatResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-!
# Resolutions by twists on the projective line

Let `k` be a field. Every coherent module `𝒢` on `ℙ¹_k` has a resolution
`0 → ⨁ 𝒪(-N - 1) → ⨁ 𝒪(-N) → 𝒢 → 0` by finite direct sums of twists.

Instead of the graded Hilbert syzygy theorem, this uses the Castelnuovo–Mumford regularity
argument on `ℙ¹`. Call `ℱ` *`0`-regular* if `H¹(ℱ(-1)) = 0`.

- If `ℱ` is `0`-regular, then a morphism `φ : ℰ ⟶ ℱ` which is surjective on `H⁰` is an
  epimorphism: tensoring the Koszul sequences `0 → 𝒪(a) → 𝒪(a + 1)² → 𝒪(a + 2) → 0` with `ℱ`
  shows that `H⁰(ℱ(m))² ⟶ H⁰(ℱ(m + 1))` is surjective for `m ≥ 0`, so `H⁰(φ(m))` is surjective
  for all `m ≥ 0`; by Serre vanishing the cokernel of `φ` then has no sections after any large
  twist, hence vanishes.
- If moreover `H⁰(ℱ(-1)) = 0`, then the evaluation `H⁰(ℱ) ⊗ 𝒪 ⟶ ℱ` is an isomorphism.
- For coherent `𝒢`, choose `N` with `𝒢(N)` `0`-regular (Serre vanishing). The kernel `𝒦` of the
  evaluation `H⁰(𝒢(N)) ⊗ 𝒪 ⟶ 𝒢(N)` satisfies `H⁰(𝒦) = H¹(𝒦) = 0`, so `𝒦(1)` is trivial.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.exists_shortExact_sigma_twist`: the resolution of length one.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

variable {k : Type u} [Field k]

local notation3 "𝒪(" a ")" => ProjectiveSpace.twist (ULift (Fin 2)) (Spec (CommRingCat.of k)) a

section RightExact

/-- On `ℙ¹_k`, an epimorphism `g : A ⟶ B` of quasi-coherent modules with `H¹(A) = 0` has
`H¹(B) = 0`, since `H²` vanishes on quasi-coherent modules. -/
lemma subsingleton_H_one_of_epi {A B : (ProjectiveLine (Spec (.of k))).Modules} (g : A ⟶ B)
    [Epi g] [A.IsQuasicoherent] [B.IsQuasicoherent] [Subsingleton (A.H 1)] :
    Subsingleton (B.H 1) := by
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hT : T.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  have := isQuasicoherent_kernel g
  have : Subsingleton (T.X₁.H (1 + 1)) := subsingleton_H_of_two_le k _ le_rfl
  exact subsingleton_H_of_shortExact hT 1

variable {S : ShortComplex (ProjectiveLine (Spec (.of k))).Modules} (hS : S.Exact)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

include hS in
/-- In an exact sequence `M₁ → M₂ → M₃ → 0` of quasi-coherent modules on `ℙ¹_k`, `H¹(M₁) = 0`
implies that `H⁰(M₂) ⟶ H⁰(M₃)` is surjective, since `H²` vanishes. -/
lemma surjective_H_zero_map_g_of_exact [Epi S.g] [Subsingleton (S.X₁.H 1)] :
    Function.Surjective (H.map S.g 0) := by
  let T := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)
  have hT : T.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  have := isQuasicoherent_kernel S.g
  let p : S.X₁ ⟶ kernel S.g := kernel.lift S.g S.f S.zero
  have : Epi p := hS.epi_kernelLift
  let U := ShortComplex.mk (kernel.ι p) p (kernel.condition _)
  have hU : U.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  have := isQuasicoherent_kernel p
  have : Subsingleton (U.X₁.H (1 + 1)) := subsingleton_H_of_two_le k _ le_rfl
  have : Subsingleton (T.X₁.H (0 + 1)) := subsingleton_H_of_shortExact hU 1
  exact H.surjective_map_g hT 0

end RightExact

section Generalities

variable {X : Scheme.{u}}

/-- A binary biproduct `N ⊞ N` of a quasi-coherent module with itself is quasi-coherent. -/
lemma isQuasicoherent_biprod_self (N : X.Modules) [N.IsQuasicoherent] :
    (N ⊞ N).IsQuasicoherent := by
  have := isQuasicoherent_sigma fun _ : ULift.{u} (Fin 2) ↦ N
  let e : (∐ fun _ : ULift.{u} (Fin 2) ↦ N) ≅ N ⊞ N :=
    { hom := Sigma.desc fun j ↦ if j = ⟨0⟩ then biprod.inl else biprod.inr
      inv := biprod.desc (Sigma.ι (fun _ : ULift.{u} (Fin 2) ↦ N) ⟨0⟩)
        (Sigma.ι (fun _ : ULift.{u} (Fin 2) ↦ N) ⟨1⟩)
      hom_inv_id := by
        refine Sigma.hom_ext _ _ fun j ↦ ?_
        rcases ulift_fin_two_cases j with rfl | rfl <;> simp
      inv_hom_id := by
        refine biprod.hom_ext' _ _ ?_ ?_ <;> simp }
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e this

/-- The cohomology of a binary biproduct vanishes if it vanishes for both summands. -/
lemma subsingleton_H_biprod (A B : X.Modules) (n : ℕ) [Subsingleton (A.H n)]
    [Subsingleton (B.H n)] : Subsingleton ((A ⊞ B).H n) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : (A ⊞ B).H n, z = 0 by rw [h x, h y]
  intro z
  rw [← H.map_id_apply _ n z, ← biprod.total, H.map_add_apply, H.map_comp_apply,
    H.map_comp_apply, Subsingleton.elim (H.map biprod.fst n z) 0,
    Subsingleton.elim (H.map biprod.snd n z) 0, map_zero, map_zero, add_zero]

end Generalities

section Koszul

variable (M : (ProjectiveLine (Spec (.of k))).Modules) (a : ℤ)

/-- The Koszul sequence `𝒪(a) → 𝒪(a + 1)² → 𝒪(a + 2) → 0` tensored with `M`. -/
abbrev koszulTensor : ShortComplex (ProjectiveLine (Spec (.of k))).Modules :=
  (koszul (Spec (.of k)) a).map (tensorLeft M)

/-- The Koszul sequence tensored with `M` is exact, `M ⊗ -` being right exact. -/
lemma koszulTensor_exact : (koszulTensor M a).Exact := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
  have hK := koszul_shortExact (Spec (.of k)) a
  have := hK.epi_g
  exact hK.exact.map_of_epi_of_preservesCokernel _ inferInstance inferInstance

instance epi_koszulTensor_g : Epi (koszulTensor M a).g := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  have := (koszul_shortExact (Spec (.of k)) a).epi_g
  exact (tensorLeft M).map_epi (koszul (Spec (.of k)) a).g

end Koszul

section Regularity

variable (M : (ProjectiveLine (Spec (.of k))).Modules)

lemma isQuasicoherent_koszulTensor_X₂ [M.IsQuasicoherent] (a : ℤ) :
    (koszulTensor M a).X₂.IsQuasicoherent := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
  have := isQuasicoherent_tensorObj M (𝒪(a + 1))
  have := isQuasicoherent_biprod_self (M ⊗ 𝒪(a + 1))
  exact (SheafOfModules.isQuasicoherent (ProjectiveLine (Spec (.of k))).ringCatSheaf).prop_of_iso
    ((tensorLeft M).mapBiprod (𝒪(a + 1)) (𝒪(a + 1))).symm this

lemma subsingleton_H_koszulTensor_X₂ (a : ℤ) (n : ℕ) [Subsingleton ((M ⊗ 𝒪(a + 1)).H n)] :
    Subsingleton ((koszulTensor M a).X₂.H n) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
  have := subsingleton_H_biprod (M ⊗ 𝒪(a + 1)) (M ⊗ 𝒪(a + 1)) n
  exact @subsingleton_H_of_iso _ _ _ ((tensorLeft M).mapBiprod (𝒪(a + 1)) (𝒪(a + 1))).symm n this

/-- **Propagation of `H¹`-vanishing.** On `ℙ¹_k`, if `H¹(M(b)) = 0` for a quasi-coherent `M`
then `H¹(M(b + 1)) = 0`, by the Koszul sequence tensored with `M`. -/
lemma subsingleton_H_one_tensor_twist_succ [M.IsQuasicoherent] {b c : ℤ} (hbc : b + 1 = c)
    (h : Subsingleton ((M ⊗ 𝒪(b)).H 1)) : Subsingleton ((M ⊗ 𝒪(c)).H 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, a + 1 = b := ⟨b - 1, by omega⟩
  subst hbc
  have := isQuasicoherent_koszulTensor_X₂ M a
  have := isQuasicoherent_tensorObj M (𝒪(a + 1 + 1))
  have := subsingleton_H_koszulTensor_X₂ M a 1
  exact subsingleton_H_one_of_epi (koszulTensor M a).g

/-- **Propagation of `H⁰`-surjectivity.** Let `φ : E ⟶ F` with `F` quasi-coherent on `ℙ¹_k`.
If `H¹(F(a)) = 0` and `H⁰(φ(a + 1))` is surjective, then `H⁰(φ(a + 2))` is surjective: by the
Koszul sequence tensored with `F`, every section of `F(a + 2)` comes from `F(a + 1)²`. -/
lemma surjective_H_zero_whiskerRight_twist_succ {E F : (ProjectiveLine (Spec (.of k))).Modules}
    [F.IsQuasicoherent] (φ : E ⟶ F) {a b c : ℤ} (hab : a + 1 = b) (hbc : b + 1 = c)
    (hR : Subsingleton ((F ⊗ 𝒪(a)).H 1)) (hQ : Function.Surjective (H.map (φ ▷ 𝒪(b)) 0)) :
    Function.Surjective (H.map (φ ▷ 𝒪(c)) 0) := by
  subst hab hbc
  have := isQuasicoherent_koszulTensor_X₂ F a
  have : (koszulTensor F a).X₁.IsQuasicoherent := isQuasicoherent_tensorObj F (𝒪(a))
  have : (koszulTensor F a).X₃.IsQuasicoherent := isQuasicoherent_tensorObj F (𝒪(a + 1 + 1))
  have e (f g : 𝒪(a + 1) ⊞ 𝒪(a + 1) ⟶ 𝒪(a + 1) ⊞ 𝒪(a + 1)) :
      F ◁ (f + g) = F ◁ f + F ◁ g := (tensorLeft F).map_add
  have h₂ (x : (F ⊗ (𝒪(a + 1) ⊞ 𝒪(a + 1))).H 0) :
      ∃ w, H.map (φ ▷ (𝒪(a + 1) ⊞ 𝒪(a + 1))) 0 w = x := by
    obtain ⟨z₁, hz₁⟩ := hQ (H.map (F ◁ biprod.fst) 0 x)
    obtain ⟨z₂, hz₂⟩ := hQ (H.map (F ◁ biprod.snd) 0 x)
    refine ⟨H.map (E ◁ biprod.inl) 0 z₁ + H.map (E ◁ biprod.inr) 0 z₂, ?_⟩
    rw [map_add, ← H.map_comp_apply, ← H.map_comp_apply, whisker_exchange, whisker_exchange,
      H.map_comp_apply, H.map_comp_apply, hz₁, hz₂, ← H.map_comp_apply, ← H.map_comp_apply,
      ← H.map_add_apply, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ← e, biprod.total, MonoidalCategory.whiskerLeft_id, H.map_id_apply]
  intro y
  have : Subsingleton ((koszulTensor F a).X₁.H 1) := hR
  obtain ⟨x, rfl⟩ := surjective_H_zero_map_g_of_exact (koszulTensor_exact F a) y
  obtain ⟨w, rfl⟩ := h₂ x
  refine ⟨H.map (E ◁ koszulRight (Spec (.of k)) a) 0 w, ?_⟩
  rw [← H.map_comp_apply, whisker_exchange, H.map_comp_apply]
  rfl

end Regularity

section Twisting

/-- Twisting by `𝒪(a)` is an autoequivalence of the category of `𝒪_{ℙ¹_k}`-modules. -/
lemma isEquivalence_tensorRight_twist (a : ℤ) :
    (tensorRight (𝒪(a)) : (ProjectiveLine (Spec (.of k))).Modules ⥤ _).IsEquivalence := by
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2))
    (Spec (.of k)) a (-a)
  exact (BraidedCategory.tensorRightEquivalence (𝒪(a)) (𝒪(-a))
    (e ≪≫ eqToIso (congrArg _ (add_neg_cancel a)) ≪≫
      (ProjectiveSpace.unitIsoTwistZero _ _).symm)).isEquivalence_functor

/-- `(M ⊗ 𝒪(a)) ⊗ 𝒪(b) ≅ M ⊗ 𝒪(c)` for `a + b = c`. -/
lemma nonempty_tensorObj_twist_tensorObj_twist_iso (M : (ProjectiveLine (Spec (.of k))).Modules)
    {a b c : ℤ} (h : a + b = c) : Nonempty ((M ⊗ 𝒪(a)) ⊗ 𝒪(b) ≅ M ⊗ 𝒪(c)) := by
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2))
    (Spec (.of k)) a b
  exact ⟨α_ _ _ _ ≪≫ whiskerLeftIso M (e ≪≫ eqToIso (by rw [h]))⟩

/-- A morphism `𝒪(-b) ⟶ N` vanishes if `H⁰(N(b)) = 0`: twisting by `𝒪(b)` it becomes a
morphism `𝒪 ⟶ N(b)`, i.e. a global section of `N(b)`. -/
lemma eq_zero_of_subsingleton_H_zero_tensor_twist {N : (ProjectiveLine (Spec (.of k))).Modules}
    {b : ℤ} (φ : 𝒪(-b) ⟶ N) (h : Subsingleton ((N ⊗ 𝒪(b)).H 0)) : φ = 0 := by
  have := isEquivalence_tensorRight_twist (k := k) b
  have : IsGrothendieckAbelian.{u} (ProjectiveLine (Spec (.of k))).Modules :=
    SheafOfModules.isGrothendieckAbelian _
  apply (tensorRight (𝒪(b))).map_injective
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2))
    (Spec (.of k)) (-b) b
  let u : 𝟙_ (ProjectiveLine (Spec (.of k))).Modules ≅ 𝒪(-b) ⊗ 𝒪(b) :=
    ProjectiveSpace.unitIsoTwistZero _ _ ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ e.symm
  rw [Functor.map_zero, ← cancel_epi u.hom, comp_zero]
  apply (unitHomAddEquiv _).injective
  have : Subsingleton Γ((tensorRight (𝒪(b))).obj N, ⊤) :=
    (H.zeroLinearEquiv (N ⊗ 𝒪(b))).symm.toEquiv.subsingleton
  exact Subsingleton.elim _ _

/-- **A criterion for vanishing.** A coherent module `C` on `ℙ¹_k` with `H⁰(C(m)) = 0` for all
large `m` vanishes: `C(m₀)` is a quotient of a sum of twists `𝒪(-e)`, and all morphisms
`𝒪(-e) ⟶ C(m₀)` vanish. -/
lemma isZero_of_subsingleton_H_zero_tensor_twist (C : (ProjectiveLine (Spec (.of k))).Modules)
    [C.IsQuasicoherent] [C.IsFinitePresentation] (m₀ : ℕ)
    (h : ∀ m : ℕ, m₀ ≤ m → Subsingleton ((C ⊗ 𝒪(m)).H 0)) : IsZero C := by
  have := isQuasicoherent_tensorObj C (𝒪(m₀))
  have := isFinitePresentation_tensorObj C (𝒪(m₀))
  obtain ⟨ι, _, e, ψ, hψ, -, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k (C ⊗ 𝒪(m₀))
  obtain rfl : ψ = 0 := Sigma.hom_ext _ _ fun j ↦ by
    rw [comp_zero]
    refine eq_zero_of_subsingleton_H_zero_tensor_twist _ ?_
    have := h (m₀ + e j) (by omega)
    exact subsingleton_H_of_iso (nonempty_tensorObj_twist_tensorObj_twist_iso C
      (a := m₀) (b := e j) (c := ((m₀ + e j : ℕ) : ℤ)) (by push_cast; rfl)).some.symm 0
  have hz : IsZero (C ⊗ 𝒪(m₀)) := @IsZero.of_epi_zero _ _ _ _ _ hψ
  have := isEquivalence_tensorRight_twist (k := k) (m₀ : ℤ)
  rw [IsZero.iff_id_eq_zero]
  apply (tensorRight (𝒪(m₀))).map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact hz.eq_of_src _ _

end Twisting

section Epi

/-- Let `F` be quasi-coherent on `ℙ¹_k` with `H¹(F(-1)) = 0` and let `φ : E ⟶ F` be surjective
on `H⁰`. Then for all `m ≥ 0`, `H⁰(φ(m))` is surjective and `H¹(F(m - 1)) = 0`. -/
lemma surjective_H_zero_whiskerRight_twist_nat {E F : (ProjectiveLine (Spec (.of k))).Modules}
    [F.IsQuasicoherent] (φ : E ⟶ F) (hR : Subsingleton ((F ⊗ 𝒪(-1)).H 1))
    (hQ : Function.Surjective (H.map (φ ▷ 𝒪(0)) 0)) (m : ℕ) :
    Function.Surjective (H.map (φ ▷ 𝒪(m)) 0) ∧ Subsingleton ((F ⊗ 𝒪((m : ℤ) - 1)).H 1) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, zero_sub]
    exact ⟨hQ, hR⟩
  | succ m ih =>
    exact ⟨surjective_H_zero_whiskerRight_twist_succ φ (a := (m : ℤ) - 1) (b := m) (by omega)
        (by push_cast; rfl) ih.2 ih.1,
      subsingleton_H_one_tensor_twist_succ F (b := (m : ℤ) - 1) (by push_cast; ring) ih.2⟩

/-- **Castelnuovo–Mumford on `ℙ¹_k`.** Let `F` be coherent on `ℙ¹_k` with `H¹(F(-1)) = 0`. A
morphism `φ : E ⟶ F` from a quasi-coherent module such that `H⁰(φ ⊗ 𝒪(0))` is surjective is an
epimorphism: `H⁰(φ(m))` is surjective for all `m ≥ 0`, so the cokernel `C` of `φ` has
`H⁰(C(m)) = 0` as soon as `H¹` of the image twisted by `m` vanishes, i.e. for `m ≫ 0`. -/
theorem epi_of_surjective_H_zero {E F : (ProjectiveLine (Spec (.of k))).Modules}
    [E.IsQuasicoherent] [F.IsQuasicoherent] [F.IsFinitePresentation] (φ : E ⟶ F)
    (hR : Subsingleton ((F ⊗ 𝒪(-1)).H 1)) (hQ : Function.Surjective (H.map (φ ▷ 𝒪(0)) 0)) :
    Epi φ := by
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_cokernel φ
  have := isFinitePresentation_cokernel φ
  have := isQuasicoherent_kernel (cokernel.π φ)
  have := isFinitePresentation_kernel (cokernel.π φ)
  obtain ⟨d₀, hd₀⟩ :=
    ProjectiveSpace.exists_subsingleton_H_tensor_twist k (kernel (cokernel.π φ))
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_subsingleton_H_zero_tensor_twist _ d₀.toNat fun m hm ↦ ?_)
  have := isEquivalence_tensorRight_twist (k := k) (m : ℤ)
  have hS : (ShortComplex.kernelSequence (cokernel.π φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
      (inferInstance : Epi (cokernel.π φ))
  have hS' := hS.map_of_exact (tensorRight (𝒪(m)))
  have : Subsingleton (((ShortComplex.kernelSequence (cokernel.π φ)).map
      (tensorRight (𝒪(m)))).X₁.H (0 + 1)) := hd₀ m (by omega) 1 one_pos
  have h0 : φ ▷ 𝒪(m) ≫ cokernel.π φ ▷ 𝒪(m) = 0 := by
    rw [← MonoidalCategory.comp_whiskerRight, cokernel.condition]
    exact (tensorRight _).map_zero _ _
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : (cokernel φ ⊗ 𝒪(m)).H 0, z = 0 by rw [h x, h y]
  intro z
  obtain ⟨w, rfl⟩ := H.surjective_map_g hS' 0 z
  obtain ⟨v, rfl⟩ := (surjective_H_zero_whiskerRight_twist_nat φ hR hQ m).1 w
  exact (H.map_comp_apply _ _ 0 v).symm.trans
    ((congrArg (fun g ↦ H.map g 0 v) h0).trans (H.map_zero_apply _ _))

end Epi

section Finiteness

/-- The cohomology of the twists `𝒪(a)` on `ℙ¹_k` is finite-dimensional. -/
lemma finiteDimensional_H_twist (a : ℤ) (q : ℕ) : FiniteDimensional k ((𝒪(a)).H q) := by
  rcases q with _ | _ | q
  · rcases lt_or_ge a 0 with ha | ha
    · have := subsingleton_H_zero_twist_of_neg k a ha
      infer_instance
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k n
      have : FiniteDimensional k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k n) :=
        Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ n)
      exact e.symm.finiteDimensional
  · rcases lt_or_ge a (-1) with ha | ha
    · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
      have : FiniteDimensional k
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k (-a - 2).toNat) :=
        Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ _)
      exact e.symm.finiteDimensional
    · have := subsingleton_H_one_twist k a ha
      infer_instance
  · have := subsingleton_H_of_two_le k (𝒪(a)) (q := q + 1 + 1) (by omega)
    infer_instance

/-- The cohomology of a finite sum of twists on `ℙ¹_k` is finite-dimensional. -/
lemma finiteDimensional_H_sigma_twist {ι : Type u} [Finite ι] (e : ι → ℤ) (q : ℕ) :
    FiniteDimensional k ((∐ fun j ↦ 𝒪(e j)).H q) := by
  classical
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts (ProjectiveLine (Spec (.of k))).Modules :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have := fun j ↦ finiteDimensional_H_twist (k := k) (e j) q
  exact ((H.isBilimitLinearEquiv k (biproduct.isBilimit fun j ↦ 𝒪(e j)) q).symm.trans
    ((cohomologyFunctor k q).mapIso (biproduct.isoCoproduct fun j ↦ 𝒪(e j))).toLinearEquiv
      ).finiteDimensional

/-- `H¹` of a coherent module on `ℙ¹_k` is finite-dimensional: it is a quotient of `H¹` of a
finite sum of twists (`ProjectiveSpace.exists_epi_sigma_twist`), `H²` vanishing. -/
lemma finiteDimensional_H_one_of_isCoherent (F : (ProjectiveLine (Spec (.of k))).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] : FiniteDimensional k (F.H 1) := by
  obtain ⟨ι, _, e, φ, hφ, hK, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k F
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance hφ
  have : Subsingleton (S.X₁.H (1 + 1)) := subsingleton_H_of_two_le k _ le_rfl
  have := finiteDimensional_H_sigma_twist (k := k) (fun j ↦ -(e j : ℤ)) 1
  exact Module.Finite.of_surjective (H.mapLinearMap k φ 1) (H.surjective_map_g hS 1)

/-- `H⁰` of a coherent module on `ℙ¹_k` is finite-dimensional: for a presentation
`0 → K → E → F → 0` by a finite sum of twists `E`, `H⁰(E) → H⁰(F) → H¹(K)` is exact. -/
lemma finiteDimensional_H_zero_of_isCoherent (F : (ProjectiveLine (Spec (.of k))).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] : FiniteDimensional k (F.H 0) := by
  obtain ⟨ι, _, e, φ, hφ, hK, hK'⟩ := ProjectiveSpace.exists_epi_sigma_twist k F
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance hφ
  have := finiteDimensional_H_one_of_isCoherent (kernel φ)
  have := finiteDimensional_H_sigma_twist (k := k) (fun j ↦ -(e j : ℤ)) 0
  let δ := H.δLinearMap k hS 0
  refine Module.Finite.of_exact (f := H.mapLinearMap k φ 0) (g := δ.rangeRestrict) ?_
    δ.surjective_rangeRestrict
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
  ext x
  exact SetLike.ext_iff.1 (H.ker_δ_eq_range_map_g hS 0) x

end Finiteness

section Evaluation

/-- Twisting by `𝒪(0)` does not change the surjectivity of a map on cohomology. -/
lemma surjective_H_map_whiskerRight_twist_zero_iff {E F : (ProjectiveLine (Spec (.of k))).Modules}
    (φ : E ⟶ F) (n : ℕ) :
    Function.Surjective (H.map (φ ▷ 𝒪(0)) n) ↔ Function.Surjective (H.map φ n) := by
  let v := ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))
  let iE : E ≅ E ⊗ 𝒪(0) := (ρ_ E).symm ≪≫ whiskerLeftIso E v
  let iF : F ≅ F ⊗ 𝒪(0) := (ρ_ F).symm ≪≫ whiskerLeftIso F v
  have h : φ ▷ 𝒪(0) = iE.inv ≫ φ ≫ iF.hom := by
    simp only [iE, iF, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_inv,
      whiskerLeftIso_hom, Category.assoc, Iso.symm_inv]
    rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id]
  have hE := (H.mapLinearEquiv iE.symm n).bijective
  have hF := (H.mapLinearEquiv iF n).bijective
  have hc (x : (E ⊗ 𝒪(0)).H n) :
      H.map (φ ▷ 𝒪(0)) n x = H.map iF.hom n (H.map φ n (H.map iE.inv n x)) := by
    rw [h, H.map_comp_apply, H.map_comp_apply]
  constructor
  · intro hs y
    obtain ⟨x, hx⟩ := hs (H.map iF.hom n y)
    refine ⟨H.map iE.inv n x, hF.1 ?_⟩
    exact (hc x).symm.trans hx
  · intro hs y
    obtain ⟨y', rfl⟩ := hF.2 y
    obtain ⟨x, rfl⟩ := hs y'
    obtain ⟨x', rfl⟩ := hE.2 x
    exact ⟨x', (hc x').trans (by rfl)⟩

/-- `H⁰(ℙ¹_k, 𝒪(0))` is one-dimensional. -/
lemma finrank_H_zero_twist_zero : Module.finrank k ((𝒪(0)).H 0) = 1 := by
  obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k 0
  erw [e.finrank_eq]
  rw [Module.finrank_eq_nat_card_basis
    (ProjectiveSpace.homogeneousSubmoduleBasis _ k 0)]
  have : Unique {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun s ↦ Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 s.2)⟩
  exact Nat.card_unique

/-- The class in `H⁰(ℙ¹_k, 𝒪(0))` of the unit section. -/
def unitHZero : (𝒪(0)).H 0 :=
  (H.zeroLinearEquiv _).symm
    (Hom.app (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))).hom ⊤
      (1 : Γ(ProjectiveLine (Spec (.of k)), ⊤)))

/-- The morphism `𝒪(0) ⟶ F` given by a global section of `F`. -/
def homOfSection (F : (ProjectiveLine (Spec (.of k))).Modules) (s : Γ(F, ⊤)) : 𝒪(0) ⟶ F :=
  (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))).inv ≫
    homOfGlobalSection F s

lemma H_map_homOfSection_unitHZero (F : (ProjectiveLine (Spec (.of k))).Modules) (s : Γ(F, ⊤)) :
    H.map (homOfSection F s) 0 (unitHZero (k := k)) = (H.zeroLinearEquiv F).symm s := by
  apply (H.zeroLinearEquiv F).injective
  rw [zeroLinearEquiv_map, LinearEquiv.apply_symm_apply, unitHZero, LinearEquiv.apply_symm_apply,
    homOfSection, ← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id_assoc,
    homOfGlobalSection_app_one]
  exact presheaf_map_id_apply _ _

/-- **Evaluation on global sections.** For `F` on `ℙ¹_k` with finite-dimensional `H⁰`, there is
a morphism `𝒪(0)^J ⟶ F`, `J` finite, inducing an isomorphism on `H⁰`: the evaluation on a basis
of `H⁰(F)`. -/
theorem exists_sigma_twist_zero_bijective_H_zero (F : (ProjectiveLine (Spec (.of k))).Modules)
    [FiniteDimensional k (F.H 0)] :
    ∃ (J : Type u) (_ : Finite J) (φ : (∐ fun _ : J ↦ 𝒪(0)) ⟶ F),
      Function.Bijective (H.map φ 0) := by
  let b := Module.Basis.ofVectorSpace k (F.H 0)
  let J := Module.Basis.ofVectorSpaceIndex k (F.H 0)
  have : Finite J := Module.Finite.finite_basis b
  have := Fintype.ofFinite J
  let φ : (∐ fun _ : J ↦ 𝒪(0)) ⟶ F :=
    Sigma.desc fun j ↦ homOfSection F (H.zeroLinearEquiv F (b j))
  have hj (j : J) : H.map φ 0 (H.map (Sigma.ι (fun _ : J ↦ 𝒪(0)) j) 0 unitHZero) = b j := by
    rw [← H.map_comp_apply, Sigma.ι_comp_desc, H_map_homOfSection_unitHZero,
      LinearEquiv.symm_apply_apply]
  have hs : Function.Surjective (H.map φ 0) := by
    suffices h : LinearMap.range (H.mapLinearMap k φ 0) = ⊤ from LinearMap.range_eq_top.1 h
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, hj j⟩
  refine ⟨J, inferInstance, φ, ?_, hs⟩
  have := finiteDimensional_H_twist (k := k) 0 0
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_sigma fun _ : J ↦ 𝒪(0)
  have := isFinitePresentation_sigma fun _ : J ↦ 𝒪(0)
  have := finiteDimensional_H_sigma_twist (k := k) (fun _ : J ↦ (0 : ℤ)) 0
  have : HasFiniteBiproducts (ProjectiveLine (Spec (.of k))).Modules :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have hd : Module.finrank k ((∐ fun _ : J ↦ 𝒪(0)).H 0) = Module.finrank k (F.H 0) := by
    rw [Module.finrank_eq_card_basis b]
    have h₁ := finrankH_of_isBilimit k (biproduct.isBilimit fun _ : J ↦ 𝒪(0)) 0
    rw [finrankH_congr k (biproduct.isoCoproduct fun _ : J ↦ 𝒪(0)) 0] at h₁
    simp only [finrankH] at h₁
    rw [h₁, finrank_H_zero_twist_zero, Finset.sum_const, smul_eq_mul, mul_one]
    rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := H.mapLinearMap k φ 0)
    hd).2 hs

end Evaluation

section Resolution

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H⁰(M₂) ⟶ H⁰(M₃)` surjective and
`H¹(M₂) = 0`, also `H¹(M₁) = 0`. -/
lemma subsingleton_H_one_X₁_of_surjective {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hg : Function.Surjective (H.map S.g 0)) [Subsingleton (S.X₂.H 1)] :
    Subsingleton (S.X₁.H 1) := by
  refine ⟨fun x y ↦ ?_⟩
  suffices h : ∀ z : S.X₁.H (0 + 1), z = 0 by rw [h x, h y]
  intro z
  obtain ⟨w, rfl⟩ := (H.ker_map_f_eq_range_δ hS 0).le
    (show H.map S.f (0 + 1) z = 0 from Subsingleton.elim (α := S.X₂.H 1) _ _)
  obtain ⟨v, rfl⟩ := hg w
  exact (H.ker_δ_eq_range_map_g hS 0).ge ⟨v, rfl⟩

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H⁰(M₂) ⟶ H⁰(M₃)` injective,
`H⁰(M₁) = 0`. -/
lemma subsingleton_H_zero_X₁_of_injective {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hg : Function.Injective (H.map S.g 0)) : Subsingleton (S.X₁.H 0) := by
  refine ⟨fun x y ↦ H.injective_map_zero_of_shortExact hS (hg ?_)⟩
  rw [← H.map_comp_apply, ← H.map_comp_apply, S.zero, H.map_zero_apply, H.map_zero_apply]

/-- A finite sum of copies of `𝒪(a)`, twisted by `𝒪(b)`, is a sum of copies of `𝒪(a + b)`. -/
lemma nonempty_sigma_twist_tensorObj_iso {J : Type u} (a b : ℤ) :
    Nonempty ((∐ fun _ : J ↦ 𝒪(a)) ⊗ 𝒪(b) ≅ ∐ fun _ : J ↦ 𝒪(a + b)) := by
  have := isEquivalence_tensorRight_twist (k := k) b
  obtain ⟨e⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2))
    (Spec (.of k)) a b
  exact ⟨PreservesCoproduct.iso (tensorRight (𝒪(b))) (fun _ : J ↦ 𝒪(a)) ≪≫
    Sigma.mapIso fun _ ↦ e⟩

/-- `M ⊗ 𝒪(0) ≅ M`. -/
def tensorTwistZeroIso (M : (ProjectiveLine (Spec (.of k))).Modules) : M ⊗ 𝒪(0) ≅ M :=
  whiskerLeftIso M (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k))).symm ≪≫
    ρ_ M

/-- **Trivial modules on `ℙ¹_k`.** A coherent module `F` on `ℙ¹_k` with
`H⁰(F(-1)) = H¹(F(-1)) = 0` is a finite sum of copies of `𝒪`: the evaluation
`H⁰(F) ⊗ 𝒪 ⟶ F` is an epimorphism by `epi_of_surjective_H_zero`, and its kernel `K` has
`H⁰(K) = H¹(K(-1)) = 0`, so `0 : K ⟶ K` is an epimorphism as well. -/
theorem exists_iso_sigma_twist_zero (F : (ProjectiveLine (Spec (.of k))).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (h0 : Subsingleton ((F ⊗ 𝒪(-1)).H 0))
    (h1 : Subsingleton ((F ⊗ 𝒪(-1)).H 1)) :
    ∃ (J : Type u) (_ : Finite J), Nonempty ((∐ fun _ : J ↦ 𝒪(0)) ≅ F) := by
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := finiteDimensional_H_zero_of_isCoherent F
  obtain ⟨J, _, φ, hφ⟩ := exists_sigma_twist_zero_bijective_H_zero F
  have := isQuasicoherent_sigma fun _ : J ↦ 𝒪(0)
  have := isFinitePresentation_sigma fun _ : J ↦ 𝒪(0)
  have : Epi φ := epi_of_surjective_H_zero φ h1
    ((surjective_H_map_whiskerRight_twist_zero_iff φ 0).2 hφ.2)
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  have := isQuasicoherent_kernel φ
  have := isFinitePresentation_kernel φ
  have hK0 : Subsingleton ((kernel φ).H 0) := subsingleton_H_zero_X₁_of_injective hS hφ.1
  have := isEquivalence_tensorRight_twist (k := k) (-1)
  have hS' := hS.map_of_exact (tensorRight (𝒪(-1)))
  have : Subsingleton ((S.map (tensorRight (𝒪(-1)))).X₂.H 1) := by
    obtain ⟨e⟩ := nonempty_sigma_twist_tensorObj_iso (k := k) (J := J) 0 (-1)
    have := @subsingleton_H_sigma _ _ _ (fun _ : J ↦ 𝒪(0 + -1)) 1
      fun _ ↦ subsingleton_H_one_twist k _ (by omega)
    exact subsingleton_H_of_iso e.symm 1
  have hK1 : Subsingleton ((kernel φ ⊗ 𝒪(-1)).H 1) :=
    subsingleton_H_one_X₁_of_surjective hS' fun _ ↦
      ⟨0, Subsingleton.elim (α := (F ⊗ 𝒪(-1)).H 0) _ _⟩
  have : Epi (0 : kernel φ ⟶ kernel φ) := epi_of_surjective_H_zero _ hK1
    ((surjective_H_map_whiskerRight_twist_zero_iff _ 0).2 fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _ (IsZero.of_epi_zero (kernel φ) _)
  have := isIso_of_mono_of_epi φ
  exact ⟨J, inferInstance, ⟨asIso φ⟩⟩

/-- A short exact sequence transported along isomorphisms of its terms is short exact. -/
lemma shortExact_of_isos {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    {A B C : X.Modules} (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ C) :
    (ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom)
      (by simp)).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ (by simp) (by simp)) hS

/-- **Resolutions of length one by twists on `ℙ¹_k`.** Every coherent module `𝒢` on `ℙ¹_k` has a
resolution `0 → 𝒪(-N - 1)^{J₁} → 𝒪(-N)^{J₀} → 𝒢 → 0`. Choose `N` with `H¹(𝒢(N - 1)) = 0` (Serre
vanishing), let `F = 𝒢(N)` and `K` the kernel of the evaluation `H⁰(F) ⊗ 𝒪 ⟶ F`, an
epimorphism by `epi_of_surjective_H_zero`. Then `H⁰(K) = H¹(K) = 0`, so `K(1)` is trivial by
`exists_iso_sigma_twist_zero`; twist back by `𝒪(-N)`. -/
theorem exists_shortExact_sigma_twist (G : (ProjectiveLine (Spec (.of k))).Modules)
    [G.IsQuasicoherent] [G.IsFinitePresentation] :
    ∃ (J₁ J₀ : Type u) (_ : Finite J₁) (_ : Finite J₀) (d₁ d₀ : ℤ)
      (f : (∐ fun _ : J₁ ↦ 𝒪(d₁)) ⟶ ∐ fun _ : J₀ ↦ 𝒪(d₀)) (g : (∐ fun _ : J₀ ↦ 𝒪(d₀)) ⟶ G)
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨d₀, hd₀⟩ := ProjectiveSpace.exists_subsingleton_H_tensor_twist k G
  have := isQuasicoherent_tensorObj G (𝒪(d₀ + 1))
  have := isFinitePresentation_tensorObj G (𝒪(d₀ + 1))
  have hR : Subsingleton (((G ⊗ 𝒪(d₀ + 1)) ⊗ 𝒪(-1)).H 1) := by
    have := hd₀ d₀ le_rfl 1 one_pos
    exact subsingleton_H_of_iso (nonempty_tensorObj_twist_tensorObj_twist_iso G
      (a := d₀ + 1) (b := -1) (c := d₀) (by omega)).some.symm 1
  have := finiteDimensional_H_zero_of_isCoherent (G ⊗ 𝒪(d₀ + 1))
  obtain ⟨J, _, φ, hφ⟩ := exists_sigma_twist_zero_bijective_H_zero (G ⊗ 𝒪(d₀ + 1))
  have := isQuasicoherent_sigma fun _ : J ↦ 𝒪(0)
  have := isFinitePresentation_sigma fun _ : J ↦ 𝒪(0)
  have : Epi φ := epi_of_surjective_H_zero φ hR
    ((surjective_H_map_whiskerRight_twist_zero_iff φ 0).2 hφ.2)
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact :=
    .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  have := isQuasicoherent_kernel φ
  have := isFinitePresentation_kernel φ
  have hK0 : Subsingleton ((kernel φ).H 0) := subsingleton_H_zero_X₁_of_injective hS hφ.1
  have : Subsingleton (S.X₂.H 1) := by
    exact @subsingleton_H_sigma _ _ _ (fun _ : J ↦ 𝒪(0)) 1
      fun _ ↦ subsingleton_H_one_twist k _ (by omega)
  have hK1 : Subsingleton ((kernel φ).H 1) := subsingleton_H_one_X₁_of_surjective hS hφ.2
  -- `K(1)` is trivial
  have := isQuasicoherent_tensorObj (kernel φ) (𝒪(1))
  have := isFinitePresentation_tensorObj (kernel φ) (𝒪(1))
  let eK : (kernel φ ⊗ 𝒪(1)) ⊗ 𝒪(-1) ≅ kernel φ :=
    (nonempty_tensorObj_twist_tensorObj_twist_iso (kernel φ) (a := 1) (b := -1) (c := 0)
      (by omega)).some ≪≫ tensorTwistZeroIso _
  obtain ⟨J', _, ⟨e⟩⟩ := exists_iso_sigma_twist_zero (kernel φ ⊗ 𝒪(1))
    (subsingleton_H_of_iso eK.symm 0) (subsingleton_H_of_iso eK.symm 1)
  -- twist back by `𝒪(-(d₀ + 1))`
  have := isEquivalence_tensorRight_twist (k := k) (-(d₀ + 1))
  have hS' := hS.map_of_exact (tensorRight (𝒪(-(d₀ + 1))))
  let e₁ : (S.map (tensorRight (𝒪(-(d₀ + 1))))).X₁ ≅ ∐ fun _ : J' ↦ 𝒪(0 + -1 + -(d₀ + 1)) :=
    (tensorRight (𝒪(-(d₀ + 1)))).mapIso (eK.symm ≪≫ (tensorRight (𝒪(-1))).mapIso e.symm ≪≫
      (nonempty_sigma_twist_tensorObj_iso 0 (-1)).some) ≪≫
      (nonempty_sigma_twist_tensorObj_iso (0 + -1) (-(d₀ + 1))).some
  let e₂ : (S.map (tensorRight (𝒪(-(d₀ + 1))))).X₂ ≅ ∐ fun _ : J ↦ 𝒪(0 + -(d₀ + 1)) :=
    (nonempty_sigma_twist_tensorObj_iso 0 (-(d₀ + 1))).some
  let e₃ : (S.map (tensorRight (𝒪(-(d₀ + 1))))).X₃ ≅ G :=
    (nonempty_tensorObj_twist_tensorObj_twist_iso G (a := d₀ + 1) (b := -(d₀ + 1)) (c := 0)
      (by omega)).some ≪≫ tensorTwistZeroIso G
  exact ⟨J', J, inferInstance, inferInstance, _, _, _, _, _, shortExact_of_isos hS' e₁ e₂ e₃⟩

end Resolution

end AlgebraicGeometry.ProjectiveLine
