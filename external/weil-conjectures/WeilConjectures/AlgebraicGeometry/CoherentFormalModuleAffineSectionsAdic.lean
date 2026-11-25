/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine sections of coherent formal modules form adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, affine reduction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Affine global sections carry a coherent formal system to a tower of finite
A-modules with the algebraic annihilation and transition-kernel conditions.
This statement concerns only finite-level sections, with no inverse limit.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, first paragraph;
Schemes, Tags 01I7 and 01IB.
(blueprint: lem-weil-pbc-coherent-formal-module-affine-sections-adic).

Proof: Spec A is locally Noetherian. Coherence is consequently equivalent to being
quasi-coherent and of finite type; affine sections of a quasi-coherent finite-type
module are finite over A. For each positive power of J, the affine sections formula
for ideal products identifies its product with a quasi-coherent module with
I^(n+1) times its sections. Apply this to the zero product in the formal-system
annihilation condition, obtaining the asserted zero submodule. The same affine
formula says that the quotient projection onto sections of F_(n+1)/J^(n+1)F_(n+1)
is surjective with kernel I^(n+1) times the source sections. The defining quotient
isomorphism of the formal system identifies this quotient with F_n and its quotient
projection with the successor transition. Apply the global-sections functor to this
isomorphism. Its invertible map preserves surjectivity and does not change the kernel.
Finally transport scalars along Γ(Spec A, O) = A; hJ identifies the ideal with I
under this transport, including all its powers. -/
theorem coherentFormalModule_affine_sections_adic (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) :
    let T := F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A)
    (∀ n : ℕ, Module.Finite A (T.obj (op n))) ∧
    (∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥) ∧
    (∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1))))) := by
  let U : (Spec (CommRingCat.of A)).affineOpens := ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  have hqc (n : ℕ) := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    (Spec (CommRingCat.of A)) (F.obj.obj (op n))).mp (F.property.1 n)
  have (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent := (hqc n).1
  have (n : ℕ) : (F.obj.obj (op n)).IsFiniteType := (hqc n).2
  have hI : J.ideal U = I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
    subst J
    exact Scheme.IdealSheafData.ideal_top_ofIdealTop _
  let (M : (Spec (CommRingCat.of A)).Modules) : Module A Γ(M, ⊤) :=
    inferInstanceAs (Module A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj M))
  let : Algebra A Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
  let (M : (Spec (CommRingCat.of A)).Modules) :
      IsScalarTower A Γ(Spec (CommRingCat.of A), ⊤) Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul (fun a s ↦ (Scheme.Modules.smul_top_eq M a s).symm)
  have hscalar (M : (Spec (CommRingCat.of A)).Modules) (n : ℕ) :
      ((J.ideal U ^ n • (⊤ : Submodule Γ(Spec (CommRingCat.of A), ⊤) Γ(M, ⊤))).restrictScalars A) =
        I ^ n • (⊤ : Submodule A Γ(M, ⊤)) := by
    rw [hI, ← Ideal.map_pow]
    exact Submodule.restrictScalars_map_smul_eq (I ^ n) ⊤
  have hpqc (n : ℕ) : (Scheme.idealSheafPower J.toModulesι (n + 1)).1.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
      (F.obj.obj (op n))).2.2.1 _ (by omega)
  have hr (n : ℕ) (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
      Set.range ((Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 M).app ⊤) =
        {s | s ∈ I ^ (n + 1) • (⊤ : Submodule A Γ(M, ⊤))} := by
    have := hpqc n
    have hpow := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J M).2.2.2.1
      U).2.2.2 (n + 1) (by omega)
    have heq : (LinearMap.range
        ((Scheme.idealSheafPower J.toModulesι (n + 1)).2.val.app (op ⊤)).hom :
          Ideal Γ(Spec (CommRingCat.of A), ⊤)) = J.ideal U ^ (n + 1) := SetLike.coe_injective hpow
    have hh := Scheme.Modules.multiplication_range
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 M U
    dsimp only at hh
    rw [heq] at hh
    exact hh.trans (congrArg (fun P : Submodule A Γ(M, ⊤) ↦ (P : Set Γ(M, ⊤)))
      (hscalar M (n + 1)))
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hf := Scheme.Modules.finite_sections_of_finiteType (F.obj.obj (op n))
      (isAffineOpen_top (Spec (CommRingCat.of A)))
    let := hf
    exact Scheme.Modules.finite_sections_top_of_finite (F.obj.obj (op n))
  · intro n
    apply le_antisymm _ bot_le
    intro s hs
    obtain ⟨t, rfl⟩ := (Set.ext_iff.mp (hr n (F.obj.obj (op n))) s).mpr hs
    have hz : Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (F.obj.obj (op n)) = 0 :=
      (F.property.2.1 n).eq_of_src _ _
    simp [hz]
  · intro n
    let M := F.obj.obj (op (n + 1))
    have := hpqc n
    have := Scheme.Modules.product_qc (Scheme.idealSheafPower J.toModulesι (n + 1)).2 M
    have hq := (Scheme.Modules.quasiCoherent_cokernel_image
      (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 M)).2.2.2.2.2.2.2.2 U
    obtain ⟨e, he⟩ := F.property.2.2 n
    constructor
    · change Function.Surjective ((F.obj.map (homOfLE (Nat.le_succ n)).op).app ⊤)
      rw [← he]
      exact (Scheme.Modules.appLinearEquivOfIso e ⊤).surjective.comp hq.2.1
    · ext s
      change (F.obj.map (homOfLE (Nat.le_succ n)).op).app ⊤ s = 0 ↔ _
      rw [← he]
      change (Scheme.Modules.appLinearEquivOfIso e ⊤)
        ((formalModuleQuotientπ J (n + 1) M).app ⊤ s) = 0 ↔ _
      rw [(Scheme.Modules.appLinearEquivOfIso e ⊤).map_eq_zero_iff]
      change s ∈ LinearMap.ker
        ((cokernel.π (Scheme.idealModuleProductι
          (Scheme.idealSheafPower J.toModulesι (n + 1)).2 M)).val.app (op ⊤)).hom ↔ _
      rw [hq.2.2.1]
      exact Set.ext_iff.mp (hr n M) s

end

end AlgebraicGeometry
