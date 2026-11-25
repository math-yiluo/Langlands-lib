/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Finite adic sections on affine opens

Source: Stacks Project, Lemma 087W, first paragraph, and Lemma 087X (2).
(blueprint: lem-weil-pbc-formal-module-affine-open-sections-adic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections on an affine open form a finite adic tower. This concerns only individual
levels and successor transitions, and asserts nothing about an inverse limit.

Source: Stacks Project, Lemma 087W, first paragraph, and Lemma 087X (2);
Schemes, Tags 01I7 and 01IB.
(blueprint: lem-weil-pbc-formal-module-affine-open-sections-adic).

Proof: On the locally Noetherian scheme X, coherence implies quasi-coherence and
finite type. The affine finite-type section criterion makes each level finite on V.
The affine ideal-product theorem identifies the sections of the positive ideal power
with I(V)^(n+1). Its multiplication-range formula then identifies the range of the
power-product inclusion into each level with I(V)^(n+1) times that level's sections.
For level n the product is a zero object, so this range is zero. For level n+1,
the affine cokernel theorem makes the quotient projection surjective with kernel
equal to that range. The defining quotient isomorphism identifies the successor
transition with this projection followed by an invertible section map. Surjectivity
and the kernel formula follow; no restriction of the tower or inverse limit is needed. -/
theorem coherentFormalModule_affine_open_sections_adic
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModule X I) (V : X.affineOpens) :
    let T := F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)
    (∀ n : ℕ, Module.Finite Γ(X, V.1) (T.obj (op n))) ∧
    (∀ n : ℕ, I.ideal V ^ (n + 1) •
      (⊤ : Submodule Γ(X, V.1) (T.obj (op n))) = ⊥) ∧
    (∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I.ideal V ^ (n + 1) •
          (⊤ : Submodule Γ(X, V.1) (T.obj (op (n + 1))))) := by
  have hcoh (n : ℕ) := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X (F.obj.obj (op n))).mp (F.property.1 n)
  have hqc (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent := (hcoh n).1
  have hft (n : ℕ) : (F.obj.obj (op n)).IsFiniteType := (hcoh n).2
  have hr (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
      LinearMap.range ((Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2 M).val.app (op V.1)).hom =
      I.ideal V ^ (n + 1) • (⊤ : Submodule Γ(X, V.1) Γ(M, V.1)) := by
    have hp := Scheme.Modules.ideal_times_quasiCoherent_affine_sections I M
    have := hp.2.2.1 (n + 1) (by omega)
    have hI : (LinearMap.range
        ((Scheme.idealSheafPower I.toModulesι (n + 1)).2.val.app (op V.1)).hom :
        Ideal Γ(X, V.1)) = I.ideal V ^ (n + 1) := by
      exact SetLike.coe_injective ((hp.2.2.2.1 V).2.2.2 (n + 1) (by omega))
    apply SetLike.coe_injective
    exact hI ▸ Scheme.Modules.multiplication_range _ M V
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have := hft n
    exact Scheme.Modules.finite_sections_of_finiteType (F.obj.obj (op n)) V.2
  · intro n
    rw [← hr n (F.obj.obj (op n))]
    have hz := (F.property.2.1 n).eq_zero_of_src
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
        (F.obj.obj (op n)))
    rw [hz]
    change LinearMap.range (0 : Γ(Scheme.idealModuleProduct
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj.obj (op n)), V.1) →ₗ[Γ(X, V.1)]
      Γ(F.obj.obj (op n), V.1)) = ⊥
    exact LinearMap.range_zero
  · intro n
    let M := F.obj.obj (op (n + 1))
    let i := (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    have := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections I M).2.2.1 (n + 1) (by omega)
    have := Scheme.Modules.product_qc i M
    obtain ⟨e, he⟩ := F.property.2.2 n
    have hπ := (Scheme.Modules.quasiCoherent_cokernel_image
      (Scheme.idealModuleProductι i M)).2.2.2.2.2.2.2.2 V
    have ht (s : Γ(M, V.1)) :
        (F.obj.map (homOfLE (Nat.le_succ n)).op).app V.1 s =
          e.hom.app V.1 ((formalModuleQuotientπ I (n + 1) M).app V.1 s) :=
      (congrArg (fun f ↦ f.app V.1 s) he).symm
    refine ⟨?_, ?_⟩
    · intro s
      obtain ⟨t, ht'⟩ := (Scheme.Modules.appLinearEquivOfIso e V.1).surjective s
      obtain ⟨v, hv⟩ := hπ.2.1 t
      change (formalModuleQuotientπ I (n + 1) M).app V.1 v = t at hv
      exact ⟨v, (ht v).trans ((congrArg (e.hom.app V.1) hv).trans ht')⟩
    · change LinearMap.ker ((F.obj.map (homOfLE (Nat.le_succ n)).op).val.app
        (op V.1)).hom = _
      rw [← hr n M, ← hπ.2.2.1]
      ext s
      change (F.obj.map (homOfLE (Nat.le_succ n)).op).app V.1 s = 0 ↔
        (formalModuleQuotientπ I (n + 1) M).app V.1 s = 0
      rw [ht]
      exact (Scheme.Modules.appLinearEquivOfIso e V.1).map_eq_zero_iff

end AlgebraicGeometry
