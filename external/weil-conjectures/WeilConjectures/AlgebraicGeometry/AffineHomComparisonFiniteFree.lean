/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Extending the affine Hom comparison from rank one to finite free modules

Source: Stacks Project, Tag 01HV (4)-(5), finite-basis argument of Tag 0BQZ.
(blueprint: lem-sc-k3-affine-hom-comparison-finite-free). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A natural forward Hom comparison invertible in rank one is invertible
on every finite free source, with arbitrary coefficients.
Source: Stacks Project, Tag 01HV (4)-(5); Tag 0BQZ,
lemma-regular-immersion-ext, finite-free coefficient calculation.
(blueprint: lem-sc-k3-affine-hom-comparison-finite-free).

Proof: Fix N and choose a finite basis b of M. Let i_j:A -> M and
p_j:M -> A be its inclusions and coordinate projections, so sum_j i_j p_j
is the identity of M. Write L(f) for T of precomposition by f and H(f)
for internal Hom precomposition by T(f). Both are additive contravariant
operations, so sum_j L(i_j)L(p_j) and sum_j H(i_j)H(p_j) are identities.
Define the inverse to c(M,N) to be sum_j H(i_j)c(A,N)^(-1)L(p_j).
Naturality moves c(M,N) past H(i_j) in one inverse identity, and moves it
past L(p_j) in the other. Cancel c(A,N) with its inverse, then use the
two sum identities. This argument works for any additive T into the
module sheaves on U, including the associated-sheaf functor transported
by isoSpec. No coefficient freeness is used. For an empty basis the sum
identities are still valid and the inverse is the zero map between zero
objects. The same proof covers the zero ring. -/
theorem affine_hom_comparison_isIso_of_finite_free
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (T : ModuleCat.{u} Γ(Y, U.1) ⥤ U.1.toScheme.Modules)
    (hT : T.Additive)
    (c : ∀ (M N : ModuleCat.{u} Γ(Y, U.1)),
      T.obj (ModuleCat.of Γ(Y, U.1) (M ⟶ N)) ⟶
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.obj M) (T.obj N))
    (hpre : ∀ (M M' N : ModuleCat.{u} Γ(Y, U.1)) (f : M' ⟶ M),
      c M N ≫ SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
        (T.map f) (𝟙 (T.obj N)) =
      T.map (ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1) N f)) ≫ c M' N)
    (hunit : ∀ N : ModuleCat.{u} Γ(Y, U.1),
      IsIso (c (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) N))
    (M N : ModuleCat.{u} Γ(Y, U.1))
    [Module.Free Γ(Y, U.1) M] [Module.Finite Γ(Y, U.1) M] : IsIso (c M N) := by
  classical
  have := hT
  have := hunit N
  let A := Γ(Y, U.1)
  let B := ModuleCat.of A A
  let b := Module.Free.chooseBasis A M
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex A M)
  let inc (i : Module.Free.ChooseBasisIndex A M) : B ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A M (b i))
  let proj (i : Module.Free.ChooseBasisIndex A M) : M ⟶ B := ModuleCat.ofHom (b.coord i)
  have hsplit : ∑ i, proj i ≫ inc i = 𝟙 M := by
    ext m
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    change ∑ i, b.repr m i • b i = m
    exact b.sum_repr m
  let L {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :=
    T.map (ModuleCat.ofHom (Linear.leftComp A N f))
  let H {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :=
    SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
      (T.map f) (𝟙 (T.obj N))
  have hLcomp {P Q S : ModuleCat.{u} A} (f : P ⟶ Q) (g : Q ⟶ S) :
      L g ≫ L f = L (f ≫ g) := by
    dsimp [L]
    rw [← T.map_comp]
    congr 1
  have hHcomp {P Q S : ModuleCat.{u} A} (f : P ⟶ Q) (g : Q ⟶ S) :
      H g ≫ H f = H (f ≫ g) := by
    simp [H, T.map_comp]
  have hLsplit : ∑ i, L (proj i ≫ inc i) = 𝟙 _ := by
    dsimp [L]
    rw [← T.map_sum]
    have heq : (∑ i, ModuleCat.ofHom (Linear.leftComp A N (proj i ≫ inc i))) =
        𝟙 (ModuleCat.of A (M ⟶ N)) := by
      ext h m
      have hm := ConcreteCategory.congr_hom hsplit m
      simpa [ModuleCat.comp_apply, map_sum] using congrArg h hm
    rw [heq, T.map_id]
  have hHsplit : ∑ i, H (proj i ≫ inc i) = 𝟙 _ := by
    let G := (SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj (T.obj N)
    change ∑ i, G.map (T.map (proj i ≫ inc i)).op = 𝟙 _
    rw [← G.map_sum, ← op_sum, ← T.map_sum, hsplit, T.map_id, op_id, G.map_id]
  have hnat {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :
      c Q N ≫ H f = L f ≫ c P N := hpre Q P N f
  let d := ∑ i, H (inc i) ≫ inv (c B N) ≫ L (proj i)
  refine ⟨⟨d, ?_, ?_⟩⟩
  · dsimp [d]
    rw [Preadditive.comp_sum]
    calc
      _ = ∑ i, L (inc i) ≫ L (proj i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Category.assoc, hnat (inc i)]
        simp
      _ = 𝟙 _ := by simpa only [hLcomp] using hLsplit
  · dsimp [d]
    rw [Preadditive.sum_comp]
    calc
      _ = ∑ i, H (inc i) ≫ H (proj i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Category.assoc, Category.assoc, ← hnat (proj i)]
        simp
      _ = 𝟙 _ := by simpa only [hHcomp] using hHsplit

end AlgebraicGeometry
