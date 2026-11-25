/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.FormalGraphFirstQuotientEpi
import WeilConjectures.AlgebraicGeometry.FiniteKernelPullbackCokernelAnnihilated
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine

/-! # The finite graph of a prescribed formal comparison map

Source: Stacks Project, Tag 0889(1), formal gluing of comparison morphisms.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The discrepancy between the second projection and the prescribed formal map
at level n+1, on the pullback of the two comparison arrows. -/
noncomputable def torsionControlledGraphError
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    pullback a.hom a'.hom ⟶ formalModuleQuotient J (n + 1) F'.obj :=
  let t : formalModuleQuotient J (n + 1) F.obj ⟶
      formalModuleQuotient J (n + 1) F'.obj := θ.hom.app (op n)
  pullback.snd a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj -
    pullback.fst a.hom a'.hom ≫ formalModuleQuotientπ J (n + 1) F.obj ≫ t

/-- The graph is a real kernel, retaining the chosen component of θ. -/
noncomputable def torsionControlledGraph
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) : X.Modules :=
  kernel (torsionControlledGraphError J a a' θ n)

/-- First projection from the finite graph. -/
noncomputable def torsionControlledGraphFst
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    torsionControlledGraph J a a' θ n ⟶ F.obj :=
  kernel.ι (torsionControlledGraphError J a a' θ n) ≫ pullback.fst a.hom a'.hom

/-- Second projection from the finite graph. -/
noncomputable def torsionControlledGraphSnd
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ) :
    torsionControlledGraph J a a' θ n ⟶ F'.obj :=
  kernel.ι (torsionControlledGraphError J a a' θ n) ≫ pullback.snd a.hom a'.hom

set_option backward.isDefEq.respectTransparency false in
private theorem isZero_of_first_quotient_and_power {X : Scheme.{u}}
    (J : X.IdealSheafData) (C : X.Modules) (s : ℕ) (hs : 1 ≤ s)
    (hq : formalModuleQuotientπ J 1 C = 0)
    (hp : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι s).2 C)) : IsZero C := by
  have hstalk (x : X) : IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj C)
      := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨e, he, hinj, hpinj, hr, hquot, hpow⟩ :=
      Scheme.ideal_module_product_stalk J.toModulesι C x
    let I : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
    have hI : I • (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) = ⊤ := by
      obtain ⟨_, _, φ, hφ⟩ := hpow 1 le_rfl
      apply top_unique
      intro y _
      have hy : (Submodule.Quotient.mk y :
          S.obj C ⧸ I ^ 1 • (⊤ : Submodule (X.presheaf.stalk x) (S.obj C))) = 0 := by
        apply φ.injective
        rw [hφ]
        change (S.map (formalModuleQuotientπ J 1 C)).hom y = φ 0
        rw [hq, S.map_zero]
        simp
      simpa using (Submodule.Quotient.mk_eq_zero _).mp hy
    have hb : I ^ s • (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) = ⊥ := by
      obtain ⟨_, hrange, _⟩ := hpow s hs
      have hz : S.map (Scheme.idealModuleProductι
          (Scheme.idealSheafPower J.toModulesι s).2 C) = 0 := by
        rw [hp.eq_zero_of_src (Scheme.idealModuleProductι
          (Scheme.idealSheafPower J.toModulesι s).2 C), S.map_zero]
      rw [← hrange, hz]
      exact LinearMap.range_zero
    have htop (k : ℕ) :
        I ^ k • (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) = ⊤ := by
      induction k with
      | zero => simp [Ideal.one_eq_top]
      | succ k ih => rw [pow_succ, Submodule.mul_smul, hI, ih]
    have htb : (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) = ⊥ :=
      (htop s).symm.trans hb
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun y z ↦ by
      have hy : y = 0 := by simpa only [htb, Submodule.mem_bot] using (show y ∈
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) from Submodule.mem_top)
      have hz : z = 0 := by simpa only [htb, Submodule.mem_bot] using (show z ∈
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj C)) from Submodule.mem_top)
      exact hy.trans hz.symm⟩
  apply (IsZero.iff_id_eq_zero C).mpr
  ext U t
  change t = 0
  apply TopCat.Presheaf.section_ext ⟨C.presheaf, C.isSheaf⟩ U t 0
  intro x hx
  have ht : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj C) :=
    ModuleCat.subsingleton_of_isZero (hstalk x)
  exact ht.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem epi_of_first_quotient_and_power_cokernel {X : Scheme.{u}}
    (J : X.IdealSheafData) {E F : X.Modules} (f : E ⟶ F)
    (s : ℕ) (hs : 1 ≤ s)
    (hq : Epi (f ≫ formalModuleQuotientπ J 1 F))
    (hp : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι s).2 (cokernel f))) : Epi f := by
  have : Epi (formalModuleQuotientπ J 1 F) := inferInstanceAs (Epi (cokernel.π _))
  let c := cokernel.π f
  let q := formalModuleQuotientMap J c (Nat.le_refl 1)
  have hqfac : formalModuleQuotientπ J 1 F ≫ q =
      c ≫ formalModuleQuotientπ J 1 (cokernel f) := by
    simp [q, formalModuleQuotientMap, formalModuleQuotientπ]
  have hqzero : q = 0 := by
    apply (cancel_epi (f ≫ formalModuleQuotientπ J 1 F)).mp
    rw [Category.assoc, hqfac, ← Category.assoc]
    simp [c]
  have hcq : formalModuleQuotientπ J 1 (cokernel f) = 0 := by
    apply (cancel_epi c).mp
    rw [← hqfac, hqzero]
    simp
  exact (Preadditive.epi_iff_isZero_cokernel f).mpr
    (isZero_of_first_quotient_and_power J (cokernel f) s hs hcq hp)

/-- The finite graph surjects onto F at every positive depth.
Source: Stacks Project, Tag 0889(1), affine comparison argument using Tag 05EK.
Proof: work on an affine open Spec(A), where all coherent sheaves give finite modules.
The graph is the kernel of the displayed discrepancy on F ×_H F'. Complete over A.
Completion is flat and exact for finite modules over the Noetherian ring A, so the
completed graph is this same kernel in the completed pullback. The map
x ↦ (x, θ(x)) lies in that kernel, by hθ and its level n+1 component; thus the
completed first projection is surjective. At a prime containing J, Nakayama applied
to its finite cokernel makes the original projection surjective. At a prime not
containing J, the power-torsion kernel and cokernel of a' vanish, so a' is an
isomorphism, the quotient at level n+1 is zero, and the graph projection is an
isomorphism. These two cases cover Spec(A). Local surjectivity is epimorphy of
sheaves, giving the global assertion. The zero ideal makes the graph the usual
graph of θ; the unit ideal makes a' an isomorphism. Zero modules and the empty
scheme cause no exception.
(blueprint: lem-weil-pbc-torsion-controlled-finite-graph-epi). -/
theorem torsionControlledGraphFst_epi
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) : Epi (torsionControlledGraphFst J a a' θ n) := by
  obtain ⟨s, hs, _, hc⟩ := ha'
  have hq : Epi (torsionControlledGraphFst J a a' θ n ≫ formalModuleQuotientπ J 1 F.obj) :=
    formalGraph_first_quotient_epi J a a' θ hθ n
  have hp : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (s + n + 1)).2
        (cokernel (torsionControlledGraphFst J a a' θ n))) :=
    finiteKernelPullback_cokernel_annihilated J a.hom a'.hom s hs hc n
      (torsionControlledGraphError J a a' θ n)
  exact epi_of_first_quotient_and_power_cokernel J _ (s + n + 1) (by omega) hq hp

end AlgebraicGeometry
