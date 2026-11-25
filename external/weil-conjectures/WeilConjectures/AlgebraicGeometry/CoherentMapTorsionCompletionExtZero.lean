/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentArtinRees
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # A torsion kernel embeds in a sufficiently deep ideal quotient

Source: Stacks Project, Tags 0889 and 088A, uniqueness argument, via Artin--Rees.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A power-torsion kernel embeds into a sufficiently deep ideal quotient.
Source: Stacks Project, Tags 0889 and 088A, uniqueness argument.
Proof: on an affine open, Artin--Rees for the finite submodule T = ker b
of Q gives T intersect K^n Q contained in K^(n-c) T for n at least c.
Choose n at least c+t so that this intersection is zero. Thus the restriction
of Q -> Q/K^n Q to T is injective. A finite affine cover exists because X
is Noetherian; take the maximum of the finitely many bounds. Injectivity is
local on that cover, giving the stated monomorphism. Increasing n to a
positive exponent handles the zero module and unit or zero ideal cases.
(blueprint: lem-weil-pbc-coherent-map-torsion-completion-ext-zero)
-/
theorem coherentMap_torsion_completion_ext_zero
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ t : ℕ, 1 ≤ t ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel b.hom))) :
    ∃ n : ℕ, Mono (kernel.ι b.hom ≫ formalModuleQuotientπ K (n + 1) Q.obj) := by
  obtain ⟨t, ht, hz⟩ := hker
  have hcoh := ((Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule X).1
    Q.obj R.obj Q.property R.property).1 b.hom |>.1
  have hqc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X (kernel b.hom)).mp hcoh |>.1
  obtain ⟨c, hc⟩ := Scheme.coherent_artin_rees Q.obj (kernel b.hom) Q.property
    (kernel.ι b.hom) hqc K
  refine ⟨c + t - 1, ?_⟩
  have he : c + t - 1 + 1 = c + t := by omega
  rw [he]
  let g := kernel.ι b.hom
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (c + t)).2 Q.obj
  have : Mono i := by
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    dsimp [i, Scheme.idealModuleProductι]
    infer_instance
  let f := g ≫ formalModuleQuotientπ K (c + t) Q.obj
  let k := kernel.ι f
  have hw : (k ≫ g) ≫ cokernel.π i = 0 := by
    simpa only [f, k, formalModuleQuotientπ, Category.assoc] using kernel.condition f
  let l := Abelian.monoLift i (k ≫ g) hw
  have hl : l ≫ i = k ≫ g := Abelian.monoLift_comp i (k ≫ g) hw
  have hz' : Scheme.idealModuleProductι
      (Scheme.idealSheafPower K.toModulesι t).2 (kernel b.hom) ≫ g = 0 := by
    rw [hz.eq_zero_of_src
      (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2
        (kernel b.hom)), zero_comp]
  have hkg : k ≫ g = 0 := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    have hs : (k ≫ g).app W s ∈ Set.range (i.app W) ∩
        Set.range (g.app W) := by
      constructor
      · refine ⟨l.app W s, ?_⟩
        exact congrArg (fun a ↦ a.app W s) hl
      · exact ⟨k.app W s, rfl⟩
    have hb := (hc (c + t) (by omega) W).2 hs
    have hsub : c + t - c = t := by omega
    rw [hsub, hz'] at hb
    obtain ⟨z, hz⟩ := hb
    simpa using hz.symm
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply (cancel_mono g).1
  simpa only [zero_comp] using hkg

end AlgebraicGeometry
