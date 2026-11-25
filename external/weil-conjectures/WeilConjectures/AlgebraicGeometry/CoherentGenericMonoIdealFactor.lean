/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Factoring an ideal multiple through a generic coherent inclusion

Source: Stacks Project, Tag 01YL, third proof paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent inclusion which is an isomorphism at a point contains an ideal multiple
of its target, for a quasi-coherent ideal with full stalk at that point.

Source: Stacks Project, Tag 01YL, third proof paragraph: the ideal annihilating the
cokernel puts the ideal multiple of the target inside the source.
(blueprint: lem-weil-pbc-coherent-generic-mono-ideal-factor)

Proof: form the coherent cokernel Q of a. Exactness of stalks and surjectivity of a at
ξ make Q_ξ zero. The annihilator ideal J of Q is quasi-coherent on a locally Noetherian
scheme, and its closed zero set is the support of Q. Thus J has full ξ-stalk. Since J
annihilates Q, the composite JG → G → Q vanishes. The kernel universal property and the
canonical isomorphism of the image of the mono a with K give a factor ψ : JG → K whose
composite with a is the product inclusion. For zero Q take the unit annihilator; zero
K and zero G are included. No integral subscheme, finite sum, or generic rank enters
this factorization. -/
theorem coherent_generic_mono_ideal_factor
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K G : X.Modules}
    (hK : RingedSpace.IsCoherent X.toRingedSpace K)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (a : K ⟶ G) [Mono a] (ξ : X)
    (ha : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map a).hom) :
    ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
      Mono ι ∧ J.IsQuasicoherent ∧
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
      ∃ (ψ : idealModuleProduct ι G ⟶ K), ψ ≫ a = idealModuleProductι ι G := by
  classical
  let Q := cokernel a
  let q : G ⟶ Q := cokernel.π a
  have hQ : RingedSpace.IsCoherent X.toRingedSpace Q :=
    ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1 K G a hK hG).2
  obtain ⟨hQqc, hQft⟩ :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X Q).mp hQ
  have : Q.IsQuasicoherent := hQqc
  have : Q.IsFiniteType := hQft
  have : G.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG).1
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace ξ
  have hzero : Subsingleton (Q.presheaf.stalk ξ) := by
    obtain ⟨hepi, _⟩ :=
      (RingedSpace.module_stalk_exact X.toRingedSpace a).2.2.1 ξ
    have hs : Function.Surjective (S.map q).hom :=
      (ModuleCat.epi_iff_surjective _).mp hepi
    have hz (y : S.obj Q) : y = 0 := by
      obtain ⟨g, rfl⟩ := hs y
      obtain ⟨k, rfl⟩ := ha.2 g
      have hh : (S.map a ≫ S.map q) = 0 := by
        rw [← S.map_comp]
        simp [q]
      exact congrArg (fun f ↦ f.hom k) hh
    exact ⟨fun y z ↦ (hz y).trans (hz z).symm⟩
  obtain ⟨J, hJann, _, hJker, _, _, hJsupport, _, _⟩ :=
    schemeTheoreticSupport X Q
  have hfull : Function.Surjective (S.map J.toModulesι).hom := by
    have hsets := (quasi_coherent_ideal_zero_set_affine X J).2.2.2.2
      J.subscheme J.subschemeι hJker
    rw [hJsupport] at hsets
    by_contra hn
    have hh : ξ ∈ {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
      rw [hsets]
      exact hn
    exact hh hzero
  have hprod := ideal_times_quasiCoherent_affine_sections J G
  have hJqc : J.toModules.IsQuasicoherent := by
    simpa only [idealSheafPower] using hprod.2.2.1 1 (by decide)
  have hvanish : idealModuleProductι J.toModulesι G ≫ q = 0 := by
    apply hom_ext
    intro U
    ext s
    change q.app U ((idealModuleProductι J.toModulesι G).app U s) = 0
    apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    have hVU : V ≤ U := hVU
    refine ⟨V, hVU, hxV, ?_⟩
    have hrange := (hprod.2.2.2.1 ⟨V, hV⟩).1
    have hmem : (idealModuleProductι J.toModulesι G).app V
        ((idealModuleProduct J.toModulesι G).presheaf.map (homOfLE hVU).op s) ∈
        J.ideal ⟨V, hV⟩ • (⊤ : Submodule Γ(X, V) Γ(G, V)) := by
      change _ ∈ {t | t ∈ J.ideal ⟨V, hV⟩ • (⊤ : Submodule Γ(X, V) Γ(G, V))}
      rw [← hrange]
      exact ⟨_, rfl⟩
    have hle : J.ideal ⟨V, hV⟩ • (⊤ : Submodule Γ(X, V) Γ(G, V)) ≤
        LinearMap.ker (q.val.app (Opposite.op V)).hom := by
      apply Submodule.smul_le.mpr
      intro r hr t _
      change q.app V (r • t) = 0
      rw [Hom.app_smul]
      rw [hJann] at hr
      exact Module.mem_annihilator.mp hr _
    have hz := hle hmem
    have hn := congrArg (fun f ↦ f s)
      ((idealModuleProductι J.toModulesι G ≫ q).mapPresheaf.naturality
        (homOfLE hVU).op)
    change q.app V ((idealModuleProductι J.toModulesι G).app V
        ((idealModuleProduct J.toModulesι G).presheaf.map (homOfLE hVU).op s)) =
      Q.presheaf.map (homOfLE hVU).op
        (q.app U ((idealModuleProductι J.toModulesι G).app U s)) at hn
    rw [map_zero, ← hn]
    exact hz
  refine ⟨J.toModules, J.toModulesι, inferInstance, hJqc, hfull, ?_⟩
  exact ⟨Abelian.monoLift a (idealModuleProductι J.toModulesι G) hvanish,
    Abelian.monoLift_comp _ _ _⟩

end AlgebraicGeometry.Scheme.Modules
