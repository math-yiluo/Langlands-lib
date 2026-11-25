/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
import WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction
import WeilConjectures.AlgebraicGeometry.TorsionControlledAffineAlgebraization
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationDescent

/-! A bridge from componentwise annihilation to torsion-controlled algebraization.
Source: Stacks Project, Tag 0889(1), after Remark 0888.
(blueprint: new-stage3-torsion-controlled-easy-algebraization-bridge).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine componentwise annihilation condition is sufficient for a
    torsion-controlled coherent algebraization.

Source: Stacks Project, Tag 0889(1), construction after Remark 0888
(blueprint: new-stage3-torsion-controlled-easy-algebraization-bridge).

Proof: apply the affine algebraization construction on a finite affine cover.
Remark 0888 identifies the componentwise annihilation hypothesis with the
annihilation of the inverse-limit kernels and cokernels on each affine. The
finite-module lifting theorem then supplies local maps whose completions agree
with `δ`; formal gluing makes these maps compatible on overlaps. Glue the local
finite modules and maps to obtain `F` and `a`. The local annihilation bounds have
a common positive upper bound, which annihilates the coherent kernel and
cokernel of `a` globally, and the glued completed identifications give `β` and
the stated factorization. -/
theorem torsionControlled_easy_algebraization_bridge
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))) := by
  classical
  obtain ⟨t, ht, hbound⟩ := htorsion
  let U : X.affineOpens → X.Opens := fun i ↦ i.1
  have hcover : (⨆ i, U i) = ⊤ := iSup_affineOpens_eq_top X
  let Hlocal : ∀ i : X.affineOpens, CoherentModules (U i).toScheme := fun i ↦
    ⟨(Scheme.Modules.restrictFunctor (U i).ι).obj H.obj,
      (coherent_module_local_on_open_cover X H.obj X.affineOpens U hcover).1
        H.property (U i)⟩
  have hHlocal (i : X.affineOpens) :
      (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj := rfl
  have hrestricted (i : X.affineOpens) :=
    torsionControlled_formal_restriction J H N δ (U i) (Hlocal i) (hHlocal i) t hbound
  choose γ hγ hγbound using hrestricted
  apply torsionControlled_algebraization_descent J H N δ X.affineOpens U hcover
    Hlocal hHlocal γ hγ
  intro i
  have : TopologicalSpace.NoetherianSpace (U i).toScheme :=
    (Scheme.Hom.isOpenEmbedding (U i).ι).isInducing.noetherianSpace
  let : IsNoetherian (U i).toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let : IsAffine (U i).toScheme := i.2
  let Nlocal := (coherentFormalModulesRestriction J (U i)).obj N
  let δlocal : Nlocal ⟶ (completion (U i).toScheme (J.comap (U i).ι)).obj (Hlocal i) :=
    ObjectProperty.homMk
      (Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom)
  have hlocalbound : ∃ s : ℕ, 1 ≤ s ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
        (kernel (δlocal.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
        (cokernel (δlocal.hom.app (op n)))) := ⟨t, ht, hγbound i⟩
  obtain ⟨F, a, β, hδ, ha⟩ :=
    torsionControlled_affine_algebraization (J.comap (U i).ι) (Hlocal i)
      Nlocal δlocal hlocalbound
  refine ⟨F, a,
    (ObjectProperty.ι (IsCoherentFormalModule (J.comap (U i).ι))).mapIso β, ?_, ha⟩
  exact congrArg (fun f ↦ f.hom) hδ

end AlgebraicGeometry
