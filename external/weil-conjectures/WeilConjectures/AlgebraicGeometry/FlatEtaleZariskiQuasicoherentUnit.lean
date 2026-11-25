/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! Quasi-coherent sheafification units in the tensor-section comparison.
Source: Descent 03FH and 03DX (blueprint: lem-fd-etale-zariski-ringed-pullback-flat).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A presheaf of étale modules identified with tensor sections of a quasi-coherent
Zariski module is fixed by module sheafification.
Source: Stacks, Descent, Tags 03DR and 03FH
(blueprint: lem-fd-etale-zariski-quasicoherent-unit).

Proof: quasi-coherent étale descent says that the tensor-section presheaf is a sheaf.
Transport this property through `p`. Under the faithful module-to-abelian-presheaf
functor the module-sheafification unit is the ordinary sheafification unit, which is
an isomorphism on a sheaf. That functor reflects isomorphisms, giving the result. -/
theorem zariski_etale_quasicoherent_unit (T : Scheme.{u})
    (P : T.Modules ⥤ _root_.PresheafOfModules.{u} (smallEtaleModuleRing T).obj)
    (p : ∀ M : T.Modules,
      (P.obj M).presheaf ≅ etaleTensorSectionsPresheaf M) :
    ∀ (M : T.Modules) [M.IsQuasicoherent],
      IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (smallEtaleModuleRing T).obj)).unit.app (P.obj M)) := by
  intro M hM
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  apply isIso_toSheafify
  exact (Presheaf.isSheaf_of_iso_iff (p M)).mpr
    (isSheaf_etaleTensorSectionsPresheaf M)

end AlgebraicGeometry.Scheme.Modules
