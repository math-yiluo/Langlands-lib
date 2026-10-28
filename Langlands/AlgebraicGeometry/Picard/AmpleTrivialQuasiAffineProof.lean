import Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Quasi-affineness from an ample trivial line bundle -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- A global function trivializes the structure module on an open precisely when the
open lies in the function's basic open. -/
theorem trivializesOn_structureModule_iff (r : Γ(X, ⊤)) (U : X.Opens) :
    TrivializesOn (structureModule X) r U ↔ U ≤ X.basicOpen r := by
  constructor
  · intro h
    have h' : IsIso ((sectionHom (structureModule X) r).app (U.ι ''ᵁ ⊤)) :=
      Scheme.Modules.Hom.isIso_iff_isIso_app.mp h ⊤
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
      ((sectionHom (structureModule X) r).app (U.ι ''ᵁ ⊤))).surjective
        (1 : Γ(X, U.ι ''ᵁ ⊤))
    change (structureMulHom r).app (U.ι ''ᵁ ⊤) a = (1 : Γ(X, U.ι ''ᵁ ⊤)) at ha
    rw [structureMulHom_app, mul_comm] at ha
    have hu : IsUnit (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op r) :=
      IsUnit.of_mul_eq_one _ ha
    have hb := X.basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_res, Scheme.Opens.ι_image_top] at hb
    rw [← hb]
    exact inf_le_right
  · intro h
    apply unitEnd_restrict_isIso
    have hres : unitEndCoefficient (sectionHom (structureModule X) r) U =
        X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r := by
      change (structureMulHom r).app U (1 : Γ(X, U)) = _
      rw [structureMulHom_app, one_mul]
    have hcomp : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r =
        X.presheaf.map (homOfLE h).op
          (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [hres, hcomp]
    exact (X.toRingedSpace.isUnit_res_basicOpen r).map (X.presheaf.map (homOfLE h).op).hom

/-- The whole trivialization open of a global function on the structure module is its
basic open. -/
theorem trivializationOpen_structureModule (r : Γ(X, ⊤)) :
    trivializationOpen (structureModule X) r = X.basicOpen r := by
  apply le_antisymm
  · exact sSup_le fun U hU ↦ (trivializesOn_structureModule_iff r U).mp hU
  · exact le_sSup ((trivializesOn_structureModule_iff r _).mpr le_rfl)

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Every actual tensor power of the structure sheaf is isomorphic to the structure sheaf,
by repeatedly applying the left unitor. -/
noncomputable def tensorPowStructureSheafIso (X : Scheme.{u}) :
    (n : ℕ) → tensorPow (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => (tensorFunctor X).mapIso ((Iso.refl _).prod (tensorPowStructureSheafIso X n)) ≪≫
      tensorLeftUnitor (structureSheaf X)

/-- A scheme with an ample line bundle isomorphic to its structure sheaf is quasi-affine. -/
theorem ampleTrivialQuasiAffine : AmpleTrivialQuasiAffineStatement.{u} := by
  intro X L hL ⟨e⟩
  have := hL.compactSpace
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x ↦ ?_
  obtain ⟨n, -, s, hx, ha⟩ := hL.exists_section x
  let φ : tensorPow L.obj n ≅ structureModule X :=
    tensorPowIso e n ≪≫ tensorPowStructureSheafIso X n
  have h : L.sectionOpen s = X.basicOpen (φ.hom.app ⊤ s) := by
    rw [← trivializationOpen_structureModule, trivializationOpen_mapIso]
  exact ⟨φ.hom.app ⊤ s, h ▸ ha, h ▸ hx⟩

end Langlands.AlgebraicGeometry.Picard
