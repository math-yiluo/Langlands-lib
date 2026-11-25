/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.DeterminantExteriorDualIso
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExact

/-! # Ordinary determinant evaluation

Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-determinant-dual-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The top exterior powers of a finite locally free sheaf and its internal dual
are tensor inverses in the ordinary category of sheaves of modules.
Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-determinant-dual-evaluation).

Proof: trivialize M as the free sheaf of rank d on an open cover. Internal Hom
into the structure sheaf restricts to the dual free module. The determinant pairing
of exterior powers takes the wedge of the dual basis and the wedge of the basis to
1. These top exterior powers are free of rank one, so the pairing is an isomorphism
locally. Under a change of basis the two generators scale by inverse determinants;
hence the pairing is independent of the trivialization. The sectionwise determinant
pairings commute with restrictions and descend through sheafification and the
sheaf tensor product. The local inverses agree on overlaps by uniqueness of the
inverse and glue to a global inverse. For d=0 the empty wedges give the structure
sheaf and the pairing is multiplication. On the empty scheme all maps involved
are the unique isomorphisms. -/
theorem determinant_dual_evaluation (X : Scheme.{u})
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    let L : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorPower
        (SheafOfModules.homObj (R := X.sheaf) M
          (SheafOfModules.unit X.ringCatSheaf)) d
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      Scheme.Modules.exteriorPower M d
    Nonempty (L ⊗ F ≅ 𝟙_ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let Z : X.Modules := SheafOfModules.free (ULift.{u} (Fin 0))
  have hZ : CategoryTheory.Limits.IsZero Z := by
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero Z).2
    apply (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf)
      (ULift.{u} (Fin 0))).hom_ext
    intro j
    exact Fin.elim0 j.as.down
  let S : ShortComplex X.Modules := ShortComplex.mk
    (0 : Z ⟶ M) (𝟙 M) (by simp)
  have hS : S.ShortExact :=
    (ShortComplex.Splitting.ofIsZeroOfIsIso S hZ (inferInstance : IsIso S.g)).shortExact
  have : M.IsFiniteLocallyFreeOfRank d := hfree
  let F := Scheme.Modules.exteriorPower M d
  have : F.IsInvertible :=
    (Scheme.Modules.determinant_shortExact S hS 0 d d (by omega)).2.1
  obtain ⟨e⟩ := exteriorSheaf_dual_iso X M d hfree
  let := SheafOfModules.symmetricCategory X.sheaf
  exact ⟨(e ⊗ᵢ Iso.refl F) ≪≫ (β_ _ _) ≪≫
    (Scheme.Modules.nonempty_tensorObj_dual_iso_unit F).some⟩

end AlgebraicGeometry
