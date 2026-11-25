/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairing
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal

/-! Intermediate determinant facts for the ordinary determinant evaluation.
Source: Stacks Project, Tag 0BRT. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Exterior powers commute with the internal dual in top degree.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.pairingDual` on each trivializing open.
(blueprint: lem-sc-determinant-dual-evaluation-dual-identification).

Proof: choose an open cover trivializing `M` with a basis of `d` sections.
On each subopen of a trivializing open, sections of `M` form a free module of
rank `d`, and internal dual sections identify with its ring-linear dual: evaluate
at that subopen and reconstruct the internal map using the basis coordinates.
Exterior sheafification commutes with restriction because the localized site's
covers are exactly the covers of the corresponding opens. The finite free exterior
power has the basis of increasing wedges (Mathlib `Basis.exteriorPower`), so its
presheaf on this open is already a sheaf, with rank-one generator the top wedge.
Mathlib `exteriorPower.pairingDual` sends the wedge of the dual basis to the
functional taking the top basis wedge to one, and is bijective by
`exteriorPower.bijective_pairingDual`. The determinant formula is compatible with
ring restriction and restriction of internal Hom sections. Therefore these local
maps to the internal dual of the exterior sheaf agree on overlaps and glue.
Their inverses agree by uniqueness of inverses, proving the glued map is an
isomorphism. Changing the local basis scales the top wedge and its dual by inverse
determinants, so the construction is independent of the cover. For `d = 0`, empty
wedges identify both sides with the structure sheaf. The empty scheme has no
points to check and its module category is trivial. No nontriviality assumption
on the section rings is needed. -/
theorem exteriorSheaf_dual_iso (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((Scheme.Modules.exteriorPower
      (SheafOfModules.homObj (R := X.sheaf) M
        (SheafOfModules.unit X.ringCatSheaf)) d) ≅
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M d)) := by
  obtain ⟨f, hf⟩ := exterior_dual_pairing_exists X M d
  obtain ⟨I, U, hU, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}
      (M := M) (r := d)).mp hfree
  have hb (V : X.Opens) (i : I) (g : V ⟶ U i) :
      Function.Bijective (f.val.app (Opposite.op V)) :=
    exterior_dual_pairing_app_bijective X M d f hf (U i) d (e i).some V g
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨Presheaf.isLocallyInjective_of_coversTop hU _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop hU _ fun V i g ↦ (hb V i g).2⟩
  let : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have : IsIso f :=
    isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  exact ⟨asIso f⟩

end AlgebraicGeometry
