/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Etale.EtaleLocalIsoCoverFromProEtaleSection
import WeilConjectures.ConstructibleSheaf.InternalHom

/-! # Etale representatives of pro-etale derived Isom sections

## References

* Stacks Project, Tag 09B1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Pro-etale local sections of the derived Isom presheaf with bounded-below target admit
etale representatives at every geometric point.
-/
theorem exists_etale_local_representative_of_proetale_local_iso_sections
    (X : Scheme.{u}) (U : X.ProEt)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hD : DerivedCategory.TStructure.t.plus D)
    (hsections : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left) B
          ((derivedComparison U.left B).obj A)
          ((derivedComparison U.left B).obj D)).obj
            (op ((toProEt U.left).obj V)))) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((localIsomorphismRestriction U.left B V).obj A ≅
          (localIsomorphismRestriction U.left B V).obj D) := by
  intro Ω instΩ instSep x
  obtain ⟨V, v, s⟩ := hsections Ω x
  obtain ⟨𝒰, h𝒰⟩ := exists_etale_iso_cover_of_proetale_local_iso_section
    U.left V A D hD (Classical.choice s)
  obtain ⟨i, t, ht⟩ := _root_.AlgebraicGeometry.Scheme.Cover.exists_comp_eq_of_isSepClosed 𝒰 v.left
  let W : U.left.Etale := Etale.mk (𝒰.f i ≫ V.hom)
  let w : (pointSmallEtale x).fiber.obj W :=
    Over.homMk t (by
      change t ≫ (𝒰.f i ≫ V.hom) = x
      rw [← Category.assoc, ht]
      exact v.w)
  exact ⟨W, w, h𝒰 i⟩

end AlgebraicGeometry.Scheme
