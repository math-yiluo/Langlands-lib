/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.RingHom.Injective
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Injectivity of finite normal stalk maps with dense etale locus

## References

* Stacks Project, Tags 0357 and 01UA
* Stacks Project, Tag 0357 (open integral normal components)
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Topology
namespace AlgebraicGeometry.Scheme

private theorem stalkMap_injective_of_integral_dense_flat {X Y : Scheme.{u}}
    [IsIntegral Y] (f : X ⟶ Y) (D : Set X) (hdense : Dense D)
    (hflat : ∀ z ∈ D, (f.stalkMap z).hom.Flat) (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro r hr
  change (f.stalkMap x).hom r = 0 at hr
  obtain ⟨U, hxU, s, rfl⟩ := Y.presheaf.exists_germ_eq r
  rw [f.germ_stalkMap_apply] at hr
  have he : X.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U s) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hxU 0 := by simpa using hr
  obtain ⟨W, hxW, i, j, hij⟩ := X.presheaf.germ_eq x hxU hxU _ _ he
  obtain ⟨z, hzW, hzD⟩ := hdense.inter_open_nonempty (W : Set X) W.isOpen ⟨x, hxW⟩
  have hzU : f z ∈ U := i.le hzW
  have hz : X.presheaf.germ (f ⁻¹ᵁ U) z hzU (f.app U s) = 0 := by
    rw [← X.presheaf.germ_res_apply i z hzW, hij]
    simp
  let : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) :=
    (f.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := hflat z hzD
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f z)) (X.presheaf.stalk z)) := by
    change IsLocalHom (f.stalkMap z).hom
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (f.stalkMap z).hom :=
    FaithfulSMul.algebraMap_injective _ _
  have hs : s = 0 := germ_injective_of_isIntegral Y (f z) hzU
    (hinj (by simpa using hz))
  simp [hs]

/-- If the target has domain stalks and is locally Noetherian, a morphism
that is etale over an open with dense source preimage has injective stalk maps. -/
theorem dense_etale_stalkMap_injective_of_domain_stalks {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (V : Y.Opens) (hdense : Dense (↑(f ⁻¹ᵁ V) : Set X))
    (hetale : Etale (f ∣_ V)) (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have : Etale (f ∣_ V) := hetale
  let C : Y.Opens := ⟨connectedComponent (f x), isOpen_connectedComponent⟩
  have hC (y : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk y) := by
    let : IsDomain (Y.presheaf.stalk (C.ι y)) := hY (C.ι y)
    exact (asIso (C.ι.stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain
  let : ConnectedSpace C.toScheme := isConnected_iff_connectedSpace.mp
    (isConnected_connectedComponent (x := f x))
  let : IrreducibleSpace C.toScheme :=
    irreducibleSpace_of_isDomain_stalk C.toScheme hC
  let (y : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk y) := hC y
  have : IsReduced C.toScheme := isReduced_of_isReduced_stalk _
  have : IsIntegral C.toScheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  let D : Set (f ⁻¹ᵁ C).toScheme :=
    (f ⁻¹ᵁ C).ι ⁻¹' (↑(f ⁻¹ᵁ V) : Set X)
  have hD : Dense D := hdense.preimage (f ⁻¹ᵁ C).isOpen.isOpenMap_subtype_val
  have hflat (z : (f ⁻¹ᵁ C).toScheme) (hz : z ∈ D) :
      ((f ∣_ C).stalkMap z).hom.Flat := by
    let zV : (f ⁻¹ᵁ V).toScheme := ⟨z.1, hz⟩
    have hzflat : (f.stalkMap z.1).hom.Flat :=
      (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (morphismRestrictStalkMap f V zV)).mp (Flat.stalkMap (f ∣_ V) zV)
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f C z)).mpr hzflat
  let xC : (f ⁻¹ᵁ C).toScheme := ⟨x, mem_connectedComponent⟩
  exact (RingHom.injective_respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap f C xC)).mp
    (stalkMap_injective_of_integral_dense_flat (f ∣_ C) D hD hflat xC)

end AlgebraicGeometry.Scheme
