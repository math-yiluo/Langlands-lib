/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-!
# Morphisms of the condensed rings `C(-, T)` induced by ring homomorphisms

A continuous ring homomorphism `φ : T →+* T'` induces, by postcomposition, a morphism of ring
objects `C(-, T) ⟶ C(-, T')` of condensed abelian groups (`Profinite.continuousMapRingObjMap`).
It sends the constant global section `t` to the constant global section `φ t`
(`Profinite.continuousMapConstRingHom_hom_comp_continuousMapRingObjMap`).
Postcomposition is functorial (`Profinite.continuousMapRingObjMap_comp`,
`Profinite.continuousMapRingObjMap_eq_id`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace Profinite

variable {T T' : Type} [TopologicalSpace T] [TopologicalSpace T']

section Ring

variable [Ring T] [IsTopologicalRing T] [Ring T'] [IsTopologicalRing T'] (φ : T →+* T')
  (hφ : Continuous φ)

/-- The morphism of ring objects `C(-, T) ⟶ C(-, T')` of condensed abelian groups given by
postcomposition with a continuous ring homomorphism `φ : T →+* T'`. -/
noncomputable def continuousMapRingObjMap :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap φ hφ)

instance : IsMonHom (continuousMapRingObjMap.{u} φ hφ) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap φ hφ)))

/-- Postcomposition is compatible with composition of continuous ring homomorphisms. -/
lemma continuousMapRingObjMap_comp {T'' : Type} [TopologicalSpace T''] [Ring T'']
    [IsTopologicalRing T''] (ψ : T' →+* T'') (hψ : Continuous ψ) :
    continuousMapRingObjMap.{u} (ψ.comp φ) (hψ.comp hφ) =
      continuousMapRingObjMap φ hφ ≫ continuousMapRingObjMap ψ hψ :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_comp
    (continuousMapRingSheafMap φ hφ) (continuousMapRingSheafMap ψ hψ)

/-- Postcomposition with a continuous ring endomorphism equal to the identity is the identity. -/
lemma continuousMapRingObjMap_eq_id (f : T →+* T) (hf : Continuous f) (h : f = RingHom.id T) :
    continuousMapRingObjMap.{u} f hf = 𝟙 _ := by
  subst h
  exact (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_id
    _

end Ring

variable [CommRing T] [IsTopologicalRing T] [CommRing T'] [IsTopologicalRing T'] (φ : T →+* T')
  (hφ : Continuous φ)

/-- The morphism `C(-, T) ⟶ C(-, T')` induced by `φ` sends the constant global section `t` to the
constant global section `φ t`. -/
lemma continuousMapConstRingHom_hom_comp_continuousMapRingObjMap (t : T) :
    (continuousMapConstRingHom.{u} T t).hom ≫ continuousMapRingObjMap φ hφ =
      (continuousMapConstRingHom.{u} T' (φ t)).hom := by
  rw [← Γ.map_hom]
  exact congrArg Γ.hom (Sheaf.Γ_map_ringHomΓSheafCompose _ (continuousMapRingSheafMap φ hφ)
    (continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl) (continuousMapConstSectionRingHom _)
    (fun _ _ ↦ rfl) (r := t) (r' := φ t) fun _ ↦ rfl)

end Profinite
