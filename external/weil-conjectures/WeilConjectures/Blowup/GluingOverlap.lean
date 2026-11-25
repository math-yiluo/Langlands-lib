/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Gluing

/-!

# Overlap comparison isomorphisms of the local blow-ups

The blow-up of a scheme `X` along a quasi-coherent ideal `I` is glued in
`WeilConjectures.Blowup.Gluing` over the thin category of all affine opens, so no explicit
overlap maps or cocycle conditions are needed there. This file recovers the classical gluing
data of the blueprint from that construction.

For affine opens `U ≤ V` the restriction map `r_{V,U} : B_U ⟶ B_V` of the local models
(`I.blowupFunctor.map`) is an open immersion onto the preimage of `U` in `B_V`
(`opensRange_blowupFunctor_map`). If `U ≤ V_i` and `U ≤ V_j` (in the blueprint `U = D(s)` is a
basic open), the overlap isomorphism is `ω_{ij,U} = r_{j,U} ∘ r_{i,U}⁻¹`.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.blowupOverlapOpen` — the preimage of `U` in the
  local model over `V`.
- `AlgebraicGeometry.Scheme.IdealSheafData.blowupRestrictIso` — the restriction isomorphism
  `r_{V,U} : B_U ≅ B_V|_U`.
- `AlgebraicGeometry.Scheme.IdealSheafData.blowupOverlapIso` — the overlap isomorphism
  `ω_{ij,U} : B_{V_i}|_U ≅ B_{V_j}|_U`.

## Main results

- `blowupOverlapIso_self`, `blowupOverlapIso_symm` — identity and symmetry.
- `blowupOverlapIso_trans` — the cocycle condition.
- `blowupOverlapIso_independent` — compatibility under shrinking `U`, so overlap maps for
  different refinements agree on intersections.
- `blowupOverlapIso_hom_structure` — the overlap isomorphisms are isomorphisms over `X`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The open subscheme of the local blow-up over `V` lying over the affine open `U ≤ V`,
i.e. the preimage of `U` under the structure map `B_V ⟶ V`. -/
noncomputable def blowupOverlapOpen {U V : X.affineOpens} (hUV : U ≤ V) :
    (I.blowupFunctor.obj V).Opens :=
  I.blowupNatTrans.app V ⁻¹ᵁ (X.homOfLE hUV).opensRange

lemma opensRange_blowupFunctor_map_eq_blowupOverlapOpen {U V : X.affineOpens} (hUV : U ≤ V) :
    (I.blowupFunctor.map (homOfLE hUV)).opensRange = I.blowupOverlapOpen hUV :=
  I.opensRange_blowupFunctor_map hUV

/-- The restriction isomorphism `r_{V,U} : B_U ≅ B_V|_U` from the local blow-up over `U`
onto the part of the local blow-up over `V` lying over `U`. -/
noncomputable def blowupRestrictIso {U V : X.affineOpens} (hUV : U ≤ V) :
    I.blowupFunctor.obj U ≅ I.blowupOverlapOpen hUV :=
  (I.blowupFunctor.map (homOfLE hUV)).isoOpensRange ≪≫
    Scheme.isoOfEq _ (I.opensRange_blowupFunctor_map hUV)

@[reassoc (attr := simp)]
lemma blowupRestrictIso_hom_ι {U V : X.affineOpens} (hUV : U ≤ V) :
    (I.blowupRestrictIso hUV).hom ≫ (I.blowupOverlapOpen hUV).ι =
      I.blowupFunctor.map (homOfLE hUV) := by
  simp [blowupRestrictIso]

@[reassoc (attr := simp)]
lemma blowupRestrictIso_inv_comp {U V : X.affineOpens} (hUV : U ≤ V) :
    (I.blowupRestrictIso hUV).inv ≫ I.blowupFunctor.map (homOfLE hUV) =
      (I.blowupOverlapOpen hUV).ι := by
  rw [Iso.inv_comp_eq, blowupRestrictIso_hom_ι]

/-- **The basic-overlap comparison isomorphism** `ω_{ij,U} = r_{j,U} ∘ r_{i,U}⁻¹` between the
parts of the local blow-ups over `V_i` and over `V_j` lying over an affine open `U ⊆ V_i ∩ V_j`.
The blueprint takes `U = D(s)` basic, where `r_{i,U}` is an isomorphism onto the preimage by
`isPullback_blowupNatTrans_of_basicOpen`. Here `U` may be any affine open.
(blueprint: `definition-admissible-blow-up--1`) -/
noncomputable def blowupOverlapIso {U Vi Vj : X.affineOpens} (hi : U ≤ Vi) (hj : U ≤ Vj) :
    (I.blowupOverlapOpen hi : Scheme.{u}) ≅ I.blowupOverlapOpen hj :=
  (I.blowupRestrictIso hi).symm ≪≫ I.blowupRestrictIso hj

@[reassoc (attr := simp)]
lemma blowupOverlapIso_hom_ι {U Vi Vj : X.affineOpens} (hi : U ≤ Vi) (hj : U ≤ Vj) :
    (I.blowupOverlapIso hi hj).hom ≫ (I.blowupOverlapOpen hj).ι =
      (I.blowupRestrictIso hi).inv ≫ I.blowupFunctor.map (homOfLE hj) := by
  simp [blowupOverlapIso]

@[reassoc (attr := simp)]
lemma blowupRestrictIso_hom_blowupOverlapIso_hom {U Vi Vj : X.affineOpens} (hi : U ≤ Vi)
    (hj : U ≤ Vj) :
    (I.blowupRestrictIso hi).hom ≫ (I.blowupOverlapIso hi hj).hom =
      (I.blowupRestrictIso hj).hom := by
  simp [blowupOverlapIso]

/-- The structure maps of the local blow-ups are compatible with the restriction maps. -/
@[reassoc]
lemma blowupFunctor_map_blowupNatTrans_app {U V : X.affineOpens} (hUV : U ≤ V) :
    I.blowupFunctor.map (homOfLE hUV) ≫ I.blowupNatTrans.app V ≫ V.1.ι =
      I.blowupNatTrans.app U ≫ U.1.ι := by
  have h := I.blowupNatTrans.naturality (homOfLE hUV)
  have hG : X.directedAffineCover.functorOfLocallyDirected.map (homOfLE hUV) =
      X.homOfLE hUV := rfl
  rw [hG] at h
  rw [reassoc_of% h, Scheme.homOfLE_ι]

/-- The overlap isomorphisms are isomorphisms over `X`. -/
lemma blowupOverlapIso_hom_structure {U Vi Vj : X.affineOpens} (hi : U ≤ Vi) (hj : U ≤ Vj) :
    (I.blowupOverlapIso hi hj).hom ≫ (I.blowupOverlapOpen hj).ι ≫ I.blowupNatTrans.app Vj ≫
        Vj.1.ι =
      (I.blowupOverlapOpen hi).ι ≫ I.blowupNatTrans.app Vi ≫ Vi.1.ι := by
  rw [blowupOverlapIso_hom_ι_assoc, blowupFunctor_map_blowupNatTrans_app,
    ← blowupRestrictIso_inv_comp, Category.assoc, blowupFunctor_map_blowupNatTrans_app]

/-- The overlap isomorphism of a chart with itself is the identity.
(blueprint: `definition-admissible-blow-up--1`) -/
@[simp]
lemma blowupOverlapIso_self {U V : X.affineOpens} (h : U ≤ V) :
    I.blowupOverlapIso h h = Iso.refl _ :=
  Iso.symm_self_id _

/-- The overlap isomorphism from chart `i` to chart `j` is inverse to the one from `j` to `i`.
(blueprint: `definition-admissible-blow-up--1`) -/
lemma blowupOverlapIso_symm {U Vi Vj : X.affineOpens} (hi : U ≤ Vi) (hj : U ≤ Vj) :
    (I.blowupOverlapIso hi hj).symm = I.blowupOverlapIso hj hi :=
  Iso.ext rfl

/-- **Cocycle condition**: `ω_{jk,U} ∘ ω_{ij,U} = ω_{ik,U}` over an affine open `U` contained
in `V_i ∩ V_j ∩ V_k`. Together with `blowupOverlapIso_independent` this gives the cocycle
condition on triple overlaps covered by such opens.
(blueprint: `definition-admissible-blow-up--1`) -/
@[simp]
lemma blowupOverlapIso_trans {U Vi Vj Vk : X.affineOpens} (hi : U ≤ Vi) (hj : U ≤ Vj)
    (hk : U ≤ Vk) :
    I.blowupOverlapIso hi hj ≪≫ I.blowupOverlapIso hj hk = I.blowupOverlapIso hi hk :=
  Iso.ext (by simp [blowupOverlapIso])

lemma blowupOverlapOpen_mono {W U V : X.affineOpens} (hWU : W ≤ U) (hUV : U ≤ V) :
    I.blowupOverlapOpen (hWU.trans hUV) ≤ I.blowupOverlapOpen hUV := by
  intro z hz
  have hz' : (I.blowupNatTrans.app V z).1 ∈ W.1 :=
    (mem_opensRange_homOfLE (hWU.trans hUV) _).mp hz
  exact (mem_opensRange_homOfLE hUV _).mpr (hWU hz')

/-- **Independence of the refinement**: for affine opens `W ≤ U ≤ V_i ∩ V_j`, the overlap
isomorphism over `U` restricts on the part over `W` to the overlap isomorphism over `W`. Hence
overlap isomorphisms constructed from two refinements agree on their intersection.
(blueprint: `definition-admissible-blow-up--1`) -/
lemma blowupOverlapIso_independent {W U Vi Vj : X.affineOpens} (hWU : W ≤ U) (hi : U ≤ Vi)
    (hj : U ≤ Vj) :
    (I.blowupFunctor.obj Vi).homOfLE (I.blowupOverlapOpen_mono hWU hi) ≫
        (I.blowupOverlapIso hi hj).hom =
      (I.blowupOverlapIso (hWU.trans hi) (hWU.trans hj)).hom ≫
        (I.blowupFunctor.obj Vj).homOfLE (I.blowupOverlapOpen_mono hWU hj) := by
  have key : (I.blowupFunctor.obj Vi).homOfLE (I.blowupOverlapOpen_mono hWU hi) ≫
      (I.blowupRestrictIso hi).inv =
      (I.blowupRestrictIso (hWU.trans hi)).inv ≫ I.blowupFunctor.map (homOfLE hWU) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq,
      ← cancel_mono (I.blowupOverlapOpen hi).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, blowupRestrictIso_hom_ι,
      ← Functor.map_comp, homOfLE_comp]
  rw [← cancel_mono (I.blowupOverlapOpen hj).ι]
  simp only [Category.assoc, blowupOverlapIso_hom_ι, Scheme.homOfLE_ι]
  rw [reassoc_of% key, ← Functor.map_comp, homOfLE_comp]

end AlgebraicGeometry.Scheme.IdealSheafData
