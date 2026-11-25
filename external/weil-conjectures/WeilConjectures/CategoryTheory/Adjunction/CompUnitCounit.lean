/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

# Units and counits along a composite which is the identity

Let `adjA : L_a ⊣ R_a`, `adjB : L_b ⊣ R_b` and `adjC : L_c ⊣ R_c` be adjunctions, thought of as
the pullback and pushforward along morphisms `a : T ⟶ Z`, `b : Z ⟶ T` and `c = a ≫ b`, with a
composition isomorphism `L_c ≅ L_b ⋙ L_a` conjugate to `R_a ⋙ R_b ≅ R_c`, and suppose `c` is the
identity: `L_c ≅ 𝟭` conjugate to `R_c ≅ 𝟭`. Then the map `R_b N ⟶ L_a N` obtained from the
counit of `adjB`,
```
R_b N ≅ L_c (R_b N) ≅ L_a (L_b (R_b N)) ⟶ L_a N,
```
is the map obtained from the unit of `adjA`,
```
R_b N ⟶ R_b (R_a (L_a N)) ≅ R_c (L_a N) ≅ L_a N
```
(`CategoryTheory.Adjunction.counit_eq_unit_of_comp_eq_id`). For the pullback and pushforward
along a section `a` of `b`, this identifies the restriction of the stalks of `b_* N` along `a`
with `b_*` of the unit of `a^* ⊣ a_*`.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {DU DZ : Type*} [Category DU] [Category DZ] {La : DZ ⥤ DU} {Ra : DU ⥤ DZ}
  {Lb : DU ⥤ DZ} {Rb : DZ ⥤ DU} {Lc Rc : DU ⥤ DU}

/-- **Units and counits along a composite which is the identity.** -/
lemma counit_eq_unit_of_comp_eq_id (adjA : La ⊣ Ra) (adjB : Lb ⊣ Rb) (adjC : Lc ⊣ Rc)
    (cL : Lc ≅ Lb ⋙ La) (dR : Ra ⋙ Rb ≅ Rc)
    (hc : ∀ M, adjB.unit.app M ≫ Rb.map (adjA.unit.app (Lb.obj M)) ≫
      dR.hom.app (La.obj (Lb.obj M)) = adjC.unit.app M ≫ Rc.map (cL.hom.app M))
    (eL : Lc ≅ 𝟭 _) (eR : Rc ≅ 𝟭 _)
    (he : ∀ M, adjC.unit.app M ≫ Rc.map (eL.hom.app M) = eR.inv.app M) (N : DZ) :
    eL.inv.app (Rb.obj N) ≫ cL.hom.app (Rb.obj N) ≫ La.map (adjB.counit.app N) =
      Rb.map (adjA.unit.app N) ≫ dR.hom.app (La.obj N) ≫ eR.hom.app (La.obj N) := by
  -- a map `f : Q ⟶ W` is determined by the adjoint of `eL.hom ≫ f`, which is `f ≫ eR.inv`
  have key {Q W : DU} (f : Q ⟶ W) :
      adjC.unit.app Q ≫ Rc.map (eL.hom.app Q ≫ f) = f ≫ eR.inv.app W := by
    rw [Functor.map_comp, reassoc_of% (he Q)]
    exact (eR.inv.naturality f).symm
  rw [← cancel_mono (eR.inv.app (La.obj N))]
  erw [← key (eL.inv.app (Rb.obj N) ≫ cL.hom.app (Rb.obj N) ≫ La.map (adjB.counit.app N)),
    ← key (Rb.map (adjA.unit.app N) ≫ dR.hom.app (La.obj N) ≫ eR.hom.app (La.obj N))]
  erw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.id_obj]
  have hd := dR.hom.naturality (La.map (adjB.counit.app N))
  have hη := adjA.unit.naturality (adjB.counit.app N)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hd hη
  rw [Functor.map_comp, ← reassoc_of% (hc (Rb.obj N)), ← hd, ← Rb.map_comp_assoc, ← hη,
    Rb.map_comp_assoc, ← Category.assoc, adjB.right_triangle_components, Category.id_comp]
  rw [key]
  simp

end CategoryTheory.Adjunction
