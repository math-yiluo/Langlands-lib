/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# Base change maps of a composite, through the conjugate composition isomorphisms

The form of `CategoryTheory.Adjunction.mateEquiv_inv_comp` for the isomorphisms of right adjoints
`Rh ≅ Rg ⋙ Rf` conjugate (`CategoryTheory.conjugateIsoEquiv`) to composition isomorphisms
`e : Lh ≅ Lf ⋙ Lg` of the left adjoints compatible with the exchange maps
(`CategoryTheory.Adjunction.ExchangeCompCompatible`): the mate of the inverse exchange of the
pasted square is the pasting of the mates
(`CategoryTheory.Adjunction.mateEquiv_inv_comp_conjugate`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz]
  [Category* Cx'] [Category* Cy'] [Category* Cz']
  {Lf : Cx ⥤ Cy} {Rf : Cy ⥤ Cx} (adjf : Lf ⊣ Rf) {Lg : Cy ⥤ Cz} {Rg : Cz ⥤ Cy} (adjg : Lg ⊣ Rg)
  {Lh : Cx ⥤ Cz} {Rh : Cz ⥤ Cx} (adjh : Lh ⊣ Rh)
  {Lf' : Cx' ⥤ Cy'} {Rf' : Cy' ⥤ Cx'} (adjf' : Lf' ⊣ Rf')
  {Lg' : Cy' ⥤ Cz'} {Rg' : Cz' ⥤ Cy'} (adjg' : Lg' ⊣ Rg')
  {Lh' : Cx' ⥤ Cz'} {Rh' : Cz' ⥤ Cx'} (adjh' : Lh' ⊣ Rh')
  {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}

/-- The inverse-exchange form of `CategoryTheory.Adjunction.ExchangeCompCompatible`. -/
lemma ExchangeCompCompatible.inv_app_comp
    (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') [IsIso Exf] (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') [IsIso Exg]
    (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh') [IsIso Exh] (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
    (hEx : ExchangeCompCompatible Exf Exg Exh e e') (M : Cx) :
    (inv Exh).app M ≫ Gc.map (e.hom.app M) =
      e'.hom.app (Ga.obj M) ≫ Lg'.map ((inv Exf).app M) ≫ (inv Exg).app (Lf.obj M) := by
  have h := hEx.comp M
  rw [← cancel_epi (Exh.app M)]
  simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, Functor.map_inv]
  rw [← cancel_mono (Exg.app _), ← cancel_mono (Lg'.map (Exf.app M))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact h

/-- The counit characterization of the isomorphism `Rh ≅ Rg ⋙ Rf` conjugate to a composition
isomorphism `e : Lh ≅ Lf ⋙ Lg`: the hypothesis `hρ` of
`CategoryTheory.Adjunction.mateEquiv_inv_comp`. -/
lemma conjugateIsoEquiv_comp_inv_app_counit (e : Lh ≅ Lf ⋙ Lg) (K : Cz) :
    Lg.map (Lf.map ((conjugateIsoEquiv (adjf.comp adjg) adjh e).inv.app K)) ≫
        Lg.map (adjf.counit.app _) ≫ adjg.counit.app K =
      e.inv.app _ ≫ adjh.counit.app K := by
  have := conjugateEquiv_counit adjh (adjf.comp adjg) e.inv K
  simpa only [Functor.comp_map, Adjunction.comp_counit_app, Category.assoc,
    conjugateIsoEquiv_apply_inv] using this

/-- **Base change maps of a composite, through the conjugate composition isomorphisms**: for
composition isomorphisms `e`, `e'` compatible with the exchange maps, the mate of the inverse
exchange of the pasted square is the pasting of the mates, through the conjugates
`Rh ≅ Rg ⋙ Rf` of `e` and `e'`. -/
theorem mateEquiv_inv_comp_conjugate
    (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') [IsIso Exf] (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') [IsIso Exg]
    (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh') [IsIso Exh] (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
    (hEx : ExchangeCompCompatible Exf Exg Exh e e') (K : Cz) :
    Ga.map ((conjugateIsoEquiv (adjf.comp adjg) adjh e).inv.app K) ≫
        (mateEquiv adjf adjf' (inv Exf)).app (Rg.obj K) ≫
        Rf'.map ((mateEquiv adjg adjg' (inv Exg)).app K) =
      (mateEquiv adjh adjh' (inv Exh)).app K ≫
        (conjugateIsoEquiv (adjf'.comp adjg') adjh' e').inv.app (Gc.obj K) :=
  mateEquiv_inv_comp adjf adjg adjh adjf' adjg' adjh' (inv Exf) (inv Exg) (inv Exh) e e'
    (ExchangeCompCompatible.inv_app_comp Exf Exg Exh e e' hEx) _
    (conjugateIsoEquiv_comp_inv_app_counit adjf adjg adjh e) _
    (conjugateIsoEquiv_comp_inv_app_counit adjf' adjg' adjh' e') K

end CategoryTheory.Adjunction
