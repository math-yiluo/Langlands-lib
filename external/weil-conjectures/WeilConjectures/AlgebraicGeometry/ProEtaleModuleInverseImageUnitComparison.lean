/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit

/-! # The canonical comparison of module and abelian inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunct of the forgotten module unit is invertible for every scheme morphism.

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(auxiliary; not a blueprint node).

Proof: Transport both sites to their strict AsSmall models. The transported ring
unit presents the inverse-image ring, by proEtaleModelRingPresentation. Construct
on the actual abelian inverse image the scalar action obtained from that ring
presentation and the abelian unit presentation. Products of unit sections determine
maps out of the scalar/module product. Testing the module laws on these sections
therefore gives a module, and testing the two scalar-action composites shows that
an abelian map is linear precisely when its adjunct is linear. Restricting the
abelian Hom equivalence gives a module adjunction whose underlying unit is exactly
the abelian unit. Compare it with the pullbackPushforwardAdjunction on the small
model by uniqueness of left adjoints. That comparison respects units, so its
underlying inverse is the adjunct of the forgotten module unit and is invertible.
Transport back along AsSmall; precomposition commutes with the forgetful functors
and transports the units, so the same identification holds on the original sites.
Finally compare this adjunction with the supplied ai by uniqueness of left adjoints.
Its unit formula identifies the displayed map with the canonical comparison
composed with the forgotten uniqueness isomorphism. This proves invertibility
for every ai, including the zero ring and empty schemes. No closed immersion is used. -/
theorem proEtaleModuleInverseImage_unitComparison_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)) :
    let S := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
    let R := (sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
    ∀ M, IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf S).obj M)
      ((SheafOfModules.toSheaf R).obj ((proEtaleModuleInverseImage i A).obj M))).symm
        ((SheafOfModules.toSheaf S).map (ai.unit.app M))) := by
  dsimp only
  intro M
  let a := proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}
  let P := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)
  let Q := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))
  let T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose
        (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let L := proEtaleModuleInverseImage i A
  obtain ⟨adj₀, h₀⟩ := proEtaleModuleInverseImage_canonicalUnitComparison i A
  let c₀ := (a.homEquiv (P.obj M) (Q.obj (L.obj M))).symm
    (P.map (adj₀.unit.app M))
  have hc₀ : IsIso c₀ := by
    exact h₀ M
  let e := adj₀.leftAdjointUniq ai
  have he : adj₀.unit.app M ≫ T.map (e.hom.app M) = ai.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app adj₀ ai M
  let c := (a.homEquiv (P.obj M) (Q.obj (L.obj M))).symm
    (P.map (ai.unit.app M))
  let f₀ : P.obj M ⟶
      (proEtaleSheafDirectImage i AddCommGrpCat).obj
        (Q.obj ((proEtaleModuleInverseImage i A).obj M)) :=
    P.map (adj₀.unit.app M)
  let g₀ : Q.obj ((proEtaleModuleInverseImage i A).obj M) ⟶
      Q.obj ((proEtaleModuleInverseImage i A).obj M) :=
    Q.map (e.hom.app M)
  have hce : c₀ ≫ g₀ = c := by
    have hh := a.homEquiv_naturality_right_symm f₀ g₀
    calc
      c₀ ≫ g₀ = (a.homEquiv (P.obj M)
          (Q.obj ((proEtaleModuleInverseImage i A).obj M))).symm f₀ ≫ g₀ := by rfl
      _ = (a.homEquiv (P.obj M)
          (Q.obj ((proEtaleModuleInverseImage i A).obj M))).symm
          (f₀ ≫ (proEtaleSheafDirectImage i AddCommGrpCat).map g₀) := hh.symm
      _ = (a.homEquiv (P.obj M)
          (Q.obj ((proEtaleModuleInverseImage i A).obj M))).symm
          (P.map (adj₀.unit.app M) ≫ P.map (T.map (e.hom.app M))) := by rfl
      _ = c := by rw [← P.map_comp, he]
  set_option linter.style.haveILetI false in
  letI : IsIso (e.hom.app M) := by infer_instance
  set_option linter.style.haveILetI false in
  letI : IsIso g₀ := Q.map_isIso _
  change IsIso c
  rw [← hce]
  exact inferInstanceAs (IsIso (c₀ ≫ g₀))

end AlgebraicGeometry.Scheme
