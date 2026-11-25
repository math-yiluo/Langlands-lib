/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide

/-! # Proper changes of ambient scheme in the explicit graph comparison

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, applied to the
product/intersection formula of `EtaleLocallyClosedGraphModel`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem cancel_proper_ambient_boundaries
    {C : Type*} [Category C] {B O₁ O₂ N₁ N₂ F₁ F₂ : C}
    (a₁ : B ≅ O₁) (a₂ : B ≅ O₂) (m₁ : O₁ ≅ N₁) (m₂ : O₂ ≅ N₂)
    (b₁ : F₁ ≅ N₁) (b₂ : F₂ ≅ N₂) (d₁ : O₁ ≅ O₂) (d₂ : N₁ ≅ N₂)
    (L : F₁ ≅ F₂)
    (h₁ : a₁.hom ≫ d₁.hom = a₂.hom)
    (h₂ : b₁.hom ≫ d₂.hom = L.hom ≫ b₂.hom)
    (hm : m₁.hom ≫ d₂.hom = d₁.hom ≫ m₂.hom) :
    (a₁ ≪≫ m₁ ≪≫ b₁.symm) ≪≫ L = a₂ ≪≫ m₂ ≪≫ b₂.symm := by
  apply Iso.ext
  apply (cancel_mono b₂.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← h₂]
  simp only [Iso.inv_hom_id_assoc]
  rw [hm, ← Category.assoc, h₁]

/-- The explicit graph comparison commutes with a Cartesian proper change of its ambient
scheme, before any shrinking of the supporting open.

Source: Stacks Project, more-etale.tex, Tags 0F7C (vertical pasting) and 0F7D
(horizontal pasting); the proper-projection grids of steps 5--7 in
lem-pur-etale-pairwise-product-graph-normalization.
(auxiliary; not a blueprint node).

Proof: in the products `s.P ×_Y c.Z` and `t.P ×_Y c.Z`, the map induced by `pr`
is proper. The supporting neighborhood for `t` is the inverse image of the one
for `s` by the supplied Cartesian square. The neighborhood for `c` and their
intersection are also related by Cartesian proper maps. Their proper graph lifts
are compatible with these maps by the pullback projection equations and `hz`.
For each supporting neighborhood, expand the side word of the graph comparison.
Vertical pasting of the normalized proper/open exchange identifies this side word
with the old side word followed by the proper-projection exchange and direct-image
compositor. For the intersection word, apply vertical pasting to the graph triangle
above the proper-projection square and horizontal pasting to the two open inclusions.
Naturality interchanges the two exchange factors and gives the same projection
exchange at both ends. Substitute these equations in `B₂⁻¹ R(B₁₂) B₁`.
The two occurrences of the intersection projection exchange cancel. The remaining
side factor is precisely the displayed compositor--Cartesian-exchange word.
Associativity of the canonical direct-image and open compositors supplies the
parenthesizations shown below. The argument also applies to empty schemes and to
identity maps; it requires no quasi-compactness of either supporting open. -/
theorem etaleGraphComparisonFromOpen_properAmbient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) (pr : t.P ⟶ s.P) [IsProper pr]
    (q : t.U ⟶ s.U) (sq : IsPullback q t.e s.e pr)
    (hz : t.a ≫ q = s.a) (hp : pr ≫ s.p = t.p) :
    etaleGraphComparisonFromOpen A c s ≪≫
        Functor.isoWhiskerRight
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) t.a q s.a hz).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A sq) _ ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _
            (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr s.p t.p hp)) =
      etaleGraphComparisonFromOpen A c t := by
  let hs := (Category.assoc s.a s.e s.p).trans (s.fac.trans c.comm)
  let ht := (Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)
  let ms := Classical.choice
    (etaleLocallyClosedGraphModel A s.a s.e s.p c.i c.g c.comm.symm s.fac)
  let mt := Classical.choice
    (etaleLocallyClosedGraphModel A t.a t.e t.p c.i c.g c.comm.symm t.fac)
  have := ms.properS₁
  have := ms.properS₂
  have := mt.properS₁
  have := mt.properS₂
  let a₁ := locallyClosedGraphSide₁ s.a s.e s.p c.i c.g hs A
  let a₂ := locallyClosedGraphSide₁ t.a t.e t.p c.i c.g ht A
  let b₁ := locallyClosedGraphSide₂ s.a s.e s.p c.i c.g hs A
  let b₂ := locallyClosedGraphSide₂ t.a t.e t.p c.i c.g ht A
  let m₁ := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (locallyClosedGraphMiddle s.a s.e s.p c.i c.g hs A)
      R((pullback.fst s.p c.g ≫ s.p)_*[ModuleCat.{u + 1} A]) ≪≫
    Functor.associator _ _ _
  let m₂ := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (locallyClosedGraphMiddle t.a t.e t.p c.i c.g ht A)
      R((pullback.fst t.p c.g ≫ t.p)_*[ModuleCat.{u + 1} A]) ≪≫
    Functor.associator _ _ _
  let d₁ := s.properAmbientFirstTransport c t pr q sq hz hp A
  let d₂ := s.properAmbientSecondTransport c t pr q sq hz hp A
  let L := etaleProperAmbientTransport A s.a s.e s.p t.a t.e t.p pr q sq hz hp
  have h₁ : a₁.hom ≫ d₁.hom = a₂.hom :=
    etaleGraphProperAmbientFirstSide A c s t pr q sq hz hp
  have h₂ : b₁.hom ≫ d₂.hom = L.hom ≫ b₂.hom :=
    etaleGraphProperAmbientSecondSide A c s t pr q sq hz hp
  have hm : m₁.hom ≫ d₂.hom = d₁.hom ≫ m₂.hom :=
    etaleGraphProperAmbientMiddle A c s t pr q sq hz hp
  have hs' : etaleGraphComparisonFromOpen A c s = a₁ ≪≫ m₁ ≪≫ b₁.symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso, a₁, b₁, m₁,
      Iso.trans_hom, Category.assoc]
  have ht' : etaleGraphComparisonFromOpen A c t = a₂ ≪≫ m₂ ≪≫ b₂.symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso, a₂, b₂, m₂,
      Iso.trans_hom, Category.assoc]
  change etaleGraphComparisonFromOpen A c s ≪≫ L = etaleGraphComparisonFromOpen A c t
  rw [hs', ht']
  exact cancel_proper_ambient_boundaries a₁ a₂ m₁ m₂ b₁ b₂ d₁ d₂ L h₁ h₂ hm

end AlgebraicGeometry.Etale
