/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition

/-! # First-side pasting under a proper ambient change

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, proper-projection grid.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

/-- The first side word commutes with the proper change of graph product.

Proof: write r for the induced proper product map, r1 for its pullback to the first
neighborhood, and d_s,d_t for the projections of these neighborhoods to X. The
projection equations give d_s r1 = d_t and r p2_s = p2_t, while the graph equations
give r1 s1_t = s1_s. Stack the Cartesian proper/open square for r1,r over the old
side square. Its outer rectangle is the new side square. Apply vertical pasting
of etaleProperOpenExchangeCube and its Cartesian normalization. Insert the inverse
direct-image compositors for the two graph/projection factorizations of the identity.
Naturality moves those compositors through the exchanges. Associativity of the
normalized direct-image compositors identifies both resulting outer factors; the
identity direct-image comparison is the same on both paths and cancels. This gives
the displayed equality before considering either the second side or intersection.
The projection equations and pasting laws also hold for empty schemes and identities.

Source: Stacks Project, more-etale.tex, Tag 0F7C, vertical pasting.
(auxiliary; not a blueprint node). -/
theorem etaleGraphProperAmbientFirstSide
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) (pr : t.P ⟶ s.P) [IsProper pr]
    (q : t.U ⟶ s.U) (sq : IsPullback q t.e s.e pr)
    (hz : t.a ≫ q = s.a) (hp : pr ≫ s.p = t.p) :
    (locallyClosedGraphSide₁ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)) A).hom ≫
        (s.properAmbientFirstTransport c t pr q sq hz hp A).hom =
      (locallyClosedGraphSide₁ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A).hom := by
  let h (H : EtaleGraphPresentation f) :=
    (Category.assoc H.a H.e H.p).trans (H.fac.trans c.comm)
  let U := (Functor.leftUnitor
      (D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((c.g)_*[ModuleCat.{u + 1} A]))).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerStarIdIso A X).symm _
  have ha (H : EtaleGraphPresentation f) :
      locallyClosedGraphS₁ H.a H.e H.p c.i c.g (h H) ≫
        pullback.snd (pullback.snd H.p c.g) c.i = 𝟙 X := by
    simp only [locallyClosedGraphS₁, pullback.lift_snd]
  let T (H : EtaleGraphPresentation f) :=
    etaleProperAmbientTransport A (𝟙 X) c.i c.g
      (locallyClosedGraphS₁ H.a H.e H.p c.i c.g (h H)) (pullback.fst _ _)
      (pullback.fst H.p c.g ≫ H.p) (pullback.snd H.p c.g) (pullback.snd _ _)
      (IsPullback.of_hasPullback (pullback.snd H.p c.g) c.i).flip
      (ha H) pullback.condition.symm
  have hside (H : EtaleGraphPresentation f) :
      locallyClosedGraphSide₁ H.a H.e H.p c.i c.g (h H) A = U ≪≫ T H := by
    apply Iso.ext
    ext K
    simp only [locallyClosedGraphSide₁, T, U, etaleProperAmbientTransport,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.map_comp, Category.assoc]
  let R := s.properAmbientProduct c t pr hp
  let r := s.properAmbientFirst c t pr hp
  have hcomp := etaleProperAmbientTransport_comp A (𝟙 X) c.i c.g
    (locallyClosedGraphS₁ s.a s.e s.p c.i c.g (h s)) (pullback.fst _ _)
    (pullback.fst s.p c.g ≫ s.p)
    (locallyClosedGraphS₁ t.a t.e t.p c.i c.g (h t)) (pullback.fst _ _)
    (pullback.fst t.p c.g ≫ t.p)
    (pullback.snd s.p c.g) R (pullback.snd _ _) r
    (IsPullback.of_hasPullback (pullback.snd s.p c.g) c.i).flip
    (s.properAmbientFirst_isPullback c t pr hp)
    (ha s) (s.properAmbientFirst_graph c t pr q sq hz hp) pullback.condition.symm
    (s.properAmbientProduct_base c t pr hp)
  have hm : T s ≪≫ s.properAmbientFirstTransport c t pr q sq hz hp A = T t := by
    change etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _ ≪≫
      etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _ =
      etaleProperAmbientTransport A _ _ _ _ _ _ _ _ _ _ _
    rw [hcomp]
    congr 1
    · simp only [R, EtaleGraphPresentation.properAmbientProduct, pullback.lift_snd]
    · simp only [r, EtaleGraphPresentation.properAmbientFirst, pullback.lift_snd]
  have heq : locallyClosedGraphSide₁ s.a s.e s.p c.i c.g (h s) A ≪≫
      s.properAmbientFirstTransport c t pr q sq hz hp A =
      locallyClosedGraphSide₁ t.a t.e t.p c.i c.g (h t) A := by
    rw [hside s, hside t, Iso.trans_assoc, hm]
  exact congrArg Iso.hom heq

end AlgebraicGeometry.Etale
