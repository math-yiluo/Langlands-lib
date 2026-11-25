/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Limits

/-! Auxiliary step of effective fpqc descent, following the Stacks Project. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The chosen categorical pullback carries the pulled-back descent datum.
Source: Stacks Project, Descent, Tag 023Y (1), pullback of descent data.
(blueprint: lem-galois-fpqc-canonical-pullback-datum)

For a point of the pullback over a : T → X', project to V, transport by D along
(a ≫ h, b ≫ h), and pair the transported point with b : T → X'. The pullback
universal property supplies a unique point of the pullback over b. Its two
projections show naturality, the identity law, and the cocycle law using the
corresponding laws of D. The first projection gives IsBaseChange. This construction
uses no covering assumption and works for empty schemes and identity maps. -/
theorem exists_canonical_pullback_descent_datum {S X X' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S) (h : X' ⟶ X) (hc : h ≫ f = g)
    {V : Over X} (D : Over.DescentDatum f V) :
    ∃ E : Over.DescentDatum g (Over.mk (pullback.snd V.hom h)),
      Over.DescentDatum.IsBaseChange hc (pullback.condition (f := V.hom) (g := h))
        D E := by
  let point {T : Scheme.{u}} (a : T ⟶ X')
      (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom h)) : Over.mk (a ≫ h) ⟶ V :=
    Over.homMk (x.left ≫ pullback.fst V.hom h) (by
      simpa [Category.assoc, pullback.condition] using
        congrArg (fun z => z ≫ h) (Over.w x))
  let tr {T : Scheme.{u}} (a b : T ⟶ X') (hab : a ≫ g = b ≫ g)
      (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom h)) :
      Over.mk b ⟶ Over.mk (pullback.snd V.hom h) :=
    Over.homMk (pullback.lift
      (D.transport (a ≫ h) (b ≫ h)
        (by rw [Category.assoc, Category.assoc, hc, hab]) (point a x)).left b
      (Over.w _)) (by simp)
  have hfst {T : Scheme.{u}} (a b : T ⟶ X') (hab : a ≫ g = b ≫ g)
      (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom h)) :
      point b (tr a b hab x) =
        D.transport (a ≫ h) (b ≫ h)
          (by rw [Category.assoc, Category.assoc, hc, hab]) (point a x) := by
    ext : 1
    simp [point, tr]
  have hext {T : Scheme.{u}} (a : T ⟶ X')
      (x y : Over.mk a ⟶ Over.mk (pullback.snd V.hom h))
      (hxy : point a x = point a y) : x = y := by
    ext : 1
    apply pullback.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  refine ⟨{ transport := tr
            transport_homMk_comp := ?_
            transport_self := ?_
            transport_transport := ?_ }, ?_⟩
  · intro T T' k a b hab x
    apply hext
    simp only [hfst]
    ext : 1
    convert congrArg (fun z => z.left)
      (D.transport_homMk_comp k (a ≫ h) (b ≫ h)
        (by rw [Category.assoc, Category.assoc, hc, hab]) (point a x)) using 1 <;>
      simp [point, tr, Category.assoc]
    congr 2
  · intro T a x
    apply hext
    simp only [hfst, D.transport_self]
  · intro T a b c hab hbc x
    apply hext
    simp only [hfst, D.transport_transport]
  · intro T a b hab x
    change (D.transport _ _ _ (point a x)).left = (tr a b hab x).left ≫ _
    exact (congrArg (fun z => z.left) (hfst a b hab x)).symm

end AlgebraicGeometry
