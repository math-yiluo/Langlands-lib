/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleTowerCover
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability

/-! # Compatible sections of finite locally constant sheaf towers

Source: Stacks Project, Tags 03RV, 01YW, 09BV and 0990; the finite-stalk
adaptation in the compatible derived trivializations proof, steps 1--5.
(blueprint: lem-weil-pbc-finite-lisse-tower-section-cover).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A countable tower of finite locally constant etale sheaves with nonempty geometric
stalks admits simultaneous compatible sections on an affine weakly contractible cover.
The transition maps need not be epimorphisms.

Source: Stacks Project, Tags 03RV, 01YW, 09BV and 0990; steps 1--5 of the
compatible finite derived trivializations proof.
(blueprint: lem-weil-pbc-finite-lisse-tower-section-cover).

Proof: Represent each sheaf by a finite etale scheme, using 03RV. Yoneda turns the
transitions into scheme maps. Over each affine open of X these schemes are affine.
Their inverse limit is the spectrum of the direct limit of their rings. The algebra
is ind-etale, so the limit is weakly etale. At a geometric point the tower of finite
nonempty stalks has a compatible tuple (finite inverse-system compactness). The
representing isomorphisms identify this tuple with compatible geometric points of
the finite etale schemes. The affine limit property gives a geometric point of the
limit above the chosen point. Thus the limit surjects onto the affine open and its
singleton is a pro-etale cover. The universal sections pull back along its projections
to compatible sections of the comparison inverse images: use the comparison adjunction
unit and naturality, rather than any preservation of infinite limits. Cover the limit
by affine opens and replace each by a faithfully flat ind-etale contractible extension
in the same universe. Compose these covers and restrict the compatible sections.
All indices remain in Type u; the empty base is covered by the empty family. -/
theorem finite_lisse_tower_section_cover
    (X : Scheme.{u}) (I : ℕ → Sheaf X.smallEtaleTopology (Type (u + 1)))
    (r : ∀ n : ℕ, I (n + 1) ⟶ I n)
    (hI : ∀ n : ℕ, IsLisseEtaleSheafOfSets (I n))
    (hne : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X), Nonempty ((pointSmallEtale x).sheafFiber.obj (I n))) :
    ∃ (J : Type u) (U : J → X.ProEt),
      Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (U j).hom) ∈
          proetalePrecoverage X ∧
      (∀ j : J, IsAffine (U j).left) ∧
      (∀ j : J, (ProEt.topology X).IsWeaklyContractible.{u + 1} (U j)) ∧
      ∃ s : ∀ (j : J) (n : ℕ),
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj (I n)).obj.obj
            (op (U j)),
        ∀ (j : J) (n : ℕ),
          ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
            (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).map (r n)).hom.app
              (op (U j)) (s j (n + 1)) = s j n := by
  classical
  choose Y π hfinite het e using fun n ↦
    finiteLocallyConstant_sets_representable X (I n) (hI n).1 (hI n).2
  let P (n : ℕ) : X.Etale := @Etale.mk _ _ (π n) (het n)
  let e' (n : ℕ) : (I n).obj ≅ uliftYoneda.{u + 1}.obj (P n) := (e n).some
  let p (n : ℕ) : P (n + 1) ⟶ P n := uliftYoneda.preimage
    ((e' (n + 1)).inv ≫ (r n).hom ≫ (e' n).hom)
  have hp (n : ℕ) : uliftYoneda.map (p n) =
      (e' (n + 1)).inv ≫ (r n).hom ≫ (e' n).hom := Functor.map_preimage _ _
  have hpoints (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ X) (n : ℕ) :
      Finite ((pointSmallEtale x).fiber.obj (P n)) ∧
        Nonempty ((pointSmallEtale x).fiber.obj (P n)) := by
    let Φ := pointSmallEtale x
    let Q := uliftYoneda.{u + 1}.obj (P n)
    let v : ∀ (V : X.Etale) (_ : Φ.fiber.obj V), Q.obj (op V) →
        ULift.{u + 1} (Φ.fiber.obj (P n)) :=
      fun V z f ↦ ⟨Φ.fiber.map f.down z⟩
    let b : Φ.presheafFiber.obj Q ⟶ ULift.{u + 1} (Φ.fiber.obj (P n)) :=
      Φ.presheafFiberDesc (fun V z ↦ TypeCat.ofHom (v V z)) (by
        intro V W f z
        ext g
        change Φ.fiber.map (f ≫ g.down) z = Φ.fiber.map g.down (Φ.fiber.map f z)
        rw [Functor.map_comp]
        rfl)
    have hb : Function.Surjective b := by
      rintro ⟨z⟩
      refine ⟨Φ.toPresheafFiber (P n) z Q ⟨𝟙 (P n)⟩, ?_⟩
      change (Φ.toPresheafFiber (P n) z Q ≫ b) ⟨𝟙 (P n)⟩ = _
      simp only [b, GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
      simp [v]
    let eF := Φ.presheafFiber.mapIso (e' n)
    have hfi : Finite (Φ.sheafFiber.obj (I n)) := (hI n).finite_sheafFiber Ω x
    change Finite (Φ.presheafFiber.obj (I n).obj) at hfi
    have hni : Nonempty (Φ.sheafFiber.obj (I n)) := hne n Ω x
    change Nonempty (Φ.presheafFiber.obj (I n).obj) at hni
    have : Finite (Φ.presheafFiber.obj Q) :=
      Finite.of_surjective eF.hom ((ConcreteCategory.bijective_of_isIso eF.hom).2)
    have : Nonempty (Φ.presheafFiber.obj Q) := Nonempty.map eF.hom inferInstance
    have : Finite (ULift.{u + 1} (Φ.fiber.obj (P n))) := Finite.of_surjective b hb
    exact ⟨Finite.of_surjective ULift.down ULift.down_surjective,
      Nonempty.map (fun z ↦ (b z).down) inferInstance⟩
  obtain ⟨J, U, hc, ha, hw, a, hpa⟩ := finite_etale_tower_cover X P p hfinite hpoints
  let F := Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)
  let η := (proEtaleSiteComparison X).unit
  let t (n : ℕ) : (I n).obj.obj (op (P n)) :=
    (e' n).inv.app (op (P n)) ⟨𝟙 (P n)⟩
  let s (j : J) (n : ℕ) : (F.obj (I n)).obj.obj (op (U j)) :=
    (F.obj (I n)).obj.map (a j n).op ((η.app (I n)).hom.app (op (P n)) (t n))
  refine ⟨J, U, hc, ha, hw, s, ?_⟩
  intro j n
  change ((F.map (r n)).hom.app (op (U j)))
    ((F.obj (I (n + 1))).obj.map (a j (n + 1)).op
      ((η.app (I (n + 1))).hom.app (op (P (n + 1))) (t (n + 1)))) = _
  rw [NatTrans.naturality_apply]
  have hr : (r n).hom.app (op (P (n + 1))) (t (n + 1)) =
      (I n).obj.map (p n).op (t n) := by
    apply (ConcreteCategory.bijective_of_isIso ((e' n).hom.app (op (P (n + 1))))).1
    have hh := congrArg (fun f ↦ f.app (op (P (n + 1))) ⟨𝟙 (P (n + 1))⟩) (hp n)
    simpa [t, ← NatTrans.naturality_apply] using hh.symm
  have hn := congrArg (fun f ↦ f.hom.app (op (P (n + 1))) (t (n + 1)))
    (η.naturality (r n))
  have hn' : (F.map (r n)).hom.app (op ((toProEt X).obj (P (n + 1))))
      ((η.app (I (n + 1))).hom.app (op (P (n + 1))) (t (n + 1))) =
      (η.app (I n)).hom.app (op (P (n + 1)))
        ((r n).hom.app (op (P (n + 1))) (t (n + 1))) := hn.symm
  rw [hn', hr]
  have hn₂ := NatTrans.naturality_apply (η.app (I n)).hom (p n).op (t n)
  have hn₂' : (η.app (I n)).hom.app (op (P (n + 1)))
      ((I n).obj.map (p n).op (t n)) =
      (F.obj (I n)).obj.map ((toProEt X).map (p n)).op
        ((η.app (I n)).hom.app (op (P n)) (t n)) := hn₂
  refine (congrArg ((F.obj (I n)).obj.map (a j (n + 1)).op) hn₂').trans ?_
  rw [← Functor.map_comp_apply, ← op_comp, hpa]

end AlgebraicGeometry.Scheme
