/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.AffineEtaleBaseChangeGeometry
import WeilConjectures.AlgebraicGeometry.AffineEtaleCartesianSheafAdjunction
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# AffineEtaleBaseChangeSystem

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-base-change-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL, qcqs case; Topologies 04HR.

Proof (steps 1--4 of lem-weil-pbc-affine-etale-site-colimit):
1. The cone projections are affine by uniqueness of limits and
   lem-weil-pbc-limit-affine-transition. Affine morphism permanence makes base change
   preserve affine objects; étaleness is stable under base change.
2. Choose identity functors on diagonal indices, ordinary restricted base change on
   other indices, and base change along the cone projections for v. The first projections
   give natural transformations p and q. For diagonal indices use the identity projection.
3. Pullback pasting and uniqueness give natural comparisons gamma and delta compatible
   with the first projections. Use identity comparisons on diagonal indices. Both sides
   of every cocycle have the same two projections, hence agree by pullback uniqueness.
4. Base change preserves finite jointly surjective étale coverings and all pullbacks.
   This gives continuity. Restriction to the affine site is a sheaf equivalence (04HR).
   Conjugate small-site inverse image by these equivalences to obtain the displayed
   adjunctions and finite-limit preservation for sheaves of Type u. The construction is
   coefficient-universe independent; equivalences preserve finite limits.
(blueprint: lem-weil-pbc-affine-etale-base-change-system). -/
theorem exists_affineEtale_baseChange_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) :
    ∃ (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i),
      (∀ i : I, U i i le_rfl = 𝟭 _)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
      ∧ (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((gamma i j k h h').hom.app A).hom.left ≫ (p i k (h.trans h')).app A =
          (p j k h').app ((U i j h).obj A) ≫ (p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A)
      ∧ (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
            (gamma i j l h (h'.trans h'')).hom.app A =
          (U k l h'').map ((gamma i j k h h').hom.app A) ≫
            (gamma i k l (h.trans h') h'').hom.app A)
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (v k).map ((gamma i j k h h').hom.app A) ≫
            (delta i k (h.trans h')).hom.app A =
          (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((U i j h).obj A))
      ∧ (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (U i j h))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (v i) ∈ fullAffineEtalePrecoverage c.pt ((v i).obj A))
      ∧ (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (v i))
      ∧ (∃ (_ : ∀ (i j : I) (h : i ≤ j), (U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
        (_ : ∀ i : I, (v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)),
        (∀ (i j : I) (h : i ≤ j), ∃ L :
            Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
              Sheaf (fullAffineEtaleTopology (D.obj (op j))) (Type u),
          Nonempty (L ⊣ (U i j h).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i)))
            (fullAffineEtaleTopology (D.obj (op j)))) ∧ PreservesFiniteLimits L) ∧
        (∀ i : I, ∃ L : Sheaf (fullAffineEtaleTopology (D.obj (op i))) (Type u) ⥤
            Sheaf (fullAffineEtaleTopology c.pt) (Type u),
          Nonempty (L ⊣ (v i).sheafPushforwardContinuous (Type u)
            (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt)) ∧
          PreservesFiniteLimits L)) := by
  obtain ⟨d, hd⟩ := exists_affineEtale_baseChange_geometry D c hc
  rcases hd with ⟨hid, hp, hq, hγl, hγr, hδ, hγp, hδp, hγc, hδc,
    hUc, hUp, hvc, hvp, hUcont, hvcont⟩
  refine ⟨d.U, d.v, d.p, d.q, d.gamma, d.delta, hid, hp, hq, hγl, hγr, hδ,
    hγp, hδp, hγc, hδc, hUc, hUp, hvc, hvp, hUcont, hvcont, ?_, ?_⟩
  · intro i j h
    have := hUcont i j h
    exact affineEtale_cartesian_sheafAdjunction (D.map (homOfLE h).op)
      (d.U i j h) (d.p i j h) (hp i j h)
  · intro i
    have := hvcont i
    have := AlgebraicGeometry.isAffineHom_π_app D c hc (op i)
    exact affineEtale_cartesian_sheafAdjunction (T := c.pt) (c.π.app (op i))
      (d.v i) (d.q i) (hq i)

end AlgebraicGeometry.Scheme
