/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
import WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction

/-! # Coordinate trace contractions on ordinary unbounded etale derived categories

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, both triangle computations before diagonal integration.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

private theorem cancel_coordinate
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {S V Q B M N : C} {Z : D}
    (p : Z ≅ F.obj V) (c : S ≅ V) (q : Q ≅ B)
    (path : F.obj S ⟶ F.obj B) (r : Z ⟶ F.obj N)
    (b : N ⟶ Q) (a : Q ⟶ M) (e : Z ⟶ F.obj M)
    (hf : p.hom ≫ F.map c.inv ≫ path = r ≫ F.map (b ≫ q.hom))
    (hn : r ≫ F.map (b ≫ a) = e) :
    F.map c.hom ≫ p.inv ≫ e = path ≫ F.map (q.inv ≫ a) := by
  apply (cancel_epi (p.hom ≫ F.map c.inv)).1
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id,
    F.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  rw [← hn]
  rw [reassoc_of% hf]
  simp only [← F.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two coordinate contraction equations for an even shifted etale line.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the two triangle computations
(auxiliary; not a blueprint node).

Proof plan:
1. A finite ring is additive torsion. Properness is stable under base change, so
   lem-weil-pbc-proper-base-change, proposition-proper-direct-image-constructible-complexes--9 and
   lem-kun-proper-base-change-torsion-ring make all the indicated projection and
   exchange maps invertible on arbitrary unbounded objects. The normalized signed
   tensor, unit and adjunction compositors are those of
   lem-sfb-ringed-derived-monoidal-comparisons.
2. Apply lem-sfb-ringed-kunneth-factorizations to the self-product with N=f*L.
   Its two expressions give a common isomorphism J_M from FM tensor F(f*L) to
   FRp2*(p1*M tensor L_W). Its factors are precisely the displayed exchanges and
   ordered projections, conjugated by the specified tensor symmetries.
3. Precompose the first equation with J_M. On the left inverse comparison and
   inverse projection cancel, leaving 1 tensor t. On the right the other
   factorization cancels inverse p1 projection; ht1 replaces t1 beta1 by f*t.
   Projection naturality and its unit normalization give the same 1 tensor t.
   Use lem-sfb-ringed-projection-tensor-composition and
   situation-conventions, then cancel J_M.
4. A sheaf line has exact tensor by lem-pur-sheaf-line-evaluation-inverse-pair.
   Its even shifted one-term model is K-flat with flat terms. The symmetry on its
   self-tensor is the ordinary line swap times (-1)^(4*d*d), hence identity.
   This is an equality of sheaf maps checked on trivializing slices, then passed
   through lem-weil-pbc-site-derived-tensor-descent; no claim that arbitrary
   derived morphisms are detected by a cover is used.
5. Apply lem-weil-pbc-ringed-exchange-tensor-coherence. Invert its square and use
   ht2 to obtain f*(e_K) beta2(HK)^(-1) = (1 tensor t2) pi_p2^(-1).
6. Tensor this equation with f*L. The associativity formula of
   lem-sfb-ringed-projection-tensor-composition rearranges the two extractions.
   The self-symmetry from step 4 is identity. Symmetry naturality with respect to
   t2 yields the second equation, with coordinateH and all unitors as written.
The definitions are natural in M and K, and no diagonal class is used. -/
theorem contractions [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (d : ℤ)
    (t : (push A f).obj ((pull A f).obj (shiftedLine A J d)) ⟶ constantComplex A Y)
    (t1 : (push A (pullback.fst f f)).obj
        ((pull A (pullback.snd f f)).obj ((pull A f).obj (shiftedLine A J d))) ⟶
          constantComplex A X)
    (t2 : (push A (pullback.snd f f)).obj
        ((pull A (pullback.snd f f)).obj ((pull A f).obj (shiftedLine A J d))) ⟶
          constantComplex A X)
    (ht1 : (exchange1 A f ((pull A f).obj (shiftedLine A J d))).hom ≫ t1 =
        (pull A f).map t ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (ht2 : (exchange2 A f ((pull A f).obj (shiftedLine A J d))).hom ≫
          (push A (pullback.snd f f)).map (coordinate A f (shiftedLine A J d)).hom ≫ t2 =
        (pull A f).map t ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom) :
      (∀ M : DerivedCategoryModule A X,
        (push A f).map (comparison A f (shiftedLine A J d) M).hom ≫
            evaluation A f (shiftedLine A J d) t
              ((push A f).obj M) =
          (directComparison A f).hom.app _ ≫
            (push A f).map ((orderedProjectionIso A (pullback.fst f f) M
              ((pull A (pullback.snd f f)).obj ((pull A f).obj (shiftedLine A J d)))).inv ≫
                ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map t1 ≫
                  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom)) ∧
      (∀ K : DerivedCategoryModule A Y,
        (comparison A f (shiftedLine A J d) ((H A f (shiftedLine A J d)).obj K)).hom ≫
            (H A f (shiftedLine A J d)).map
              (evaluation A f (shiftedLine A J d) t K) =
          (push A (pullback.snd f f)).map
              (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
                (coordinateH A f (shiftedLine A J d) K).hom).app
                  ((pull A (pullback.snd f f)).obj ((pull A f).obj (shiftedLine A J d)))) ≫
            (orderedProjectionIso A (pullback.snd f f) ((H A f (shiftedLine A J d)).obj K)
              ((pull A (pullback.snd f f)).obj ((pull A f).obj (shiftedLine A J d)))).inv ≫
                ((derivedTensor (ModuleCat.{u + 1} A) X).obj
                  ((H A f (shiftedLine A J d)).obj K)).map t2 ≫
                  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
                    ((H A f (shiftedLine A J d)).obj K)).hom) := by
  constructor
  · intro M
    let L := shiftedLine A J d
    let F := push A f
    let T := (derivedTensor (ModuleCat.{u + 1} A) X).obj M
    let p := orderedProjectionIso A f (F.obj M) ((pull A f).obj L)
    let c := comparison A f L M
    let q := orderedProjectionIso A (pullback.fst f f) M
      ((pull A (pullback.snd f f)).obj ((pull A f).obj L))
    let path := (directComparison A f).hom.app
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L)))
    let r := ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
      (F.obj ((pull A f).obj L))
    let b := T.map (exchange1 A f ((pull A f).obj L)).hom
    let a := T.map t1 ≫ (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom
    let e := ((derivedTensor (ModuleCat.{u + 1} A) Y).obj (F.obj M)).map t ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y (F.obj M)).hom
    have hf : p.hom ≫ F.map c.inv ≫ path = r ≫ F.map (b ≫ q.hom) :=
      coordinateKunnethFactorization_route_eq A f L M
    have hn : r ≫ F.map (b ≫ a) = e := by
      have h := projectionTraceNormalization A f M (F.obj ((pull A f).obj L)) t
      rw [← ht1] at h
      have hba : T.map ((exchange1 A f ((pull A f).obj L)).hom ≫ t1) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom = b ≫ a := by
        rw [T.map_comp]
        exact Category.assoc _ _ _
      change r ≫ F.map (T.map ((exchange1 A f ((pull A f).obj L)).hom ≫ t1) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom) = e at h
      rw [hba] at h
      exact h
    exact cancel_coordinate F p c q path r b a e hf hn
  · intro K
    exact secondCoordinateContraction A f (shiftedLine A J d)
      (evenLineSelfSymmetry A J hJ d) t t2 ht2 K

end AlgebraicGeometry.Etale.CoordinateTrace
