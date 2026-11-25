/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyDegreeZeroDescent
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyConnectingLadder

/-! # Finite-stage representatives of limit cohomology classes

Source: Stacks Project, Tags 09YQ, 09YP, 09YN, 0EXZ and 0739.
(blueprint: lem-weil-pbc-etale-limit-cohomology-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Finite-stage representatives of limit cohomology classes.

Source: Stacks Project, Theorem 09YQ, via 09YP, using the degree-zero
section comparison 09YN and dimension shifting 0739.
(blueprint: lem-weil-pbc-etale-limit-cohomology-class-descent).

Proof: Induct on the degree, simultaneously for all coefficient systems and
all supplied cohomology diagrams and comparison cocones. In degree zero use
the finite-stage section comparison. In successor degree take the cokernel
coefficient system and its connecting-map ladder. The surjective limit
connecting map lifts the target class to the preceding degree for that system.
The induction hypothesis represents this lift at a stage. Apply that stage's
connecting map to its representative. The commuting square of the ladder,
followed by the two representative equalities, proves the required image
identity. The induction is on degree, not on the fixed coefficient sheaf;
it uses no assertion about detection of zero. Empty schemes and zero sheaves
are included in the two intermediate lemmas; degree zero needs no negative term.
-/
theorem etale_limit_cohomology_class_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)) :
    ∀ y : B.pt, ∃ (i : I) (x : H.obj i), (B.ι.app i).hom x = y := by
  induction p generalizing F φ G L H B with
  | zero =>
    exact etale_limit_cohomology_degree_zero_descent
      D c hc F φ hidentity hcomposition G eG hG L hL H eH hH B eB hB
  | succ n ih =>
    obtain ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
        HR, eHR, hHR, BR, eBR, hBR, δ, δstage, hδ, hcomm⟩ :=
      etale_limit_cohomology_connecting_ladder
        D c hc F φ hidentity hcomposition G eG hG L hL n H eH hH B eB hB
    intro y
    obtain ⟨z, hz⟩ := hδ y
    obtain ⟨i, x, hx⟩ := ih FR φR hidentityR hcompositionR GR eGR hGR LR hLR
      HR eHR hHR BR eBR hBR z
    refine ⟨i, (δstage i).hom x, ?_⟩
    calc
      (B.ι.app i).hom ((δstage i).hom x) = δ.hom ((BR.ι.app i).hom x) :=
        ConcreteCategory.congr_hom (hcomm i) x
      _ = y := by rw [hx, hz]

end AlgebraicGeometry.Etale
