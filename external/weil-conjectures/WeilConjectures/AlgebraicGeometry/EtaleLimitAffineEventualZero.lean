/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineDegreeZeroKernel
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineCorrectedLift

/-! # EtaleLimitAffineEventualZero

Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YP.
(blueprint: lem-weil-pbc-etale-limit-affine-eventual-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem cohomologyMap_comp_explicit {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = a ≫ b)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (x : Sheaf.H F p) :
    cohomologyMap a ((upperStar AddCommGrpCat.{u + 1} b).obj F) p
        (cohomologyMap b F p x) =
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b c hc).hom.app F) p
        (cohomologyMap c F p x) := by
  subst c
  exact (cohomologyPullbackFunctorial a b F p).2.1 x

set_option backward.isDefEq.respectTransparency false in
/-- The kernel half of affine-stage cohomology continuity.

Source: Stacks Project, Theorem 09YQ, via Lemmas 0EYL, 04HR and 09YP,
and the dimension-shifting argument of 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-eventual-zero).

Proof: Induct on the cohomological degree, generalizing the coefficient
system, its pullback diagram, its colimit cocone, and the initial stage.
The degree-zero kernel theorem gives the base case. In successor degree n+1,
the corrected-lift theorem supplies a cokernel coefficient system R with
natural additive connecting maps, and a degree-n class z at a later stage j.
The limit image of z is zero and its connecting image is the transition of x.
The induction hypothesis for R kills z after a transition j → k. Naturality
of the connecting maps then kills the successive transitions of x.
Cohomology pullback naturality, its composition comparison, and the supplied
coefficient composition law identify these successive transitions with the
single transition i → k. This gives the required witness.

The geometric base case and exact-ladder construction remain separate named
theorems. Corrected lifting uses finite-stage class descent only in degree n;
it does not invoke eventual detection of zero in that degree.

Edge cases: the index is nonempty; an empty scheme has zero cohomology; degree
zero is the section assertion. For a singleton system the assertion is
injectivity of that identification, with the identity transition.
-/
theorem etale_limit_affine_eventual_zero
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
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
    (i : I) (x : Sheaf.H (F i) p)
    (hx : Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p
      (cohomologyMap (c.π.app (op i)) (F i) p x) = 0) :
    ∃ (j : I) (f : i ⟶ j),
      Sheaf.H.map (φ f) p (cohomologyMap (D.map f.op) (F i) p x) = 0 := by
  induction p generalizing F φ G L i with
  | zero =>
    exact etale_limit_affine_degree_zero_kernel
      D c hc F φ hidentity hcomposition G eG hG L hL i x hx
  | succ n ih =>
    obtain ⟨R, ρ, hidR, hcompR, T, eT, hT, K, hK, δ, hδ, hlift⟩ :=
      etale_limit_affine_corrected_lift
        D c hc F φ hidentity hcomposition G eG hG L hL n
    obtain ⟨j, f, z, hz, hzx⟩ := hlift i x hx
    obtain ⟨k, g, hg⟩ := ih R ρ hidR hcompR T eT hT K hK j z hz
    refine ⟨k, f ≫ g, ?_⟩
    have hzero :
        Sheaf.H.map (φ g) (n + 1)
          (cohomologyMap (D.map g.op) (F j) (n + 1)
            (Sheaf.H.map (φ f) (n + 1)
              (cohomologyMap (D.map f.op) (F i) (n + 1) x))) = 0 := by
      rw [← hzx, ← hδ, hg, map_zero]
    rw [cohomologyMap_map, cohomologyMap_comp_explicit (D.map g.op)
      (D.map f.op) (D.map (f ≫ g).op) (D.map_comp g.op f.op)] at hzero
    rw [hcomposition]
    simp only [Sheaf.H.map_comp_apply]
    convert hzero using 1

end AlgebraicGeometry.Etale
