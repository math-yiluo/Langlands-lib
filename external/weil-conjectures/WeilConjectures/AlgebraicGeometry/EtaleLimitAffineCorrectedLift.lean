/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineExactLadder
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import Mathlib.CategoryTheory.Filtered.Final

/-! # Corrected lifts for the affine continuity kernel

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-corrected-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- A successor-degree zero-image class has a corrected preceding-degree lift.

Source: Stacks Project, Tag 09YP via the injective-system construction 0EXZ,
and the connecting-row argument of Tag 0739, transported by 0EYL and 04HR.
(blueprint: lem-weil-pbc-etale-limit-affine-corrected-lift).

Proof: Embed the compatible coefficient system F in an injective system E
using 0EXZ: at stage i use the product of the direct images of injective
embeddings of F_k over arrows i → k. The identity component is monic;
exact inverse image implies that direct image preserves injectives. Take
stage cokernels R. Exact inverse images and cancellation of cokernel epis
give the identity and composition laws of ρ. Pull R to the limit to form T,
with its canonical inverse-image comparisons, and take its sheaf colimit K.
Filtered sheaf colimits are exact, giving the short exact limit sequence.
The stage connecting homomorphisms δ map H^n(R_i) to H^(n+1)(F_i).
Naturality of Ext connecting maps under exact inverse image and under
coefficient maps gives the displayed transition square for every arrow.

For x with zero limit image, stage injectivity of E_i makes the connecting
map surjective, so lift x to z₀ in H^n(R_i). The limit image of z₀ is killed
by the limit connecting map, hence is the image of a class w in H^n of the
colimit of the pulled-back E system, by exactness of the limit long exact
sequence. Apply degree-n class descent (etale_limit_cohomology_class_descent)
to E. It uses existence only and does not depend on the eventual-zero theorem.
It represents w at some stage k. Directedness gives a common stage j ≥ i,k.
Transition z₀ and this representative to j and subtract the image of the
E_j class from the R_j class, producing z. Cocone naturality and the equality
representing w show that z has exactly zero limit image. The connecting map
kills the E_j image by exactness, so δ_j(z) is the transition of x.
This construction proves the final lifting assertion without detecting zero
in degree n or assuming any successor-degree continuity.

For n=0 the same argument uses the ordinary H⁰ connecting map. Zero systems
and empty schemes give zero homomorphisms; a singleton index uses exactness
of its two long exact sequences. The existential data are used only inside
proofs: no object is defined by choosing an undetermined existence witness.
-/
theorem etale_limit_affine_corrected_lift
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
    (L : Cocone G) (hL : IsColimit L)
    (n : ℕ) :
    ∃ (R : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ρ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (R i) ⟶ R j)
    (_hidentityR : ∀ i : I, ρ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (R i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (R i))
    (_hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ρ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ρ f) ≫ ρ g)
    (T : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eT : ∀ i : I, T.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (R i))
    (_hT : ∀ (i j : I) (f : i ⟶ j), T.map f =
      (eT i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ρ f) ≫ (eT j).inv)
    (K : Cocone T) (_hK : IsColimit K)
    (δ : ∀ k : I, Sheaf.H (R k) n →+ Sheaf.H (F k) (n + 1)),
      (∀ (j k : I) (g : j ⟶ k) (z : Sheaf.H (R j) n),
        δ k (Sheaf.H.map (ρ g) n (cohomologyMap (D.map g.op) (R j) n z)) =
          Sheaf.H.map (φ g) (n + 1)
            (cohomologyMap (D.map g.op) (F j) (n + 1) (δ j z))) ∧
      (∀ (i : I) (x : Sheaf.H (F i) (n + 1)),
        Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1)
          (cohomologyMap (c.π.app (op i)) (F i) (n + 1) x) = 0 →
        ∃ (j : I) (f : i ⟶ j) (z : Sheaf.H (R j) n),
          Sheaf.H.map ((eT j).inv ≫ K.ι.app j) n
            (cohomologyMap (c.π.app (op j)) (R j) n z) = 0 ∧
          δ j z = Sheaf.H.map (φ f) (n + 1)
            (cohomologyMap (D.map f.op) (F i) (n + 1) x)) := by
  classical
  apply etale_limit_affine_exact_ladder
    D c hc F φ hidentity hcomposition G eG hG L hL n
  intro E ψ hidE hcompE GE eGE hGE LE hLE HE eHE hHE BE eBE hBE
    R ρ hidR hcompR T eT hT K hK δ α α₀ β hrows
  rcases hrows with ⟨hsurj, hzero, hδ, hδsquare, hαsquare, hexact, htrans⟩
  refine ⟨R, ρ, hidR, hcompR, T, eT, hT, K, hK, δ, hδ, ?_⟩
  intro i x hx
  obtain ⟨z₀, hz₀⟩ := hsurj i x
  have hβz : β (Sheaf.H.map ((eT i).inv ≫ K.ι.app i) n
      (cohomologyMap (c.π.app (op i)) (R i) n z₀)) = 0 := by
    rw [hδsquare, hz₀, hx]
  obtain ⟨w, hw⟩ := hexact _ hβz
  obtain ⟨k, v, hv⟩ := etale_limit_cohomology_class_descent
    D c hc E ψ hidE hcompE GE eGE hGE LE hLE n HE eHE hHE BE eBE hBE w
  let j := IsFiltered.max i k
  let f : i ⟶ j := IsFiltered.leftToMax i k
  let g : k ⟶ j := IsFiltered.rightToMax i k
  let v' := (HE.map g).hom v
  let z := Sheaf.H.map (ρ f) n (cohomologyMap (D.map f.op) (R i) n z₀) - α j v'
  refine ⟨j, f, z, ?_, ?_⟩
  · dsimp only [z]
    rw [map_sub, map_sub, htrans, hαsquare]
    have hv' : (BE.ι.app j).hom v' = w := by
      calc
        (BE.ι.app j).hom v' = (BE.ι.app k).hom v :=
          ConcreteCategory.congr_hom (BE.w g) v
        _ = w := hv
    rw [hv', hw, sub_self]
  · dsimp only [z]
    rw [map_sub, hδ, hzero, sub_zero, hz₀]


end AlgebraicGeometry.Etale
