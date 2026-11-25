/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitAcyclicReplacement
import WeilConjectures.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Degree reduction for etale limit cohomology

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- A connecting-map ladder lowers a successor-degree descent problem by one.

Source: Stacks Project, Cohomology on Sites, proof of Tag 09YP via the
injective-system construction 0EXZ and dimension shifting 0739; Etale Cohomology
Tag 09YQ, using its affine-site reduction 0EYL and 04HR.
(blueprint: lem-weil-pbc-etale-limit-cohomology-connecting-ladder).

Proof: Choose injective embeddings F_k -> A_k. At stage i form the product
E_i of the direct images of A_k over all arrows i -> k, as in 0EXZ. Adjunction
transposes the composites of the coefficient transitions and these embeddings
to F_i -> E_i. The identity component makes this a monomorphism. The canonical
transition maps of these products give a compatible injective system: direct
image preserves injectives since inverse image is exact, and products of
injectives are injective. Take stage cokernels R_i. Exact inverse images and
cancellation of their epimorphisms give the identity and composition laws for R.
Pull the three systems to the limit. Exact filtered sheaf colimits give
0 -> L -> LE -> LR -> 0.

To prove positive global acyclicity of LE use only degree-zero continuity.
Take the basis of qcqs etale objects on the limit. Every such object, and each
finite affine covering of it, descends to a stage by 0EYL; cofinal tails leave
the limit and sheaf colimit unchanged. Every iterated covering fibre product
is qcqs. Degree-zero continuity applied to its descended inverse system
identifies its sections of LE with the filtered colimit of sections of E_i.
Finite products commute with these colimits, so the Cech complex of the
covering is the filtered colimit of its stage Cech complexes. Injective
stage sheaves have acyclic augmented Cech complexes (03AW); exact filtered
group colimits preserve positive acyclicity. Finite qcqs covers are cofinal,
so the Cech criterion (03F9) gives positive object cohomology vanishing on
the qcqs basis, in particular at the terminal object of the qcqs limit.
This proves global acyclicity without any successor-degree continuity.

The long exact sequence on the limit now makes the connecting map
H^n(LR) -> H^(n+1)(L) surjective. At each stage take the connecting map from the
short exact sequence F_i -> E_i -> R_i. Naturality of connecting maps for exact
inverse image, and then for the coprojections, gives the commuting square with
the limit connecting map. Define HR and BR from R in degree n, and transport the
connecting maps through eH and eB. Their square is the final displayed equation.
The new coefficient system has all the hypotheses needed for the degree-n
induction; the lemma asserts no descent for it. For n=0 use the ordinary H^0
connecting map. Empty schemes or zero systems give zero maps to the zero group,
which are surjective, and the construction is valid for a one-object index.
-/
theorem etale_limit_cohomology_connecting_ladder
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
    (L : Cocone G) (hL : IsColimit L) (n : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (n + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (n + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (n + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (n + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (n + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1))) :
    ∃ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φR : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FR i) ⟶ FR j)
    (hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g)
    (GR : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGR : ∀ i : I, GR.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FR i))
    (hGR : ∀ (i j : I) (f : i ⟶ j), GR.map f =
      (eGR i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φR f) ≫ (eGR j).inv)
    (LR : Cocone GR) (hLR : IsColimit LR)
    (HR : I ⥤ AddCommGrpCat.{u + 1})
    (eHR : ∀ i : I, HR.obj i ≅ AddCommGrpCat.of (Sheaf.H (FR i) n))
    (hHR : ∀ (i j : I) (f : i ⟶ j), HR.map f =
      (eHR i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (FR i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φR f) n) ≫ (eHR j).inv)
    (BR : Cocone HR) (eBR : BR.pt ≅ AddCommGrpCat.of (Sheaf.H LR.pt n))
    (hBR : ∀ i : I, BR.ι.app i ≫ eBR.hom =
      (eHR i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (FR i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eGR i).inv ≫ LR.ι.app i) n)),
      ∃ (δ : BR.pt ⟶ B.pt) (δstage : ∀ i : I, HR.obj i ⟶ H.obj i),
        Function.Surjective δ.hom ∧
        (∀ i : I, δstage i ≫ B.ι.app i = BR.ι.app i ≫ δ) := by
  classical
  obtain ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
      E, a, b, w, hE, d, hdformula, hacyclic, beta, hbeta⟩ :=
    etale_limit_acyclic_replacement
      D c hc F φ hidentity hcomposition G eG hG L hL n
  obtain ⟨HR, eHR, hHR, BR, eBR, hBR⟩ :=
    etale_limit_canonical_cohomology_diagram
      D c FR φR hidentityR hcompositionR GR eGR hGR LR n
  have hd : Function.Surjective d.hom := by
    let := hacyclic
    intro x
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hE x
      (Subsingleton.elim _ _) rfl
    exact ⟨y, (hdformula y).trans hy⟩
  let δ : BR.pt ⟶ B.pt := eBR.hom ≫ d ≫ eB.inv
  let δstage (i : I) : HR.obj i ⟶ H.obj i := (eHR i).hom ≫ beta i ≫ (eH i).inv
  refine ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
    HR, eHR, hHR, BR, eBR, hBR, δ, δstage, ?_, ?_⟩
  · have : Epi d := (AddCommGrpCat.epi_iff_surjective d).mpr hd
    exact (AddCommGrpCat.epi_iff_surjective δ).mp (by dsimp [δ]; infer_instance)
  · intro i
    apply (cancel_mono eB.hom).mp
    dsimp [δstage, δ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hB i]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc (BR.ι.app i), hBR i]
    simpa only [Category.assoc] using congrArg (fun z ↦ (eHR i).hom ≫ z) (hbeta i)


end AlgebraicGeometry.Etale
