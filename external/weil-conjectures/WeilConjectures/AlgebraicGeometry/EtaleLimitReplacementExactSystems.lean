/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

import WeilConjectures.AlgebraicGeometry.EtaleReplacementStageDiagram
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # Etale replacement: construction and vanishing

Source: Stacks Project, Tags 0EXZ, 09YP, 09YN and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Compatible stage short exact sequences and their limit sequence.
Source: Stacks Project, Tags 0EXZ and 09YP, construction of the injective system and
its cokernel; exactness of filtered sheaf colimits.
(blueprint: lem-weil-pbc-etale-limit-replacement-exact-systems).

Proof: For each k take the canonical injective embedding F_k into Injective.under F_k.
At i take the product of the direct images of these injectives over all arrows i to k.
The adjunction transposes the coefficient transitions into product components. The
identity component makes the induced embedding monic. Exact inverse image makes each
factor injective and products preserve injectivity. Composition of arrows defines the
product transitions; the canonical adjunction comparisons prove the identity and
composition laws. Take the actual stage cokernels of the embeddings. Exact inverse
image preserves their cokernel property, so cancelling the quotient epimorphisms proves
the quotient transition laws. Pull all three systems to X using the cone comparisons,
then take their actual filtered colimits. Exact filtered sheaf colimits give the limit
short exact sequence. The stage coprojections induce the displayed morphisms of short
complexes, whose first and third components are precisely the prescribed comparisons.
This is only the construction: no vanishing or cohomology boundary is asserted.
-/
theorem etale_limit_replacement_exact_systems
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
    (L : Cocone G) (hL : IsColimit L) :
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
    (FI : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (GI : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGI : ∀ i : I, GI.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FI i))
    (hGI : ∀ (i j : I) (f : i ⟶ j), GI.map f =
      (eGI i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ψ f) ≫ (eGI j).inv)
    (LI : Cocone GI) (hLI : IsColimit LI)
    (a : L.pt ⟶ LI.pt) (b : LI.pt ⟶ LR.pt) (w : a ≫ b = 0)
    (hE : (ShortComplex.mk a b w).ShortExact)
    (ai : ∀ i : I, F i ⟶ FI i) (bi : ∀ i : I, FI i ⟶ FR i)
    (wi : ∀ i : I, ai i ≫ bi i = 0)
    (hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact)
    (t : ∀ i : I,
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶ ShortComplex.mk a b w),
      (∀ i : I, Injective (FI i)) ∧
      (∀ i : I, (t i).τ₁ = (eG i).inv ≫ L.ι.app i) ∧
      (∀ i : I, (t i).τ₃ = (eGR i).inv ≫ LR.ι.app i)
    := by
  classical
  have _ := hc
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  obtain ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR,
    FI, ψ, hidentityI, hcompositionI, GI, eGI, hGI,
    ai, bi, wi, hi, α, β, wz, s, hinj, hS, hs₁, hs₃⟩ :=
    etale_replacement_stage_diagram D c F φ hidentity hcomposition G eG hG
  let LI := colimit.cocone GI
  let LR := colimit.cocone GR
  let e : colimit G ≅ L.pt := (colimit.isColimit G).coconePointUniqueUpToIso hL
  let a : L.pt ⟶ LI.pt := e.inv ≫ colim.map α
  let b : LI.pt ⟶ LR.pt := colim.map β
  have w : a ≫ b = 0 := by
    dsimp only [a, b]
    rw [Category.assoc, ← Functor.map_comp, wz, Functor.map_zero, comp_zero]
  let S := ShortComplex.mk α β wz
  have hex : (S.map (colim (J := I))).ShortExact := hS.map_of_exact colim
  let E := ShortComplex.mk a b w
  let eS : S.map (colim (J := I)) ≅ E :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simp [S, E, a]) (by simp [S, E, b])
  have hE : E.ShortExact := ShortComplex.shortExact_of_iso eS hex
  let q (i : I) : ShortComplex.mk (α.app i) (β.app i)
      (congrArg (fun f ↦ f.app i) wz) ⟶ E :=
    { τ₁ := L.ι.app i
      τ₂ := colimit.ι GI i
      τ₃ := colimit.ι GR i
      comm₁₂ := by
        dsimp only [E, a, ShortComplex.mk]
        have he : L.ι.app i = colimit.ι G i ≫ e.hom := by simp [e]
        rw [he]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, colimit.ι_map]
      comm₂₃ := by
        dsimp only [E, b, ShortComplex.mk]
        exact colimit.ι_map β i }
  refine ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR,
    colimit.isColimit GR, FI, ψ, hidentityI, hcompositionI, GI, eGI, hGI, LI,
    colimit.isColimit GI, a, b, w, hE, ai, bi, wi, hi,
    fun i ↦ s i ≫ q i, hinj, ?_, ?_⟩
  · intro i
    change (s i).τ₁ ≫ L.ι.app i = _
    rw [hs₁]
  · intro i
    change (s i).τ₃ ≫ colimit.ι GR i = _
    rw [hs₃]
    rfl

end AlgebraicGeometry.Etale
