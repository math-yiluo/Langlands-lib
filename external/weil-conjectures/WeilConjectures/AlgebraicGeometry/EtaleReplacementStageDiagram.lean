/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory

import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveCokernelSystem
import WeilConjectures.AlgebraicGeometry.EtaleSystemConeFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # The stage diagram of an étale injective replacement

Source: Stacks Project, Tags 0EXZ and 04JC.
(blueprint: lem-weil-pbc-etale-replacement-stage-diagram).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

-- The existential proof binders in the unchanged interface are used by later witnesses.
set_option linter.unusedVariables false in
/-- Compatible injective and cokernel systems, assembled into a short exact diagram
on the cone point, before taking any filtered colimit.
Source: Stacks Project, Tag 0EXZ, its product-of-direct-images construction, and
Tag 04JC for exact inverse image.
(blueprint: lem-weil-pbc-etale-replacement-stage-diagram).

Proof: At every k use Injective.under (F k) and its canonical monomorphism.
At i form the product of their direct images over the arrows i to k. Transpose
coefficient transitions through the inverse-image/direct-image adjunction to
obtain the embedding. The identity component proves monicity. Exact inverse
image implies that direct image preserves injectives, and products of injectives
are injective. Reindexing the products defines the transition maps; adjunction
naturality and the inverse-image associativity and unit comparisons prove the
system laws and compatibility of the embeddings. Set FR i to the cokernel of
the embedding. Preservation of cokernels by inverse image defines its transitions;
cancel the epic cokernel projections to prove their identity and composition laws.
Pull both systems to the cone point, using the cone equation and upperStarComp
to define the functor arrows. The same unit and associativity equations prove
the functor laws. Transport the pulled-back embedding and quotient through eG,
eGI and eGR; compatibility makes them natural transformations α and β. Their
composite is zero by stagewise exactness. Each transported sequence is short
exact because inverse image is exact; kernels and cokernels in the functor
category are evaluated objectwise, so their short complex is short exact.
The inverse objectwise identifications define the displayed morphisms s; their
commutation equations are the definitions of α and β. Their first and third
components are eG.inv and eGR.inv. No colimit or exact limit sequence is asserted.
-/
theorem etale_replacement_stage_diagram
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
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
 :
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
    (ai : ∀ i : I, F i ⟶ FI i) (bi : ∀ i : I, FI i ⟶ FR i)
    (wi : ∀ i : I, ai i ≫ bi i = 0)
    (hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact)
    (α : G ⟶ GI) (β : GI ⟶ GR) (w : α ≫ β = 0)
    (s : ∀ i : I,
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶
      (ShortComplex.mk (α.app i) (β.app i) (congrArg (fun f ↦ f.app i) w))),
      (∀ i : I, Injective (FI i)) ∧
      (ShortComplex.mk α β w).ShortExact ∧
      (∀ i : I, (s i).τ₁ = (eG i).inv) ∧
      (∀ i : I, (s i).τ₃ = (eGR i).inv) := by
  obtain ⟨FR, φR, hidentityR, hcompositionR, FI, ψ, hidentityI, hcompositionI,
    ai, bi, wi, hi, hInjective, ha, hb⟩ :=
    etale_coefficient_injective_cokernel_system D F φ hidentity hcomposition
  obtain ⟨GI, eGI, hGI⟩ :=
    etale_system_cone_functor D c FI ψ hidentityI hcompositionI
  obtain ⟨GR, eGR, hGR⟩ :=
    etale_system_cone_functor D c FR φR hidentityR hcompositionR
  let α : G ⟶ GI :=
    { app := fun i ↦ (eG i).hom ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).map (ai i) ≫ (eGI i).inv
      naturality := by
        intro i j f
        dsimp
        rw [hG, hGI]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Functor.map_comp_assoc, ha i j f, Functor.map_comp]
        have hn := (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j))
          (D.map f.op) (c.π.app (op i)) (c.w f.op).symm).hom.naturality (ai i)
        dsimp at hn
        simp only [Category.assoc]
        rw [← reassoc_of% hn] }
  let β : GI ⟶ GR :=
    { app := fun i ↦ (eGI i).hom ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).map (bi i) ≫ (eGR i).inv
      naturality := by
        intro i j f
        dsimp
        rw [hGI, hGR]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Functor.map_comp_assoc, hb i j f, Functor.map_comp]
        have hn := (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j))
          (D.map f.op) (c.π.app (op i)) (c.w f.op).symm).hom.naturality (bi i)
        dsimp at hn
        simp only [Category.assoc]
        rw [← reassoc_of% hn] }
  have w : α ≫ β = 0 := by
    apply NatTrans.ext
    funext i
    dsimp [α, β]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, wi,
      Functor.map_zero, comp_zero, zero_comp]
  let s : ∀ i : I,
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶
      ShortComplex.mk (α.app i) (β.app i) (congrArg (fun f ↦ f.app i) w) :=
    fun i ↦
      { τ₁ := (eG i).inv
        τ₂ := (eGI i).inv
        τ₃ := (eGR i).inv
        comm₁₂ := by simp [α]
        comm₂₃ := by simp [β] }
  have hComponents : ∀ i : I,
      (ShortComplex.mk (α.app i) (β.app i)
        (congrArg (fun f ↦ f.app i) w)).ShortExact := by
    intro i
    have : IsIso (s i).τ₁ := by dsimp [s]; infer_instance
    have : IsIso (s i).τ₂ := by dsimp [s]; infer_instance
    have : IsIso (s i).τ₃ := by dsimp [s]; infer_instance
    have : IsIso (s i) := ShortComplex.isIso_of_isIso (s i)
    exact ShortComplex.shortExact_of_iso (asIso (s i))
      ((hi i).map_of_exact (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))))
  have hEval : JointlyReflectIsomorphisms
      (fun i : I ↦ (evaluation I
        (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})).obj i) :=
    { isIso := by
        intro X Y f hf
        have : ∀ i, IsIso (f.app i) := hf
        exact NatIso.isIso_of_isIso_app f }
  have hShortExact : (ShortComplex.mk α β w).ShortExact := by
    apply (hEval.shortExact_iff _).mpr
    intro i
    exact hComponents i
  exact ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR,
    FI, ψ, hidentityI, hcompositionI, GI, eGI, hGI, ai, bi, wi, hi,
    α, β, w, s, hInjective, hShortExact, (fun _ ↦ rfl), (fun _ ↦ rfl)⟩

end AlgebraicGeometry.Etale
