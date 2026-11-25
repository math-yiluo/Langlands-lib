/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.EtaleCoefficientInjectiveCokernelSystem
import WeilConjectures.AlgebraicGeometry.EtaleSystemConeFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Compatible short exact systems of etale sheaves

Source: Stacks Project, Tags 0EXZ, 09YP and 0739.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Compatible stage short exact sequences and their limit sequence, in continuation form.
Source: Stacks Project, Tags 0EXZ and 09YP, construction of the injective system and
its cokernel; exactness of filtered sheaf colimits.
(blueprint: lem-weil-pbc-etale-limit-compatible-exact-systems).

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
complexes. More explicitly, transport the pulled-back embeddings and quotients
through eG, eGI and eGR to natural transformations between the three diagrams.
The coefficient squares and the cone comparisons prove their naturality. Their
composite is zero objectwise. Exact inverse image gives stagewise short exactness,
hence objectwise exactness gives a short exact sequence in the functor category.
Apply the exact filtered colimit functor. Identify colimit G with the supplied
L.pt by the unique colimit isomorphism. Compose the three object-identification
inverses with the coprojections to obtain t. Naturality of the coprojections
and the definitions of the induced colimit maps prove its two squares.
The stage compatibility of the embedding and quotient makes the triples
(phi, psi, phiR) morphisms r of short complexes. The middle component of each
limit comparison t is the pulled-back middle coprojection, just as its outer
components are the prescribed coprojections. This is only the construction:
no vanishing or cohomology boundary is asserted. The product construction
works for a singleton index and zero or empty-scheme systems as well.
-/
theorem etale_limit_compatible_exact_systems
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
    (L : Cocone G) (hL : IsColimit L) (result : Prop)
    (continuation : ∀ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
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
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶ ShortComplex.mk a b w)
    (r : ∀ (i j : I) (f : i ⟶ j),
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (D.map f.op)) ⟶
      ShortComplex.mk (ai j) (bi j) (wi j)),
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₁ = φ f) ∧
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₂ = ψ f) ∧
      (∀ (i j : I) (f : i ⟶ j), (r i j f).τ₃ = φR f) ∧
      (∀ i : I, (t i).τ₂ = (eGI i).inv ≫ LI.ι.app i) ∧
      (∀ i : I, Injective (FI i)) ∧
      (∀ i : I, (t i).τ₁ = (eG i).inv ≫ L.ι.app i) ∧
      (∀ i : I, (t i).τ₃ = (eGR i).inv ≫ LR.ι.app i) → result) : result := by
  classical
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
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
  let r (i j : I) (f : i ⟶ j) :
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (D.map f.op)) ⟶
      ShortComplex.mk (ai j) (bi j) (wi j) :=
    { τ₁ := φ f
      τ₂ := ψ f
      τ₃ := φR f
      comm₁₂ := ha i j f
      comm₂₃ := hb i j f }
  let LI := colimit.cocone GI
  let LR := colimit.cocone GR
  let e : colimit G ≅ L.pt := (colimit.isColimit G).coconePointUniqueUpToIso hL
  let a : L.pt ⟶ LI.pt := e.inv ≫ colim.map α
  let b : LI.pt ⟶ LR.pt := colim.map β
  have wz : a ≫ b = 0 := by
    dsimp only [a, b]
    rw [Category.assoc, ← Functor.map_comp, w, Functor.map_zero, comp_zero]
  let S := ShortComplex.mk α β w
  have hex : (S.map (colim (J := I))).ShortExact := hShortExact.map_of_exact colim
  let E := ShortComplex.mk a b wz
  let eS : S.map (colim (J := I)) ≅ E :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simp [S, E, a]) (by simp [S, E, b])
  have hE : E.ShortExact := ShortComplex.shortExact_of_iso eS hex
  let q (i : I) : ShortComplex.mk (α.app i) (β.app i)
      (congrArg (fun f ↦ f.app i) w) ⟶ E :=
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
  apply continuation FR φR hidentityR hcompositionR GR eGR hGR LR
    (colimit.isColimit GR) FI ψ hidentityI hcompositionI GI eGI hGI LI
    (colimit.isColimit GI) a b wz hE ai bi wi hi (fun i ↦ s i ≫ q i) r
  exact ⟨(fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl),
    (fun _ ↦ rfl), hInjective, (fun _ ↦ rfl), (fun _ ↦ rfl)⟩

end AlgebraicGeometry.Etale
