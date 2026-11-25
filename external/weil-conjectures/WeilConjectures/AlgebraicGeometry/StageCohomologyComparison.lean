/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.Grp.Colimits
/-! # Certificates for comparison maps on specified stages

Source: Stacks Project, Tag 09YQ, comparison maps for coherent sheaf systems.
The closure under products and transport is the finite-cover bookkeeping used
with Tag 0A50. These certificates contain geometric data, not continuity proofs.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A comparison assembled from canonical cohomology comparisons with specified stages.

Source: Stacks Project, Tag 09YQ (theorem-colimit), comparison-map construction,
and Tag 0A50, finite direct sums in Mayer--Vietoris.
(blueprint: def-weil-pbc-stage-cohomology-comparison).

The system constructor records an actual scheme limit, coherent coefficient system,
sheaf colimit, and canonical cohomology cocone, with a stage in `allowed`.
It asserts no cohomology colimit property. Isomorphisms, composition and products
only transport these maps or assemble their finite direct sums. This is a proposition
about supplied maps, and chooses no object or morphism from an existence theorem. -/
inductive StageCohomologyComparison (allowed : Scheme.{u} → Prop) :
    {A B : AddCommGrpCat.{u + 1}} → (A ⟶ B) → Prop
  | iso {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) :
      StageCohomologyComparison allowed e.hom
  | comp {A B C : AddCommGrpCat.{u + 1}} {f : A ⟶ B} {g : B ⟶ C}
      (hf : StageCohomologyComparison allowed f)
      (hg : StageCohomologyComparison allowed g) :
      StageCohomologyComparison allowed (f ≫ g)
  | prod {A B C D : AddCommGrpCat.{u + 1}} {f : A ⟶ B} {g : C ⟶ D}
      (hf : StageCohomologyComparison allowed f)
      (hg : StageCohomologyComparison allowed g) :
      StageCohomologyComparison allowed (AddCommGrpCat.ofHom (f.hom.prodMap g.hom))
  | system
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
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    (S : Scheme.{u}) (hS : allowed S)
    (i₀ : I) (e : D.obj (op i₀) ≅ S) :
      StageCohomologyComparison allowed (colimit.desc H B)

end AlgebraicGeometry.Etale
