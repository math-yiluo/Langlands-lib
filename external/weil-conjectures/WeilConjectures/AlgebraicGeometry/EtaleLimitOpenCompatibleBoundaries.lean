/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisCanonicalBoundaryExact
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisCanonicalBoundaryNaturality

/-! # Compatible boundaries on the actual stage and limit cohomology groups

Source: Stacks Project, Tags 0A50 and 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-compatible-boundaries).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar cohomologyMap
  openCohomologyRestriction openSquareCoefficient
  Sheaf.H.map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Choose exact Mayer--Vietoris boundaries compatible with all stage maps and legs.

Source: Stacks Project, Tag 0A50, functorial long exact sequence of an injective
resolution, and Tag 09YQ, coherent-system restriction maps.
(blueprint: lem-weil-pbc-etale-limit-open-compatible-boundaries).

Proof: The value hypotheses identify the supplied additive difference maps
with the actual differences of restrictions, by extensionality. Fix injective
resolutions for the coefficient sheaves on every stage and
on c.pt. Sections on the two covering opens and their intersection form short
exact sequences of complexes. Use their homology connecting maps and transport
through the comparisons with Sheaf.H. For each transition, pull back the stage
resolution and lift the coefficient map φ into the target resolution. The maps
on sections commute with restriction, hence give a morphism of the short exact
complex sequences. Homology connecting-map naturality identifies the induced
intersection map followed by the target boundary with the source boundary
followed by whole-scheme pullback and coefficient cohomology. The comparison
with Sheaf.H gives exactly tailOpenCohomologyMapDegree, including its inverse
image composition comparison. Repeat for each cone projection and coefficient
(eG j).inv ≫ L.ι.app j to obtain the leg equation. This construction uses the
same resolution boundaries for all arrows; choosing existential boundaries
separately for each arrow would not suffice. Long exactness gives both stage
exactness assertions and bottom exactness. Inverse image preserves intersections,
so the intersection term is the inverse image of U∩V used here. No directedness,
identity/composition condition on φ, or formula for G.map is used. Empty or
coincident covering opens give the same exact section complexes. The existential
boundaries are used in proofs only, never to define unspecified data. -/
theorem tailOpenCompatibleBoundaries
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ) (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X)
    (d : ∀ j : Set.Ici i₀,
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ U j).ι).obj
        (F j.val)) q ×
       Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ V j).ι).obj
        (F j.val)) q) →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ (U ⊓ V) j).ι).obj
        (F j.val)) q)
    (dL : (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) q ×
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) q) →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)).ι).obj L.pt) q)
    (hd : (∀ j x, d j x =
      openCohomologyRestriction (X := D.obj (op j.val))
        (A := tailStageOpen D g₀ (U ⊓ V) j) (B := tailStageOpen D g₀ U j)
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono
          (inf_le_left : U ⊓ V ≤ U)) (F j.val) q x.1 -
      openCohomologyRestriction (X := D.obj (op j.val))
        (A := tailStageOpen D g₀ (U ⊓ V) j) (B := tailStageOpen D g₀ V j)
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono
          (inf_le_right : U ⊓ V ≤ V)) (F j.val) q x.2))
    (hdL : (∀ x, dL x =
      openCohomologyRestriction (X := c.pt)
        (A := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V))
        (B := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U)
        ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_left : U ⊓ V ≤ U)) L.pt q x.1 -
      openCohomologyRestriction (X := c.pt)
        (A := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V))
        (B := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V)
        ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_right : U ⊓ V ≤ V)) L.pt q x.2))
    (hstageCover : ∀ j : Set.Ici i₀,
      tailStageOpen D (X := X) (i₀ := i₀) g₀ U j ⊔ tailStageOpen D (X := X) (i₀ := i₀) g₀ V j = ⊤)
    (hlimitCover : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ⊔
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V) = ⊤) :
    ∃ (δ : ∀ j : Set.Ici i₀, Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D (X := X) (i₀ := i₀) g₀ (U ⊓ V) j).ι).obj
          (F j.val)) q →+ Sheaf.H (F j.val) (q + 1))
      (δL : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)).ι).obj L.pt) q →+
          Sheaf.H L.pt (q + 1)),
      (∀ j, Function.Exact (d j) (δ j)) ∧
      (∀ j, Function.Exact (δ j) (fun x ↦
        (cohomologyMap (tailStageOpen D (X := X) (i₀ := i₀) g₀ U j).ι (F j.val) (q + 1) x,
          cohomologyMap (tailStageOpen D (X := X) (i₀ := i₀) g₀ V j).ι (F j.val) (q + 1) x))) ∧
      Function.Exact dL δL ∧
      (∀ (j k : Set.Ici i₀) (f : j ⟶ k)
        (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (tailStageOpen D (X := X) (i₀ := i₀) g₀ (U ⊓ V) j).ι).obj (F j.val)) q),
        δ k ((tailOpenCohomologyMapDegree D (X := X) (i₀ := i₀) g₀ (U ⊓ V) F φ q f).hom x) =
        Sheaf.H.map (φ (homOfLE (show j.val ≤ k.val from f.le))) (q + 1)
          (cohomologyMap (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
            (F j.val) (q + 1) (δ j x))) ∧
      (∀ (j : Set.Ici i₀)
        (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (tailStageOpen D (X := X) (i₀ := i₀) g₀ (U ⊓ V) j).ι).obj (F j.val)) q),
        δL ((tailOpenCohomologyLegDegree D c (X := X) (i₀ := i₀) g₀ (U ⊓ V) F G eG L q j).hom x) =
        Sheaf.H.map ((eG j.val).inv ≫ L.ι.app j.val) (q + 1)
          (cohomologyMap (c.π.app (op j.val)) (F j.val) (q + 1) (δ j x))) := by
  have hI (j : Set.Ici i₀) : tailStageOpen D g₀ (U ⊓ V) j =
      tailStageOpen D g₀ U j ⊓ tailStageOpen D g₀ V j :=
    (D.map (homOfLE j.property).op ≫ g₀).preimage_inf
  have hIL : (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V) =
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ⊓ ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V) :=
    (c.π.app (op i₀) ≫ g₀).preimage_inf
  let δ := fun (j : Set.Ici i₀) ↦ etaleMayerVietorisFixedBoundary
    (tailStageOpen D g₀ U j) (tailStageOpen D g₀ V j) (tailStageOpen D g₀ (U ⊓ V) j)
    (hI j) (hstageCover j) (F j.val) q
  let δL := etaleMayerVietorisFixedBoundary
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V)
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)) hIL hlimitCover L.pt q
  have hs := fun (j : Set.Ici i₀) ↦
    etaleMayerVietorisFixedBoundary_exact
      (tailStageOpen D g₀ U j) (tailStageOpen D g₀ V j) (tailStageOpen D g₀ (U ⊓ V) j)
      (hI j) (hstageCover j) (F j.val) q
      ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono (inf_le_left : U ⊓ V ≤ U))
      ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono (inf_le_right : U ⊓ V ≤ V))
      (d j) (hd j)
  have hl :=
    (etaleMayerVietorisFixedBoundary_exact
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V)
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)) hIL hlimitCover L.pt q
      ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_left : U ⊓ V ≤ U))
      ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_right : U ⊓ V ≤ V)) dL hdL).1
  refine ⟨δ, δL, (fun j ↦ (hs j).1), (fun j ↦ (hs j).2), hl, ?_, ?_⟩
  · intro j k f x
    have hopen (W : X.Opens) : tailStageOpen D g₀ W k =
        (D.map (homOfLE (show j.val ≤ k.val from f.le)).op) ⁻¹ᵁ
          (tailStageOpen D g₀ W j) := by
      dsimp only [tailStageOpen]
      rw [← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]
      rfl
    have h := etaleMayerVietorisFixedBoundary_naturality
      (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
      (tailStageOpen D g₀ U j) (tailStageOpen D g₀ V j) (tailStageOpen D g₀ (U ⊓ V) j)
      (tailStageOpen D g₀ U k) (tailStageOpen D g₀ V k) (tailStageOpen D g₀ (U ⊓ V) k)
      (hI j) (hI k) (hstageCover j) (hstageCover k) (hopen U) (hopen V)
      (tailStageOpenMap D g₀ (U ⊓ V) f)
      (by exact (Scheme.Hom.resLE_comp_ι _ _).symm)
      (F j.val) (F k.val) (φ (homOfLE (show j.val ≤ k.val from f.le)))
      q x
    exact h
  · intro j x
    have hopen (W : X.Opens) : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W) =
        (c.π.app (op j.val)) ⁻¹ᵁ (tailStageOpen D g₀ W j) := by
      dsimp only [tailStageOpen]
      rw [← Scheme.Hom.comp_preimage, ← Category.assoc, c.w]
    have h := etaleMayerVietorisFixedBoundary_naturality
      (c.π.app (op j.val))
      (tailStageOpen D g₀ U j) (tailStageOpen D g₀ V j) (tailStageOpen D g₀ (U ⊓ V) j)
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V)
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V))
      (hI j) hIL (hstageCover j) hlimitCover (hopen U) (hopen V)
      (tailLimitOpenMap D c g₀ (U ⊓ V) j)
      (by exact (Scheme.Hom.resLE_comp_ι _ _).symm)
      (F j.val) L.pt ((eG j.val).inv ≫ L.ι.app j.val)
      q x
    exact h

end AlgebraicGeometry.Etale
