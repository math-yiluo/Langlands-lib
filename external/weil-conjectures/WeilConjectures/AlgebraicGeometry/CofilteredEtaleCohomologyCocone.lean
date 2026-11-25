/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# A cohomology colimit cocone for a cofiltered system over a fixed scheme

Source: Stacks Project, Theorem 59.51.3, Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical cohomology diagram of the restrictions of an abelian sheaf to a
cofiltered qcqs system with affine transitions has a colimit given by limit cohomology.
The stage isomorphisms identify its objects, and `r` records the compatible restriction
maps from the fixed base. The last equation specifies the comparison on those maps.

Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ), with the cofiltered-category reduction
of `lem-weil-pbc-filtered-category-exists-directed-final`.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-cocone)

Proof:
1. At stage j take the abelian group H^q(D_j, pi_j inverse image of G). Along an
   arrow k to j use cohomological pullback followed by the inverse-image composition
   isomorphism. Naturality of pi and inverse-image coherence give identity and
   composition, defining H on J opposite. The maps r_j are cohomologyMap pi_j.
   Pullback functoriality proves their displayed compatibility.
2. The composites c_j followed by pi_j agree: choose a common predecessor for any
   two indices, and use the cone and natural transformation equations. Call this
   map t. Inverse-image composition identifies the pullback to the limit of every
   stage sheaf with t inverse image of G, compatibly with all transitions.
3. Choose a small directed final functor to J opposite. Its opposite is initial,
   so the reindexed scheme cone is still a limit and has the same limit object.
   The constant compatible limit sheaves have colimit t inverse image of G,
   since the index category is nonempty and connected.
4. Apply Tag 09YQ to the reindexed directed qcqs system with affine transitions.
   It identifies the colimit of its cohomology groups with H^q(c.pt, t inverse
   image of G). Finality transfers this colimit universal property to J opposite.
   Use the canonical pullback maps to form B; the comparison is an isomorphism e.
5. Pullback functoriality and the composition comparisons identify e B_j r_j
   with cohomologyMap t. The stage identifications give eH_j r_j = cohomologyMap
   pi_j. These prove all displayed equations. No torsion assumption is used.

This asserts a cohomology colimit, before choosing a class or testing vanishing.
It includes q = 0, zero sheaves, empty schemes and a one-object index category. -/
theorem exists_cofiltered_etale_cohomology_cocone
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (j₀ : J) :
    ∃ (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (eH : ∀ j : J, H.obj (op j) ≅
        AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj G) q))
      (r : ∀ j : J, Sheaf.H G q →+ H.obj (op j)),
      (∀ (j k : J) (f : j ⟶ k) (x : Sheaf.H G q),
        H.map f.op (r k x) = r j x) ∧
      (∀ (j : J) (x : Sheaf.H G q), (eH j).hom (r j x) = cohomologyMap (π.app j) G q x) ∧
      ∃ (B : Cocone H) (_ : IsColimit B)
        (e : B.pt ≅ AddCommGrpCat.of
          (Sheaf.H (((c.π.app j₀ ≫ π.app j₀)^*[AddCommGrpCat.{u + 1}]).obj G) q)),
        ∀ (j : J) (x : Sheaf.H G q),
          e.hom (B.ι.app (op j) (r j x)) =
            cohomologyMap (c.π.app j₀ ≫ π.app j₀) G q x := by
  classical
  have hπ {j k : J} (f : j ⟶ k) : π.app j = D.map f ≫ π.app k := by
    have h := (π.naturality f).symm
    change π.app j ≫ 𝟙 S = D.map f ≫ π.app k at h
    exact (Category.comp_id _).symm.trans h
  have hcone {j k : J} (f : j ⟶ k) :
      c.π.app j ≫ π.app j = c.π.app k ≫ π.app k := by
    rw [hπ f, ← Category.assoc, c.w f]
  let t := c.π.app j₀ ≫ π.app j₀
  have ht (j : J) : t = c.π.app j ≫ π.app j := by
    exact (hcone (IsCofiltered.minToRight j j₀)).symm.trans
      (hcone (IsCofiltered.minToLeft j j₀))
  have laws := cohomologyTriangleMap_laws S G q
  let H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ AddCommGrpCat.of
        (Sheaf.H (((π.app j.unop)^*[AddCommGrpCat.{u + 1}]).obj G) q)
      map := fun f ↦ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D.map f.unop) (π.app _) (π.app _) (hπ f.unop) G q)
      map_id := by
        intro j
        dsimp
        simp only [D.map_id]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.1 (D.obj j.unop) (π.app j.unop))).trans AddCommGrpCat.ofHom_id
      map_comp := by
        intro j k l f g
        dsimp
        simp only [D.map_comp]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.2 (D.obj l.unop) (D.obj k.unop) (D.obj j.unop)
            (D.map g.unop) (D.map f.unop) (π.app j.unop) (π.app k.unop)
            (π.app l.unop) (hπ f.unop) (hπ g.unop))).trans
              (AddCommGrpCat.ofHom_comp _ _) }
  let eH (j : J) : H.obj (op j) ≅
      AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj G) q) :=
    Iso.refl _
  let r (j : J) : Sheaf.H G q →+ H.obj (op j) := cohomologyMap (π.app j) G q
  let B : Cocone H :=
    { pt := AddCommGrpCat.of (Sheaf.H (((t)^*[AddCommGrpCat.{u + 1}]).obj G) q)
      ι :=
        { app := fun j ↦ AddCommGrpCat.ofHom
            (cohomologyTriangleMap (c.π.app j.unop) (π.app j.unop) t (ht j.unop) G q)
          naturality := by
            intro j k f
            dsimp
            simp only [Category.comp_id]
            have h := laws.2 c.pt (D.obj k.unop) (D.obj j.unop)
              (c.π.app k.unop) (D.map f.unop) (π.app j.unop) (π.app k.unop)
              t (hπ f.unop) (ht k.unop)
            simp only [c.w f.unop] at h
            simpa only [AddCommGrpCat.ofHom_comp] using
              (congrArg AddCommGrpCat.ofHom h).symm } }
  have hH (j k : J) (f : j ⟶ k) : H.map f.op =
      (eH k).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D.map f) (π.app k) (π.app j) (hπ f) G q) ≫
          (eH j).inv := by simp [H, eH]
  have hB (j : J) : B.ι.app (op j) ≫ (Iso.refl B.pt).hom =
      (eH j).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (c.π.app j) (π.app j) t (ht j) G q) := by
    simp [B, eH]
  obtain ⟨hcolimit⟩ := nonempty_isColimit_cofiltered_fixed_base_cohomology
    D π c hc t ht G q H eH hH B (Iso.refl _) hB
  refine ⟨H, eH, r, ?_, ?_, B, hcolimit, Iso.refl _, ?_⟩
  · intro j k f x
    exact cohomologyTriangleMap_restriction (D.map f) (π.app k) (π.app j)
      (hπ f) G q x
  · intro j x
    rfl
  · intro j x
    exact cohomologyTriangleMap_restriction (c.π.app j) (π.app j) t (ht j) G q x

end AlgebraicGeometry.Etale
