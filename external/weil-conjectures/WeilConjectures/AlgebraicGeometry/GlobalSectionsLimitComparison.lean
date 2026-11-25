/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Global sections of pullbacks at cofiltered limits

Source: Stacks Project, Tag 09YQ, degree zero.
(blueprint: lem-weil-pbc-global-sections-limit-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

private noncomputable def sectionsHZeroIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F ≅
      AddCommGrpCat.of (Sheaf.H F 0) :=
  (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).app F ≪≫
    (Sheaf.H.equiv₀ F terminalIsTerminal).symm.toAddCommGrpIso

private theorem sectionsHZeroIso_naturality {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map f ≫
        (sectionsHZeroIso G).hom =
      (sectionsHZeroIso F).hom ≫ AddCommGrpCat.ofHom (Sheaf.H.map f 0) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (Sheaf.H.equiv₀ G terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G
        ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).map f x)) =
    Sheaf.H.map f 0 ((Sheaf.H.equiv₀ F terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app F x))
  rw [Sheaf.H.equiv₀_symm_naturality]
  congr 1
  exact ConcreteCategory.congr_hom
    ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.naturality f) x

private theorem sectionsHZeroIso_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f F ≫
        (sectionsHZeroIso ((upperStar AddCommGrpCat.{u + 1} f).obj F)).hom =
      (sectionsHZeroIso F).hom ≫ AddCommGrpCat.ofHom (cohomologyMap f F 0) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (cohomologyMap_zero_eq_globalSectionsUpperStarMap f F x).symm

private noncomputable def sectionTransition {R X Y : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f) :
    (Sheaf.Γ _ AddCommGrpCat.{u + 1}).obj ((upperStar AddCommGrpCat.{u + 1} f).obj G) ⟶
      (Sheaf.Γ _ AddCommGrpCat.{u + 1}).obj ((upperStar AddCommGrpCat.{u + 1} g).obj G) :=
  globalSectionsUpperStarMap AddCommGrpCat.{u + 1} h
      ((upperStar AddCommGrpCat.{u + 1} f).obj G) ≫
    (Sheaf.Γ _ AddCommGrpCat.{u + 1}).map
      ((upperStarComp AddCommGrpCat.{u + 1} h f g w).inv.app G)

private theorem sectionTransition_HZero {R X Y : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f) :
    sectionTransition G h f g w ≫
        (sectionsHZeroIso ((upperStar AddCommGrpCat.{u + 1} g).obj G)).hom =
      (sectionsHZeroIso ((upperStar AddCommGrpCat.{u + 1} f).obj G)).hom ≫
        AddCommGrpCat.ofHom (cohomologyTriangleMap h f g w G 0) := by
  unfold sectionTransition
  rw [Category.assoc, sectionsHZeroIso_naturality, ← Category.assoc,
    sectionsHZeroIso_pullback, Category.assoc]
  rfl

private theorem sectionTransition_id {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : X ⟶ R) :
    sectionTransition G (𝟙 X) f f (by simp) = 𝟙 _ := by
  apply (cancel_mono (sectionsHZeroIso ((upperStar AddCommGrpCat.{u + 1} f).obj G)).hom).mp
  rw [sectionTransition_HZero, (cohomologyTriangleMap_laws R G 0).1 X f]
  simp

private theorem sectionTransition_comp {R X Y Z : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : X ⟶ Y) (k : Y ⟶ Z) (f : Z ⟶ R) (g : Y ⟶ R) (l : X ⟶ R)
    (wg : g = k ≫ f) (wl : l = h ≫ g) :
    sectionTransition G k f g wg ≫ sectionTransition G h g l wl =
      sectionTransition G (h ≫ k) f l (by rw [wl, wg, Category.assoc]) := by
  apply (cancel_mono (sectionsHZeroIso ((upperStar AddCommGrpCat.{u + 1} l).obj G)).hom).mp
  rw [Category.assoc, sectionTransition_HZero, ← Category.assoc,
    sectionTransition_HZero, Category.assoc, sectionTransition_HZero,
    (cohomologyTriangleMap_laws R G 0).2 X Y Z h k f g l wg wl,
    AddCommGrpCat.ofHom_comp]

set_option backward.isDefEq.respectTransparency true in
/-- Global sections of pullbacks of a fixed abelian sheaf commute with a qcqs inverse
limit with affine transition maps. No assumption on the base scheme is needed.
Source: Stacks Project, Tag 09YQ, degree zero.
(blueprint: lem-weil-pbc-global-sections-limit-comparison)

Proof: Replace the cofiltered category by a coinitial directed preorder and restrict
both the limit cone and the system along that functor. Set F_j = π_j^* G. The inverse-image
composition isomorphisms give transition isomorphisms h^* F_j ≅ F_k; their cocycle and unit
laws follow from coherence of inverse image. On the limit, composition identifies the
pullbacks of every F_j with P^* G, and identifies all transitions with the identity. A
filtered category is connected, so this constant cocone is a colimit. Apply Theorem 09YQ
in degree zero to this system and this cocone. The degree-zero identification with global
sections is natural in sheaf maps and carries cohomology pullback to the adjunction-unit
map globalSectionsUpperStarMap. Thus the resulting colimit legs and transitions are the
maps displayed below. The elementwise criterion for filtered colimits of abelian groups
then gives representatives and eventual vanishing. Coinitiality returns these witnesses
to the original category (for vanishing use a common refinement mapping to the given
object); all transition formulas are preserved by inverse-image coherence. -/
theorem globalSections_limit_comparison {R : Scheme.{u}} {J : Type u}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
    (hP : ∀ j, P = c.π.app j ≫ π.app j)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let Γ := fun X : Scheme.{u} ↦ Sheaf.Γ X.smallEtaleTopology A
    let F := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (upperStar A f).obj G
    let ρ := fun {X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R)
      (w : g = h ≫ f) ↦ globalSectionsUpperStarMap A h (F f) ≫
        (Γ X).map ((upperStarComp A h f g w).inv.app G)
    (∀ t : (Γ c.pt).obj (F P), ∃ (j : J) (s : (Γ (D.obj j)).obj (F (π.app j))),
      ρ (c.π.app j) (π.app j) P (hP j) s = t) ∧
    ∀ (j : J) (s : (Γ (D.obj j)).obj (F (π.app j))),
      ρ (c.π.app j) (π.app j) P (hP j) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), ρ (D.map f) (π.app j) (π.app j') (by simp) s = 0 := by
  intro A Γ F ρ
  let H : Jᵒᵖ ⥤ A :=
    { obj := fun j ↦ (Γ (D.obj j.unop)).obj (F (π.app j.unop))
      map := fun {j k} f ↦ ρ (D.map f.unop) (π.app j.unop) (π.app k.unop) (by simp)
      map_id := by
        intro j
        dsimp
        simpa only [ρ, A, Γ, F, sectionTransition, D.map_id] using
          sectionTransition_id G (π.app j.unop)
      map_comp := by
        intro i j k f g
        dsimp
        simpa only [ρ, A, Γ, F, sectionTransition, D.map_comp] using
          (sectionTransition_comp G (D.map g.unop) (D.map f.unop)
          (π.app i.unop) (π.app j.unop) (π.app k.unop) (by simp) (by simp)).symm }
  let B : Cocone H :=
    { pt := (Γ c.pt).obj (F P)
      ι :=
        { app := fun j ↦ ρ (c.π.app j.unop) (π.app j.unop) P (hP j.unop)
          naturality := by
            intro j k f
            dsimp
            rw [Category.comp_id]
            change sectionTransition G (D.map f.unop) _ _ _ ≫
              sectionTransition G (c.π.app k.unop) _ _ _ = _
            rw [sectionTransition_comp]
            congr 1
            exact c.w f.unop } }
  obtain ⟨hB⟩ := nonempty_isColimit_cofiltered_fixed_base_cohomology D π c hc P hP G 0
    H (fun j ↦ sectionsHZeroIso (F (π.app j))) (by
      intro j k f
      apply (cancel_mono (sectionsHZeroIso (F (π.app j))).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change sectionTransition G (D.map f) (π.app k) (π.app j) _ ≫
          (sectionsHZeroIso (F (π.app j))).hom = _
      exact sectionTransition_HZero G _ _ _ _)
    B (sectionsHZeroIso (F P)) (by
      intro j
      change sectionTransition G (c.π.app j) (π.app j) P _ ≫
          (sectionsHZeroIso (F P)).hom = _
      exact sectionTransition_HZero G _ _ _ _)
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget AddCommGrpCat.{u + 1})
  constructor
  · intro t
    obtain ⟨j, s, hs⟩ := Concrete.isColimit_exists_rep H hB t
    exact ⟨j.unop, s, hs⟩
  · intro j s hs
    have hz : B.ι.app (op j) s = B.ι.app (op j) 0 := by
      change ρ (c.π.app j) (π.app j) P (hP j) s =
        ρ (c.π.app j) (π.app j) P (hP j) 0
      rw [hs]
      exact ((ρ (c.π.app j) (π.app j) P (hP j)).hom.map_zero).symm
    obtain ⟨k, f, g, he⟩ := Concrete.isColimit_exists_of_rep_eq H hB s 0 hz
    exact ⟨k.unop, f.unop, by simpa using he⟩

end AlgebraicGeometry.Etale
