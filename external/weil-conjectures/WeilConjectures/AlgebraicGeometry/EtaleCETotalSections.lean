/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
public import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal

/-! # Global sections of Cartan--Eilenberg totals

Source: Stacks Project, Tag 015J, the finite-diagonal comparison in the proof.
(blueprint: lem-weil-pbc-ce-total-sections-comparison).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

namespace EtaleTermwiseHypercohomology

/-- The extended and flipped CE total before global sections. Source: Stacks, Tag 015J.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
noncomputable abbrev sheafTotal {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :=
  (((CartanEilenbergPresentation.mappedFunctor
    (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj D.I).flip).total
      (ComplexShape.up ℤ)

/-- The CE total after global sections. Source: Stacks, Tag 015J.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
noncomputable abbrev sectionsTotal {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :=
  (((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj D.I).flip).total
      (ComplexShape.up ℤ)

/-- Finite-diagonal comparison. Source: Stacks, Tag 015J.
The summand equations determine this isomorphism uniquely: total coproduct inclusions
are jointly epimorphic in each degree, and negative resolution summands are zero.
The existence theorem used here is proved, and no arbitrary existence data are chosen.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
noncomputable def totalSectionsIso {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :
    D.sectionsTotal ≅
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D.sheafTotal :=
  (Functor.cartanEilenberg_mapped_total_iso
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I D.below).choose

/-- Summand characterization of the comparison. Source: Stacks, Tag 015J.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
theorem totalSectionsIso_formula {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :
    ∀ (m : ℕ) (k n : ℤ) (h : (m : ℤ) + k = n),
            (((CartanEilenbergPresentation.mappedFunctor
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj
                D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h ≫ D.totalSectionsIso.hom.f n =
              (HomologicalComplex.extendXIso
                (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
                  |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X k))
                ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
                ((HomologicalComplex.extendXIso
                  (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
                    |>.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X k))
                  ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) k n h) :=
  (Functor.cartanEilenberg_mapped_total_iso
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I D.below).choose_spec

/-- The diagonal comparison followed by global sections of the resolution comparison
is the presentation's fixed map `w`. Source: Stacks, Tag 015J.
(blueprint: lem-weil-pbc-ce-total-sections-comparison).

Proof: Test equality on every diagonal summand. For nonnegative resolution degree,
use the comparison's summand equation, functoriality of global sections, and `w_formula`.
For negative resolution degree extension by zero makes the source zero, so both maps
are equal. The total coproduct inclusions are jointly epimorphic in every degree. -/
theorem totalSectionsIso_comparison {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :
    D.totalSectionsIso.hom ≫
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map D.comparison = D.w := by
  apply HomologicalComplex.hom_f_injective
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro m k h
  by_cases hm : 0 ≤ m
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    change _ ≫ (D.totalSectionsIso.hom.f n ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
        (D.comparison.f n)) = _
    rw [← Category.assoc, D.totalSectionsIso_formula a k n h, D.w_formula a k n h]
    simp only [Category.assoc, Functor.map_comp]
  · exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat m
      (fun a ha ↦ by change (a : ℤ) = m at ha; omega)).eq_of_src _ _

end EtaleTermwiseHypercohomology

set_option backward.isDefEq.respectTransparency false in
/-- The global-sections pullback maps form a natural transformation.
Source: Stacks, Tag 015K. Naturality follows from the inverse-image adjunction unit
and the natural comparison between global sections and sections at the terminal object.
This packages all components, so its naturality also applies to complex differentials.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
noncomputable def ceSectionsUnit {X Y : Scheme.{uNatural}} (f : Y ⟶ X) :
    Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1} ⟶
      upperStar AddCommGrpCat.{uNatural + 1} f ⋙
        Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1} :=
  (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
    terminalIsTerminal).hom ≫
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).obj
        (Opposite.op (⊤_ X.Etale))) ≫
    Functor.whiskerLeft (upperStar AddCommGrpCat.{uNatural + 1} f)
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{uNatural + 1} f).hom ≫
    Functor.whiskerLeft (upperStar AddCommGrpCat.{uNatural + 1} f)
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
        terminalIsTerminal).inv

set_option backward.isDefEq.respectTransparency false in
/-- Apply the global-sections unit and a given chain map. Source: Stacks, Tag 015K.
(blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
noncomputable def ceSectionsLift {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {A : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {B : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (g : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶ B) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj B where
  f i := globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X i) ≫
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (g.f i)
  comm' i k _ := by
    change (_ ≫ _) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (B.d i k) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (A.d i k) ≫ _
    rw [Category.assoc, ← Functor.map_comp, g.comm i k, Functor.map_comp]
    simp only [Functor.mapHomologicalComplex_obj_d]
    have hn := (ceSectionsUnit f).naturality (A.d i k)
    change (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (A.d i k) ≫
        globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X k) =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (A.X i) ≫
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
          ((upperStar AddCommGrpCat.{uNatural + 1} f).map (A.d i k)) at hn
    rw [← Category.assoc, ← hn, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition of the chain map commutes with its sections lift.
Source: Stacks, Tag 015K (blueprint: lem-weil-pbc-ce-total-sections-comparison). -/
theorem ceSectionsLift_comp {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {A : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {B C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (g : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶ B) (h : B ⟶ C) :
    ceSectionsLift f (g ≫ h) = ceSectionsLift f g ≫
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map h := by
  apply HomologicalComplex.hom_f_injective
  funext i
  change _ ≫ (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map
    (g.f i ≫ h.f i) = (_ ≫ _) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (h.f i)
  rw [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
