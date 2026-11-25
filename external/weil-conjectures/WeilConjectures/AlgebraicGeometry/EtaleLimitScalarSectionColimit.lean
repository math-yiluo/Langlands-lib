/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionRepresentatives
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionEventualEquality
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Scalar section comparison along an inverse system
Source: Stacks Project, Tags 09YN and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The canonical stage-section cocone is a colimit once its coherence is supplied.
Source: Stacks Project, Sites, Tag 09YN, proof of lemma-colimit; Etale Cohomology,
Tag 09YQ; Cohomology on Sites, Tag 09YP, degree-zero comparison.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-colimit).

Proof: Base change T0 along the final directed tail. Affine-transition limits
identify its limit with Tlim. On affine objects, present inverse-image sections
using the full affine etale sites. Descent of objects, arrows and equalities makes
the simultaneous refinement category filtered and its diagonal final. The finite
covering section theorem identifies sections of the sheaf colimit with the
iterated filtered colimit. Flattening that colimit gives the stage-section diagram
A. Transposing by the inverse-image adjunction identifies its maps and cocone legs
with rho and mu, using the prescribed projection equations. For qcqs T0 choose a
finite affine cover and finite affine covers of its pairwise intersections.
Matching-family equalizers compute sections, and filtered colimits of abelian
groups commute with these finite limits. This extends the colimit comparison to
T0. Finality of the tail identifies its sheaf colimit with L. This proves the
universal property of C, without using any eventual-vanishing criterion. Empty
schemes give zero section groups; the same equalizer argument covers this case. -/
theorem etale_limit_scalar_section_colimit
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
    (L : Cocone G) (hL : IsColimit L)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    [CompactSpace T₀.left] [QuasiSeparatedSpace T₀.left] :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let μ := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (L.ι.app j.val).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        L.pt.obj.map (δ j).inv.op
    ∀ (hid : ∀ j : J, ρ j j (𝟙 j) = 𝟙 _)
      (hcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l),
        ρ j l (a ≫ b) = ρ j k a ≫ ρ k l b)
      (hleg : ∀ (j k : J) (a : j ⟶ k), ρ j k a ≫ μ k = μ j),
    let A : J ⥤ AddCommGrpCat.{u + 1} :=
      { obj := fun j ↦ (F j.val).obj.obj (op (Tj j))
        map := fun a ↦ ρ _ _ a
        map_id := hid
        map_comp := hcomp _ _ _ }
    let C : Cocone A :=
      { pt := L.pt.obj.obj (op Tlim)
        ι := { app := μ
               naturality := fun j k a ↦ by simpa using hleg j k a } }
    Nonempty (IsColimit C) := by
  intro J Tj Tlim γ δ hγ hδ ρ μ hid hcomp hleg A C
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩⟩
  let U := forget AddCommGrpCat.{u + 1}
  let : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} U
  have : ReflectsColimit A U := reflectsColimit_of_reflectsIsomorphisms A U
  refine ⟨isColimitOfReflects U ?_⟩
  apply Types.FilteredColimit.isColimitOf' (A ⋙ U) (U.mapCocone C)
  · intro x
    obtain ⟨j, z, hz⟩ := etale_limit_scalar_sections_representatives
      D c hc F φ hidentity hcomposition G eG hG L hL i₀ T₀ γ δ hγ hδ x
    exact ⟨j, z, hz.symm⟩
  · intro j s t hst
    exact etale_limit_scalar_sections_eventual_equality
      D c hc F φ hidentity hcomposition G eG hG L hL i₀ T₀ γ δ hγ hδ j s t hst

end AlgebraicGeometry.Etale
