/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionColimit
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Scalar continuity for descended qcqs étale objects

Source: Stacks Project, Tags 09YN and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- This helper is the eventual-zero half of scalar section continuity. Equality in the
filtered colimit is detected after a later transition. Source: Stacks Tags 09YN and 09YQ.
Source: Stacks Project, Sites, Tag 09YN, proof of lemma-colimit; Étale Cohomology,
Tag 09YQ, qcqs inverse-limit realization; Cohomology on Sites, Tag 09YP.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-zero-eventually).

Proof: Base change T₀ along the tail of D. Affine-transition base-change limits
identify its limit with Tlim. The first-projection equations, together with the
already fixed base projections, uniquely identify γ and δ with pullback pasting.
On an affine piece, use the full affine étale site and its topos comparison to
apply 09YM to each inverse image in G. Insert these filtered presentations into
the sectionwise colimit of G. Objects, arrows and equalities in the affine site
all descend, so simultaneous refinements are filtered and the diagonal is final.
This identifies the iterated colimit with the stage section groups. Transposing
through the inverse-image adjunction identifies its transitions with the units
followed by φ and γ inverse, and its legs with the units followed by eG inverse,
L.ι and δ inverse. For qcqs T₀, take a finite affine cover, and finite affine
covers of its pairwise intersections; filtered colimits commute with the finite
matching-family equalizers. Thus the same comparison holds for T₀ itself.
The tail is final, so restricting G does not change the colimit supplied by hL.
Every element of a filtered colimit of abelian groups has a stage representative.
Equality of a representative with zero holds after one later transition. These
are the two conclusions below, with the prescribed maps. The empty scheme and
zero coefficients give zero groups; no nonempty-object hypothesis is needed.
This statement concerns one object, with no products or cochain complexes. -/
theorem etale_limit_scalar_sections_zero_eventually
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
    (∀ (j : J) (z : (F j.val).obj.obj (op (Tj j))), μ j z = 0 →
      ∃ (k : J) (a : j ⟶ k), ρ j k a z = 0) := by
  intro J Tj Tlim γ δ hγ hδ ρ μ
  obtain ⟨hid, hcomp, hleg⟩ := etale_limit_scalar_section_map_laws
    D c F φ hidentity hcomposition G eG hG L i₀ T₀ γ δ hγ hδ
  let A : J ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun j ↦ (F j.val).obj.obj (op (Tj j))
      map := fun a ↦ ρ _ _ a
      map_id := hid
      map_comp := hcomp _ _ _ }
  let C : Cocone A :=
    { pt := L.pt.obj.obj (op Tlim)
      ι := { app := μ
             naturality := fun j k a ↦ by
               change ρ j k a ≫ μ k = μ j ≫ 𝟙 _
               rw [Category.comp_id]
               exact hleg j k a } }
  obtain ⟨hC⟩ := etale_limit_scalar_section_colimit
    D c hc F φ hidentity hcomposition G eG hG L hL i₀ T₀ γ δ hγ hδ hid hcomp hleg
  have : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩⟩
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
      (forget AddCommGrpCat.{u + 1})
  intro j z hz
  have he : C.ι.app j z = C.ι.app j 0 := by
    change μ j z = μ j 0
    simpa only [map_zero] using hz
  obtain ⟨k, a, ha⟩ := hC.eq_iff' z 0 |>.mp he
  change ρ j k a z = ρ j k a 0 at ha
  exact ⟨k, a, by simpa only [map_zero] using ha⟩

end AlgebraicGeometry.Etale
