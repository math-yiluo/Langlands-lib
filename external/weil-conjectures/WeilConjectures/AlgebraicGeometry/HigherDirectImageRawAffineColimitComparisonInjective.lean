/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackCoherence
import WeilConjectures.AlgebraicGeometry.AbelianRawCoconeComplexPresentation

/-! # Injectivity of the raw affine cohomology colimit comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-raw-affine-colimit-comparison-injective).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Data for the raw affine comparison, with the canonical maps retained as natural
transformations. Its existence is asserted by the theorem below; this type makes
no choice of a witness and contains no unproved data.
(blueprint: lem-sbc-raw-affine-colimit-comparison-injective). -/
structure RawAffineColimitComparisonData {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] {S : Scheme.{v}}
    (A : I → S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v + 1})
    (Z : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v + 1}) (U : S.Etale)
    (r : ∀ {i j : I} (_f : i ⟶ j) (V : S.Etale), (A i).obj (op V) →
      (A j).obj (op V))
    (b : ∀ (i : I) (V : S.Etale), (A i).obj (op V) → Z.obj (op V)) where
  τ : ∀ {i j : I} (_f : i ⟶ j), A i ⟶ A j
  β : ∀ i : I, A i ⟶ Z
  K : I ⥤ AddCommGrpCat.{v + 1}
  B : Cocone K
  eStage : ∀ i : I, (A i).obj (op U) ≅ K.obj i
  eLimit : Z.obj (op U) ≅ B.pt
  hτ : ∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t : (A i).obj (op V)),
    (τ f).app (op V) t = r f V t
  hβ : ∀ (i : I) (V : S.Etale) (t : (A i).obj (op V)),
    (β i).app (op V) t = b i V t
  htrans : ∀ {i j : I} (f : i ⟶ j) (t : (A i).obj (op U)),
    K.map f ((eStage i).hom t) = (eStage j).hom ((τ f).app (op U) t)
  hleg : ∀ (i : I) (t : (A i).obj (op U)),
    B.ι.app i ((eStage i).hom t) = eLimit.hom ((β i).app (op U) t)
  hinj : Function.Injective (colimit.desc K B)

/-- The canonical colimit comparison for raw cohomology on an affine etale
object is injective. The raw stage and limit maps are natural transformations whose components are
constrained to be the explicit raw pullbacks. The diagram is constrained by these maps.
This statement asserts no eventual vanishing and no
uniformity over further restrictions.
Source: Stacks Project, Tag 09Z1 (the displayed cohomology colimit in the proof),
Tag 03Q8 (restricted cohomology), and Tag 0EZM (continuity for single complexes).
(blueprint: lem-sbc-raw-affine-colimit-comparison-injective).

Proof: Base change the diagram and its limiting cone along U → S. The pullback
universal properties preserve the limit. The stages are qcqs because the structure
maps are qcqs and U is affine; transitions remain affine after base change. Pull
back each coefficient sheaf and its coherent transitions to the new stages. Pull
back H to the limit and use the inverse-image composition comparisons to obtain
its canonical transition equations. Inverse image preserves the coefficient
colimit, and degree-zero single complexes preserve these termwise colimits.
The complexes have common lower bound zero. Form K from their cohomology groups,
with maps canonical derived pullback followed by the coefficient transitions.
The raw functions are additive: each factor is an additive functor map or composition
with a fixed morphism in a preadditive derived category. Construct tau and beta with
these component homomorphisms. Naturality of inverse-image composition and of the
single-functor comparison moves precomposition with a restriction map across the
source comparisons, and functoriality moves it across derived pullback. The shifted
coefficient map is independent of the test object. This proves the naturality
squares, so tau and beta are actual natural transformations with the stated components.
The coherent coefficient equations imply the functor laws. Form B with vertex
cohomology of the coefficient colimit and the canonical pullback legs.
The free abelian sheaf sections adjunction identifies raw derived Hom with
cohomology on the base changes: etale restriction preserves injectives because
its left adjoint is exact. Fully faithful inclusion of D⁺ into D identifies this
with cohomology of the single complexes. These additive identifications give
eStage and eLimit. Naturality of inverse-image composition, derived adjunction,
the single-complex comparison and the shift comparison gives the two displayed
equations. Apply complex cohomology continuity (0EZM) to this system. Transport
its colimit universal property along these identifications to B. Thus the
canonical colimit.desc K B is an isomorphism, in particular injective. This proof
uses only injectivity of continuity; surjectivity is not part of the assertion.
For degree zero this is section continuity. For the empty affine U all the groups
are zero and the comparison is injective. -/
theorem exists_raw_affine_colimit_comparison_injective {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    Nonempty (RawAffineColimitComparisonData
      (fun i ↦ abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i))
      (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)) U
      (fun {i j} f V t ↦ abelianHigherDirectImageRawPullback (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) V t)
      (fun i V t ↦ abelianHigherDirectImageRawPullback (c.π.app (op i)).left
        (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
        (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t)) := by
  obtain ⟨τ, β, hτ, hβ, hτid, hτcomp, hβcomp⟩ :=
    abelianRawPullback_coherent D c F φ hφid hφcomp H eH hH p
  let K : I ⥤ AddCommGrpCat.{v + 1} :=
    { obj := fun i ↦
        (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U)
      map := fun f ↦ (τ f).app (op U)
      map_id := fun i ↦ by rw [hτid]; rfl
      map_comp := fun f g ↦ by rw [hτcomp]; rfl }
  let B : Cocone K :=
    { pt := (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).obj (op U)
      ι :=
        { app := fun i ↦ (β i).app (op U)
          naturality := fun i j f ↦ by
            change (τ f).app (op U) ≫ (β j).app (op U) = (β i).app (op U) ≫ 𝟙 _
            rw [Category.comp_id]
            exact congrArg (fun t ↦ t.app (op U)) (hβcomp f) } }
  have s := abelianRawCocone_complex_presentation D c hc F φ hφid hφcomp H eH hH p U
    K B (fun i ↦ Iso.refl _) (Iso.refl _) (fun f t ↦ hτ f U t) (fun i t ↦ hβ i U t)
  obtain ⟨hB'⟩ := s.isColimit
  have hB : IsColimit B := IsColimit.ofWhiskerEquivalence (opOpEquivalence I) hB'
  have hinj : Function.Injective (colimit.desc K B) := by
    let e := (colimit.isColimit K).coconePointUniqueUpToIso hB
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective
  exact ⟨
    { τ := τ
      β := β
      K := K
      B := B
      eStage := fun i ↦ Iso.refl _
      eLimit := Iso.refl _
      hτ := hτ
      hβ := hβ
      htrans := fun _ _ ↦ rfl
      hleg := fun _ _ ↦ rfl
      hinj := hinj }⟩

end AlgebraicGeometry.Etale
