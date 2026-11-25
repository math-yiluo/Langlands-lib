/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineRestrictionVanishing

/-! # Raw affine cohomology classes eventually vanish

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-local-class-vanishing).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private lemma covering_of_affine_arrows {S : Scheme.{v}} (W : S.Etale)
    (R : Sieve W) (hR : ∀ (V : S.Etale) (f : V ⟶ W), IsAffine V.left → R f) :
    R ∈ S.smallEtaleTopology W := by
  have : Etale W.hom := W.prop
  let 𝒰 := W.left.affineCover
  let V : 𝒰.I₀ → S.Etale := fun x ↦
    ⟨Over.mk (𝒰.f x ≫ W.hom), by
      change Etale (𝒰.f x ≫ W.hom)
      infer_instance⟩
  let f : ∀ x, V x ⟶ W := fun x ↦
    ⟨Over.homMk (𝒰.f x) (by rfl), trivial, trivial⟩
  have hcov : Sieve.ofArrows V f ∈ S.smallEtaleTopology W :=
    Scheme.ofArrows_mem_smallEtaleTopology_iff f |>.2 𝒰.iUnion_range
  apply S.smallEtaleTopology.superset_covering _ hcov
  rintro Z g ⟨T, a, _, ⟨x⟩, rfl⟩
  exact R.downward_closed (hR (V x) (f x) (by dsimp [V, 𝒰]; infer_instance)) a

/-- A raw class whose limit sheafification is zero is locally killed at later stages.
Source: Stacks Project, Tag 09Z1, proof of lemma-relative-colimit; Tags 03Q8 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-local-class-vanishing).

Proof: Local injectivity of the sheafification unit first gives a covering sieve
on which the raw limit class itself is zero. Refine each member by its affine
open cover. Raw pullback commutes with restriction, by functoriality of pullback
on derived Hom, so the restricted stage class has zero raw limit image.
On each affine member W, base change the scheme cone along W.hom. The stages
are qcqs because W is affine and the structure maps are qcqs; transitions remain
affine and the cone remains limiting. Restrict coefficients and their maps;
inverse image preserves their colimit. Put these sheaves in degree zero with
uniform lower bound zero, and apply complex cohomology continuity (0EZM).
The free abelian sheaf on W corepresents sections. Etale restriction has an exact
left adjoint and preserves injectives, so derived adjunction identifies these
raw Hom groups with cohomology on W times_S X_i, naturally in pullback and
coefficients. Single and shift comparisons identify the cocone maps with
abelianHigherDirectImageRawPullback. Injectivity of the colimit comparison and
the filtered group colimit equality criterion give a later zero representative.
Generate a sieve from these affine covering arrows. A further restriction
preserves zero and commutes with raw pullback, giving the asserted witness on
every arrow of the sieve. Cover transitivity makes this sieve covering.
For p = 0 use section continuity; empty objects have zero raw group. No common
later stage, higher-image sheaf comparison, or finite-cover gluing is asserted. -/
theorem exists_higherDirectImage_raw_local_class_eq_zero {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ) (U : S.Etale) (i : I)
    (z : (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U))
    (hz : (toSheafify S.smallEtaleTopology
      (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H))).app (op U)
        (abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
          (colimit H) ((eH i).inv ≫ colimit.ι H i) U z) = 0) :
    ∃ R : Sieve U, R ∈ S.smallEtaleTopology U ∧
      ∀ (W : S.Etale) (q : W ⟶ U), R q →
        ∃ (j : I) (f : i ⟶ j),
          abelianHigherDirectImageRawPullback (D.map f.op).left (D.obj (op i)).hom
            (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) W
              ((abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).map
                q.op z) = 0 := by
  let P := abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)
  let Q := abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)
  let t : Q.obj (op U) :=
    abelianHigherDirectImageRawPullback (c.π.app (op i)).left
      (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
      (colimit H) ((eH i).inv ≫ colimit.ι H i) U z
  let R : Sieve U :=
    { arrows := fun W q ↦ ∃ (j : I) (f : i ⟶ j),
        ∀ (V : S.Etale) (a : V ⟶ W),
          abelianHigherDirectImageRawPullback (D.map f.op).left (D.obj (op i)).hom
            (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) V
              (P.map (a ≫ q).op z) = 0
      downward_closed := by
        rintro W V q ⟨j, f, hf⟩ a
        refine ⟨j, f, fun T b ↦ ?_⟩
        simpa only [Category.assoc] using hf T (b ≫ a) }
  have hE : Presheaf.equalizerSieve t (0 : Q.obj (op U)) ∈
      S.smallEtaleTopology U :=
    Presheaf.equalizerSieve_mem S.smallEtaleTopology
      (toSheafify S.smallEtaleTopology Q) t 0 (hz.trans (map_zero _).symm)
  refine ⟨R, S.smallEtaleTopology.transitive hE R ?_, ?_⟩
  · intro W q hq
    apply covering_of_affine_arrows W (R.pullback q)
    intro V a ha
    have : IsAffine V.left := ha
    have hq' : Q.map q.op t = 0 := by
      simpa only [Presheaf.equalizerSieve_apply, map_zero] using hq
    have hv : Q.map (a ≫ q).op t = 0 := by
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hq', map_zero]
    exact exists_higherDirectImage_raw_affine_restriction_eq_zero
      D c hc F φ hφid hφcomp H eH hH p U i z V (a ≫ q) hv
  · intro W q hq
    obtain ⟨j, f, hf⟩ := hq
    exact ⟨j, f, by simpa only [Category.id_comp] using hf W (𝟙 W)⟩

end AlgebraicGeometry.Etale
