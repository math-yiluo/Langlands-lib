/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Normalized evaluation as the constant-sheaf coordinates upstairs

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS;
lem-weil-pbc-torsor-section-evaluation-local, steps 1 and 3.
(blueprint: lem-weil-pbc-torsor-normalized-graph-evaluation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Constant coordinates for a sheaf trivialized by a connected torsor, with a
pointwise local description by restrictions of global sections upstairs.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS;
lem-weil-pbc-torsor-normalized-graph-evaluation, step 1.
(blueprint: lem-weil-pbc-torsor-normalized-graph-evaluation)

Proof:
The comparison between inverse image and localization on the small etale site identifies
F restricted to c.P with the supplied constant module sheaf A. The constant module sheaf
on a scheme is the sheaf of locally constant A-valued functions: its constant presheaf
maps into locally constant functions and this map is both locally injective and locally
surjective, by covering with open fibres of a locally constant function. Sheafification
therefore gives the comparison isomorphism. Since c.P is connected and nonempty, every
locally constant A-valued function on c.P has a unique constant value. Evaluation of this
isomorphism at c.P identifies A with F(c.P). Apply the coefficient equivalence pointwise
to get the equivalence gamma on W, regarding W as etale over c.P via f. For s and w,
take the open fibre of gamma(s) through w. Its open subscheme U, with inclusion i and
point z over w, is etale over V. On U the coordinate function is constantly x, so the
restricted section equals the restriction of x in F(c.P), as asserted. If W is empty
there is no point w and the local assertion is vacuous; both section sets are singletons.
The zero module also gives singleton section sets, so the same argument applies. -/
private theorem Scheme.GaloisCover.constantCoordinates_localRestriction
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (W : V.Etaleᵒᵖ) (f : W.unop ⟶ c.sectionObject) :
    ∃ γ : F.obj.obj W ≃ LocallyConstant W.unop.left
        (F.obj.obj (Opposite.op c.sectionObject)),
      ∀ (s : F.obj.obj W) (w : W.unop.left),
        ∃ (U : V.Etale) (i : U ⟶ W.unop) (z : U.left)
          (x : F.obj.obj (Opposite.op c.sectionObject)),
          i.left z = w ∧ F.obj.map i.op s = F.obj.map (i ≫ f).op x ∧ γ s w = x := by
  classical
  let R := ULift.{u + 1} (ZMod ℓ)
  let C := ModuleCat.{u + 1} R
  let U := CategoryTheory.forget₂ C AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} R
  have : c.P.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification c.P.smallEtaleTopology U
  let D := MorphismProperty.Over.map ⊤ c.etale
  let T : c.P.Etale := Scheme.Etale.mk (𝟙 c.P)
  let Z : c.P.Etale := Scheme.Etale.mk f.left
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨e⟩ := h
  let k : (sheafCompose c.P.smallEtaleTopology U).obj
      ((localizationRestriction C c.π c.etale).obj F) ≅
      Scheme.Etale.continuousMapSheaf c.P A :=
    (sheafCompose c.P.smallEtaleTopology U).mapIso
      ((upperStarIsoLocalizationRestriction C c.π c.etale).app F).symm ≪≫
    (sheafCompose c.P.smallEtaleTopology U).mapIso e ≪≫
    (constantCommuteCompose c.P.smallEtaleTopology U).app A ≪≫
    Scheme.Etale.constantSheafIsoContinuousMapSheaf c.P A
  let t : D.obj T ≅ c.sectionObject :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 c.P) ≫ c.π = (𝟙 c.P) ≫ c.π
      rfl)
  let tW : D.obj Z ≅ W.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 W.unop.left) ≫ W.unop.hom =
        (𝟙 W.unop.left) ≫ f.left ≫ c.π
      simpa using (MorphismProperty.Over.w f).symm)
  obtain ⟨y₀⟩ := ‹ConnectedSpace c.P›.toNonempty
  let ev : C(c.P, A) ≃+ A :=
    { toFun := fun g ↦ g y₀
      invFun := ContinuousMap.const _
      left_inv := by
        intro g
        ext y
        exact ((IsLocallyConstant.iff_continuous g).2 g.continuous).apply_eq_of_preconnectedSpace
          y₀ y
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let b : F.obj.obj (Opposite.op c.sectionObject) ≃+ A :=
    ((F.obj.mapIso t.op).toLinearEquiv.toAddEquiv).trans
      (((((sheafToPresheaf _ _).mapIso k).app (Opposite.op T)).addCommGroupIsoToAddEquiv).trans
        ev)
  let r : F.obj.obj W ≃ C(W.unop.left, A) :=
    (F.obj.mapIso tW.op).toLinearEquiv.toEquiv.trans
      (((((sheafToPresheaf _ _).mapIso k).app (Opposite.op Z)).addCommGroupIsoToAddEquiv).toEquiv)
  let lc : C(W.unop.left, A) ≃ LocallyConstant W.unop.left A :=
    { toFun := fun g ↦ ⟨g, (IsLocallyConstant.iff_continuous g).2 g.continuous⟩
      invFun := fun g ↦ g.toContinuousMap
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let γ : F.obj.obj W ≃ LocallyConstant W.unop.left
      (F.obj.obj (Opposite.op c.sectionObject)) :=
    r.trans (lc.trans (LocallyConstant.congrRight b.symm.toEquiv))
  refine ⟨γ, ?_⟩
  intro s w
  let O := W.unop.left.fiberOpens (r s) (r s w)
  let B : c.P.Etale := Scheme.Etale.mk (O.ι ≫ f.left)
  let j : B ⟶ Z := MorphismProperty.Over.homMk O.ι rfl
  let q : B ⟶ T := MorphismProperty.Over.homMk B.hom (by
    change B.hom ≫ 𝟙 c.P = B.hom
    exact Category.comp_id _)
  let i : D.obj B ⟶ W.unop := D.map j ≫ tW.hom
  let z : O := ⟨w, rfl⟩
  let x := b.symm (r s w)
  refine ⟨D.obj B, i, z, x, ?_, ?_, ?_⟩
  · change (O.ι ≫ 𝟙 _) z = w
    simp [z]
  · have hi : D.map j ≫ tW.hom = i := rfl
    have hq : D.map q ≫ t.hom = i ≫ f := by
      apply MorphismProperty.Over.Hom.ext
      change (O.ι ≫ f.left) ≫ 𝟙 _ = (O.ι ≫ 𝟙 _) ≫ f.left
      simp
    have hj := ConcreteCategory.congr_hom (k.hom.hom.naturality j.op)
      (F.obj.map tW.hom.op s)
    have hqnat := ConcreteCategory.congr_hom (k.hom.hom.naturality q.op)
      (F.obj.map t.hom.op x)
    have hFis : F.obj.map (D.map j).op (F.obj.map tW.hom.op s) =
        F.obj.map i.op s := by
      rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← CategoryTheory.op_comp, hi]
    have hFix : F.obj.map (D.map q).op (F.obj.map t.hom.op x) =
        F.obj.map (i ≫ f).op x := by
      rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← CategoryTheory.op_comp, hq]
    have hb : (show C(c.P, A) from k.hom.hom.app (Opposite.op T)
        (F.obj.map t.hom.op x)) = ContinuousMap.const _ (r s w) := by
      ext y
      let v : C(c.P, A) := k.hom.hom.app (Opposite.op T) (F.obj.map t.hom.op x)
      change v y = r s w
      calc
        v y = v y₀ :=
          ((IsLocallyConstant.iff_continuous v).2 v.continuous).apply_eq_of_preconnectedSpace
            y y₀
        _ = b x := rfl
        _ = r s w := b.apply_symm_apply _
    apply (ConcreteCategory.bijective_of_isIso (k.hom.hom.app (Opposite.op B))).1
    change k.hom.hom.app (Opposite.op B) (F.obj.map i.op s) =
      k.hom.hom.app (Opposite.op B) (F.obj.map (i ≫ f).op x)
    rw [← hFis, ← hFix]
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map j).op (F.obj.map tW.hom.op s))) =
      (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
        (F.obj.map (D.map q).op (F.obj.map t.hom.op x)))
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map j).op (F.obj.map tW.hom.op s))) =
      (r s).comp j.left.base.hom at hj
    change (show C(B.left, A) from k.hom.hom.app (Opposite.op B)
      (F.obj.map (D.map q).op (F.obj.map t.hom.op x))) =
      (show C(c.P, A) from k.hom.hom.app (Opposite.op T)
        (F.obj.map t.hom.op x)).comp q.left.base.hom at hqnat
    rw [hj, hqnat, hb]
    ext y
    exact y.property
  · rfl

/-- The value of an ordinary normalized evaluation on the graph of f gives the
constant-sheaf coordinates on W. No equivariance of the evaluation is assumed.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS;
lem-weil-pbc-torsor-section-evaluation-local, steps 1 and 3.
(blueprint: lem-weil-pbc-torsor-normalized-graph-evaluation)

Proof:
Use the etale inverse-image/localization comparison to identify the restriction of F
to c.P with the given constant sheaf A. A morphism between etale V-objects is etale,
so f makes W an object of the small etale site of c.P. Its sections on an etale object T are locally
constant functions on T with value A. Since c.P is connected and nonempty, constant
functions identify A with F(c.P); restriction of a global section x is the constant
function x. This gives a canonical bijection gamma between F(W) and locally constant
functions on W with value F(c.P), where W is regarded as etale over c.P using f.
For a point of W and a section s, take an open neighborhood on which gamma(s) is the
constant value x. On that neighborhood s is the restriction of x along f. Naturality
of beta then identifies its value on the graph with beta at c.P evaluated on the
diagonal at f(w), which equals x by normalization. Thus graph evaluation after beta
is gamma, pointwise, and is bijective. On an empty W both the sheaf sections and locally
constant functions have a unique element by the empty covering. No torsor splitting
or extension of equivariant functions is used in this argument. -/
theorem Scheme.GaloisCover.ordinaryGraphEvaluation_bijective
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (β : ∀ T : V.Etaleᵒᵖ, F.obj.obj T →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace T.unop) (F.obj.obj (Opposite.op c.sectionObject)))
    (hβ : ∀ (T T' : V.Etaleᵒᵖ) (g : T ⟶ T') (s : F.obj.obj T)
        (x : c.sectionSpace T'.unop),
      β T' (F.obj.map g s) x = β T s (c.sectionRestriction g.unop x))
    (hΔ : ∀ (s : F.obj.obj (Opposite.op c.sectionObject)) (y : c.P),
      β (Opposite.op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) (W : V.Etaleᵒᵖ)
    (f : W.unop ⟶ c.sectionObject) :
    Function.Bijective (fun s : F.obj.obj W ↦
      LocallyConstant.comap
        (pullback.lift (f := W.unop.hom) (g := c.π) (𝟙 W.unop.left) f.left
          (by simpa using (MorphismProperty.Over.w f).symm)).base.hom
        (β W s)) := by
  obtain ⟨γ, hγ⟩ := c.constantCoordinates_localRestriction ℓ P F A h W f
  let graph (T : V.Etale) (g : T ⟶ c.sectionObject) : T.left ⟶ c.sectionSpace T :=
    pullback.lift (𝟙 T.left) g.left
      (by simpa using (MorphismProperty.Over.w g).symm)
  have heq (s : F.obj.obj W) :
      LocallyConstant.comap (graph W.unop f).base.hom (β W s) = γ s := by
    apply LocallyConstant.ext
    intro w
    obtain ⟨U, i, z, x, hiz, hs, hx⟩ := hγ s w
    have hi : graph U (i ≫ f) ≫ c.sectionRestriction i =
        i.left ≫ graph W.unop f := by
      apply pullback.hom_ext <;> simp [graph, Scheme.GaloisCover.sectionRestriction]
      rfl
    have hf : graph U (i ≫ f) ≫ c.sectionRestriction (i ≫ f) =
        (i ≫ f).left ≫ graph c.sectionObject (𝟙 _) := by
      apply pullback.hom_ext <;> simp [graph, Scheme.GaloisCover.sectionRestriction]
      rfl
    change β W s (graph W.unop f w) = γ s w
    rw [hx, ← hiz]
    rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply]
    have hb := hβ W (Opposite.op U) i.op s (graph U (i ≫ f) z)
    change β (Opposite.op U) (F.obj.map i.op s) (graph U (i ≫ f) z) =
      β W s (c.sectionRestriction i (graph U (i ≫ f) z)) at hb
    rw [← hb, hs]
    rw [hβ (Opposite.op c.sectionObject) (Opposite.op U) (i ≫ f).op x
      (graph U (i ≫ f) z)]
    change β (Opposite.op c.sectionObject) x
      (c.sectionRestriction (i ≫ f) (graph U (i ≫ f) z)) = x
    rw [← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply]
    exact hΔ x ((i ≫ f).left z)
  change Function.Bijective (fun s ↦
    LocallyConstant.comap (graph W.unop f).base.hom (β W s))
  have he : (fun s ↦ LocallyConstant.comap (graph W.unop f).base.hom (β W s)) =
      (fun s ↦ γ s) := funext heq
  rw [he]
  exact γ.bijective

end AlgebraicGeometry
