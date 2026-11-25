/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Localization of the small pro-etale site at a weakly etale object

Source: Stacks Project, Tags 098K, 094T, 0951, 00XZ, 04IX and 09AE
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- A morphism in a pro-etale slice is weakly etale by cancellation.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
theorem weaklyEtale_slice (X : Scheme.{u}) (W : X.ProEt) (T : Over W) :
    WeaklyEtale T.hom.left := by
  have hcomp : T.hom.left ≫ W.hom = T.left.hom := by simp
  have : WeaklyEtale (T.hom.left ≫ W.hom) := hcomp ▸ inferInstance
  exact WeaklyEtale.of_comp T.hom.left W.hom

/-- The functor from the slice at W to the small pro-etale site of its scheme.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
def sliceTo (X : Scheme.{u}) (W : X.ProEt) : Over W ⥤ W.left.ProEt where
  obj T := by
    have := weaklyEtale_slice X W T
    exact ProEt.mk T.hom.left
  map f := MorphismProperty.Over.homMk f.left.left (by
    have h := congrArg (fun f ↦ f.left) (Over.w f)
    exact h)

/-- The functor to the slice defined by composition with W.hom.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
def sliceFrom (X : Scheme.{u}) (W : X.ProEt) : W.left.ProEt ⥤ Over W where
  obj V := Over.mk (Y := ProEt.mk (V.hom ≫ W.hom))
    (MorphismProperty.Over.homMk V.hom rfl)
  map {V V'} f := Over.homMk (MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (V'.hom ≫ W.hom) = V.hom ≫ W.hom
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ W.hom)
      (MorphismProperty.Over.w f))) (by
        apply MorphismProperty.Over.Hom.ext
        exact MorphismProperty.Over.w f)

/-- The concrete equivalence from the slice to the small pro-etale site.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
def sliceEquiv (X : Scheme.{u}) (W : X.ProEt) : Over W ≌ W.left.ProEt where
  functor := sliceTo X W
  inverse := sliceFrom X W
  unitIso := NatIso.ofComponents (fun T ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom])) (by
      apply MorphismProperty.Over.Hom.ext
      change 𝟙 _ ≫ T.hom.left = T.hom.left
      exact Category.id_comp _))
  counitIso := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom]))

/-- Composition into the slice preserves the pro-etale coverings.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
theorem sliceFrom_cover (X : Scheme.{u}) (W : X.ProEt) :
    CoverPreserving (topology W.left) ((topology X).over W) (sliceFrom X W) where
  cover_preserve {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    change (S.functorPushforward (sliceFrom X W)).functorPushforward (Over.forget W) ∈ _
    rw [← Sieve.functorPushforward_comp]
    exact (coverPreserving_overMap (inferInstance : WeaklyEtale W.hom)).cover_preserve hS

/-- Composition into the slice is cocontinuous for the pro-etale topologies.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
theorem sliceFrom_cocont (X : Scheme.{u}) (W : X.ProEt) :
    (sliceFrom X W).IsCocontinuous (topology W.left) ((topology X).over W) where
  cover_lift {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff, mem_topology_iff] at hS
    obtain ⟨R, hR, hle⟩ := hS
    obtain ⟨ι, Z, φ, rfl⟩ := R.exists_eq_ofArrows
    let Z' (i : ι) : W.left.ProEt :=
      MorphismProperty.Over.mk ⊤ ((φ i).left ≫ V.hom)
        (weaklyEtale_left_comp (inferInstance : WeaklyEtale W.hom) (φ i))
    let φ' (i : ι) : Z' i ⟶ V := MorphismProperty.Over.homMk (φ i).left rfl
    apply mem_topology_iff.mpr
    refine ⟨Presieve.ofArrows Z' φ', ?_, ?_⟩
    · rw [mem_precoverage_iff] at hR ⊢
      rw [Presieve.map_ofArrows] at hR ⊢
      exact hR
    · rintro T _ ⟨i⟩
      have hY : 𝟙 (Z i).left ≫ (Z i).hom = ((φ i).left ≫ V.hom) ≫ W.hom := by
        simp only [Category.id_comp, Category.assoc]
        exact (MorphismProperty.Over.w (φ i)).symm
      let a : (sliceFrom X W).obj (Z' i) ⟶
          Over.mk ((φ i) ≫ ((sliceFrom X W).obj V).hom) :=
        Over.homMk (MorphismProperty.Over.homMk (𝟙 (Z i).left) hY) (by
          apply MorphismProperty.Over.Hom.ext
          change 𝟙 _ ≫ ((φ i).left ≫ V.hom) = (φ i).left ≫ V.hom
          exact Category.id_comp _)
      have ha : (sliceFrom X W).map (φ' i) = a ≫ Over.homMk (φ i) := by
        apply Over.OverMorphism.ext
        apply MorphismProperty.Over.Hom.ext
        exact (Category.id_comp _).symm
      change S ((sliceFrom X W).map (φ' i))
      rw [ha]
      exact S.downward_closed ((Sieve.overEquiv_iff _ _).mp (hle _ _ ⟨i⟩)) a

/-- The inverse slice equivalence is a dense subsite for the pro-etale topologies.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(auxiliary; not a blueprint node) -/
theorem sliceDense (X : Scheme.{u}) (W : X.ProEt) :
    (sliceEquiv X W).inverse.IsDenseSubsite (topology W.left) ((topology X).over W) where
  functorPushforward_mem_iff {V S} := by
    constructor
    · intro hS
      have := sliceFrom_cocont X W
      have h := (sliceFrom X W).cover_lift (topology W.left) ((topology X).over W) hS
      have : (sliceFrom X W).Full := inferInstanceAs (sliceEquiv X W).inverse.Full
      have : (sliceFrom X W).Faithful := inferInstanceAs (sliceEquiv X W).inverse.Faithful
      change (S.functorPushforward (sliceFrom X W)).functorPullback (sliceFrom X W) ∈ _ at h
      simpa only [Sieve.functorPullback_functorPushforward_eq] using h
    · exact (sliceFrom_cover X W).cover_preserve

private theorem rings (X : Scheme.{u}) (W : X.ProEt) (A : CommRingCat.{u + 1}) :
    ∃ (R : Sheaf (topology W.left) RingCat.{u + 1})
      (_hR : R.obj = (sliceEquiv X W).inverse.op ⋙
        (((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A)).over W).obj)
      (c : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ≅ R),
      (∀ V : W.left.ProEt,
        HEq ((toSheafify (topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
            c.hom.hom.app (op V))
          ((toSheafify (topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
              (op ((sliceEquiv X W).inverse.obj V).left))) := by
  let G : W.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom)
  have : G.IsContinuous (topology W.left) (topology X) := isContinuous_overMap W.prop
  have : G.IsCocontinuous (topology W.left) (topology X) := isCocontinuous_overMap W.prop
  let P := (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)
  let R := (G.sheafPushforwardContinuous RingCat.{u + 1} (topology W.left)
    (topology X)).obj ((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A))
  let c : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ≅ R :=
    (G.pushforwardContinuousSheafificationCompatibility RingCat.{u + 1}
      (topology W.left) (topology X)).app P
  refine ⟨R, rfl, c, ?_⟩
  intro V
  apply heq_of_eq
  exact congrArg (fun f ↦ f.app (op V))
    (G.toSheafify_pullbackSheafificationCompatibility RingCat.{u + 1}
      (topology W.left) (topology X) P)

private theorem module_transport
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    ∃ q : SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S,
      q.functor ⋙ SheafOfModules.forget _ =
        SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := e.inverse) c.hom.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  refine ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂, rfl⟩

/-- Localization at a weakly etale object identifies the small pro-etale sites, their
constant ring sheaves, and their module sheaves. The equivalence is oriented from the
slice to the site of `W.left`; its inverse is the assignment called `iota_j` in the node.
The object equalities fix the underlying schemes, and the heterogeneous equalities
specify the actual structure arrows and underlying maps without explicit transports.
The ring comparison
is uniquely specified by its composites with the constant-presheaf units. The final
functor equality specifies both the sectionwise action and the components of morphisms;
composing its functor with `SheafOfModules.overFunctor` gives ambient restriction.

Source: Stacks Project, Tags 098K, 094T, 0951, 00XZ, 04IX, 09AE, 01L7 and 01HI
(auxiliary; not a blueprint node).

Proof plan:
1. Compose weakly etale maps using 094T. Conversely cancel the weakly etale structure
   map using 0951 (`WeaklyEtale.of_comp`). The two assignments leave schemes and arrows
   unchanged, giving mutually inverse concrete categories and an equivalence of skeleta
   (`prose-01-10`, `lem-weil-pbc-weakly-etale-composition-base-change`,
   `lemma-stability--5`).
2. The fpqc finite-affine-cover condition depends only on the arrows to the covered scheme,
   not on the base. Thus the coverings agree and precomposition identifies sheaves
   (`definition-small-pro-etale-site--1`, `def-pur-localized-ringed-site`).
3. Restrict the constant ring presheaf. Ring-valued sheafification commutes with localization
   (`Functor.pushforwardContinuousSheafificationCompatibility`, Tag 00XZ). Its unit identity
   identifies constant sections, and the sheafification universal property gives uniqueness
   (`def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`,
   `lem-pur-ring-presheaf-sheafification-localization`).
4. Restrict modules using `SheafOfModules.overFunctor`, then pull their actions back along
   the ring comparison. Naturality gives semilinearity; the inverse ring map reverses this
   operation. Both operations leave section groups and morphism components unchanged
   (`def-pur-localized-ringed-site`, `situation-conventions`).
5. For an open immersion use its monomorphism property (01L7) for uniqueness. A factorization
   has image in the open; conversely `IsOpenImmersion.lift` (01HI) supplies the factorization
   whenever this image containment holds (`def-weil-open-immersion`,
   `lem-weil-pbc-open-immersion-monomorphism`,
   `lem-weil-pbc-morphism-factors-through-open-subscheme`). -/
theorem weaklyEtale_localization (X : Scheme.{u}) (W : X.ProEt)
    (A : CommRingCat.{u + 1}) :
    (∀ V : W.left.ProEt, WeaklyEtale (V.hom ≫ W.hom)) ∧
    (∀ T : Over W, WeaklyEtale T.hom.left) ∧
    (∃ e : Over W ≌ W.left.ProEt,
      (∀ T : Over W, (e.functor.obj T).left = T.left.left) ∧
      (∀ T : Over W, HEq (e.functor.obj T).hom T.hom.left) ∧
      (∀ (T T' : Over W) (f : T ⟶ T'), HEq (e.functor.map f).left f.left.left) ∧
      (∀ V : W.left.ProEt, (e.inverse.obj V).left.left = V.left) ∧
      (∀ V : W.left.ProEt, HEq (e.inverse.obj V).hom.left V.hom) ∧
      (∀ (V V' : W.left.ProEt) (f : V ⟶ V'), HEq (e.inverse.map f).left.left f.left) ∧
      (∀ (V : W.left.ProEt) (S : Sieve V),
        S ∈ topology W.left V ↔
          S.functorPushforward e.inverse ∈ (topology X).over W (e.inverse.obj V)) ∧
      (∀ (D : Type v) [Category.{w} D],
        ∃ s : Sheaf ((topology X).over W) D ≌ Sheaf (topology W.left) D,
          s.functor ⋙ sheafToPresheaf _ D =
            sheafToPresheaf _ D ⋙ (Functor.whiskeringLeft _ _ D).obj e.inverse.op) ∧
      (∃ (R : Sheaf (topology W.left) RingCat.{u + 1})
          (hR : R.obj = e.inverse.op ⋙
            (((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A)).over W).obj)
          (c : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ≅ R),
        (∀ V : W.left.ProEt,
          HEq ((toSheafify (topology W.left)
            ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
              c.hom.hom.app (op V))
            ((toSheafify (topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
                (op (e.inverse.obj V).left))) ∧
        (∀ f : (constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A) ⟶ R,
          (∀ V : W.left.ProEt,
            HEq ((toSheafify (topology W.left)
              ((Functor.const W.left.ProEtᵒᵖ).obj (RingCat.of A))).app (op V) ≫
                f.hom.app (op V))
              ((toSheafify (topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
                  (op (e.inverse.obj V).left))) → f = c.hom) ∧
        (∃ q : SheafOfModules.{u + 1}
            (((constantSheaf (topology X) RingCat.{u + 1}).obj (RingCat.of A)).over W) ≌
              SheafOfModules.{u + 1}
                ((constantSheaf (topology W.left) RingCat.{u + 1}).obj (RingCat.of A)),
          q.functor ⋙ SheafOfModules.forget _ =
            SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward
              (F := e.inverse) (c.hom.hom ≫ eqToHom hR)))) ∧
    (IsOpenImmersion W.hom →
      Mono W.hom ∧
      (∀ V : X.ProEt, Subsingleton (V ⟶ W)) ∧
      (∀ V : X.ProEt,
        (Nonempty (V ⟶ W) ↔ ∃ a : V.left ⟶ W.left, a ≫ W.hom = V.hom) ∧
        (Nonempty (V ⟶ W) ↔ Set.range V.hom ⊆ Set.range W.hom))) := by
  have := sliceDense X W
  refine ⟨fun _ ↦ inferInstance, weaklyEtale_slice X W, ?_, ?_⟩
  · refine ⟨sliceEquiv X W, (fun _ ↦ rfl), (fun _ ↦ HEq.rfl),
      (fun _ _ _ ↦ HEq.rfl), (fun _ ↦ rfl), (fun _ ↦ HEq.rfl),
      (fun _ _ _ ↦ HEq.rfl), ?_, ?_, ?_⟩
    · intro V S
      exact ((sliceEquiv X W).inverse.functorPushforward_mem_iff
        (topology W.left) ((topology X).over W)).symm
    · intro D _
      exact ⟨(sliceEquiv X W).sheafCongr ((topology X).over W) (topology W.left) D,
        rfl⟩
    · obtain ⟨R, hR, c, hc⟩ := rings X W A
      refine ⟨R, hR, c, hc, ?_, ?_⟩
      · intro f hf
        apply Sheaf.hom_ext
        apply sheafify_hom_ext (topology W.left) _ _ R.property
        apply NatTrans.ext
        funext V
        exact eq_of_heq ((hf V.unop).trans (hc V.unop).symm)
      · let R₀ := ((constantSheaf (topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).over W
        let c' : (constantSheaf (topology W.left) RingCat.{u + 1}).obj
            (RingCat.of A) ≅
            ((sliceEquiv X W).inverse.sheafPushforwardContinuous RingCat.{u + 1}
              (topology W.left) ((topology X).over W)).obj R₀ :=
          c ≪≫ (fullyFaithfulSheafToPresheaf _ _).preimageIso (eqToIso hR)
        obtain ⟨q, hq⟩ := module_transport ((topology X).over W) (topology W.left)
          (sliceEquiv X W) R₀ _ c'
        exact ⟨q, hq⟩
  · intro hW
    have := hW
    refine ⟨inferInstance, ?_, ?_⟩
    · intro V
      refine ⟨fun a b ↦ ?_⟩
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono W.hom).mp
      exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
    · intro V
      constructor
      · constructor
        · rintro ⟨a⟩
          exact ⟨a.left, MorphismProperty.Over.w a⟩
        · rintro ⟨a, ha⟩
          exact ⟨MorphismProperty.Over.homMk a ha⟩
      · constructor
        · rintro ⟨a⟩ y ⟨x, rfl⟩
          exact ⟨a.left x, congrArg (fun f : V.left ⟶ X ↦ f x)
            (MorphismProperty.Over.w a)⟩
        · intro h
          exact ⟨MorphismProperty.Over.homMk (IsOpenImmersion.lift W.hom V.hom h)
            (IsOpenImmersion.lift_fac W.hom V.hom h)⟩

end AlgebraicGeometry.Scheme.ProEt
