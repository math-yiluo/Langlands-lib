/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # A pointed witness for equality of étale inverse-image unit sections
Source: Stacks Project, Tag 09ZF, first proof paragraph, and Sites, Tag 00WK.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem sheafification_unit_locally_injective
    {C : Type u} [Category.{w} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type (max u w v)) :
    Presheaf.IsLocallyInjective J (toSheafify J P) := by
  have hplus (Q : Cᵒᵖ ⥤ Type (max u w v)) :
      Presheaf.IsLocallyInjective J (J.toPlus Q) := by
    constructor
    intro X x y h
    rw [GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.toPlus_eq_mk,
      GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering
      (fun Y f hf ↦ congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2
  let := hplus P
  let := hplus (J.plusObj P)
  have : Presheaf.IsLocallyInjective J (J.toSheafify P) := by
    dsimp [GrothendieckTopology.toSheafify]
    rw [GrothendieckTopology.plusMap_toPlus]
    infer_instance
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

/-- Equality of unit sections after restriction is witnessed on an étale
X-scheme whose image contains the image of the chosen point.
Source: Stacks Project, Tag 09ZF, first proof paragraph; Sites, Tags 00VE, 00WX, 00WK.
(blueprint: lem-weil-pbc-etale-pullback-unit-pointed-witness).

Proof: the constructed sheaf pullback is the sheafification of the left Kan
extension along the opposite base-change functor. Its adjunction unit is the
Kan-extension unit followed by the sheafification unit. Thus the two restricted
sections are sheafifications of the two coprojections indexed by (W,f).
Local injectivity of sheafification supplies an étale cover of V on which these
coprojections agree. Choose a member and a point above z, using joint
surjectivity. The index category is filtered: the small étale category has
finite limits and base change preserves them. Equality in a filtered colimit
of sets is witnessed by one arrow out of the common index. Opposing that
arrow gives an étale X-scheme U, an X-morphism g:U→W, and a Z-morphism from
the chosen covering member to U×[X]Z; the restrictions of s and t along g
are equal. Project the chosen point to U. Commutativity over Z and the
pullback square show that its image in X is i(V.hom(z)). This proves all
three assertions. Empty V has no z, and no surjectivity or closedness of i
is required. The section universe is at least that of the small étale site,
so the usual local-injectivity theorem for sheafification applies. -/
theorem etale_pullback_unit_pointed_witness
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (W : X.Etale) (V : Z.Etale)
    (f : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj W)
    (z : V.left) (s t : F.obj.obj (op W))
    (heq :
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).obj F).obj.map f.op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
          (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op W) s) =
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)).obj F).obj.map f.op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
          (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op W) t)) :
    ∃ (U : X.Etale) (g : U ⟶ W) (u : U.left),
      U.hom u = i (V.hom z) ∧ F.obj.map g.op s = F.obj.map g.op t := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ i
  let J : GrothendieckTopology Z.Etale := Z.smallGrothendieckTopology @Etale
  let P := b.op.lan.obj F.obj
  let α := b.op.lanUnit.app F.obj
  let p := P.map f.op (α.app (op W) s)
  let q := P.map f.op (α.app (op W) t)
  have heq' : (toSheafify J P).app (op V) p = (toSheafify J P).app (op V) q := by
    change (sheafify J P).map f.op
      ((toSheafify J P).app (op (b.obj W)) (α.app (op W) s)) =
      (sheafify J P).map f.op
      ((toSheafify J P).app (op (b.obj W)) (α.app (op W) t)) at heq
    exact ((toSheafify J P).naturality_apply f.op _).trans
      (heq.trans ((toSheafify J P).naturality_apply f.op _).symm)
  let := sheafification_unit_locally_injective (C := MorphismProperty.Over @Etale ⊤ Z) J P
  have hcover := Presheaf.equalizerSieve_mem J (toSheafify J P) p q heq'
  obtain ⟨𝒰, h𝒰, h𝒰', hle⟩ := (Scheme.mem_smallGrothendieckTopology _ _).mp hcover
  let := h𝒰
  obtain ⟨k, y, hy⟩ := 𝒰.exists_eq z
  let Vk : Z.Etale := (𝒰.X k).asOverProp Z (h𝒰' k)
  let a : Vk ⟶ V := (𝒰.f k).asOverProp Z
  have he : P.map a.op p = P.map a.op q := hle _ _ (Presieve.ofArrows.mk k)
  let T : CostructuredArrow b.op (op Vk) := CostructuredArrow.mk (a ≫ f).op
  let c := (Functor.LeftExtension.mk _ (b.op.leftKanExtensionUnit F.obj)).coconeAt (op Vk)
  have hc := b.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op Vk)
  let : RepresentablyFlat b := flat_of_preservesFiniteLimits b
  let : IsFiltered (CostructuredArrow b.op (op Vk)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence b Vk)
  have he' : c.ι.app T s = c.ι.app T t := by
    change P.map (a ≫ f).op (α.app (op W) s) =
      P.map (a ≫ f).op (α.app (op W) t)
    exact (congrArg (fun k ↦ k (α.app (op W) s))
      (P.map_comp f.op a.op)).trans
      (he.trans (congrArg (fun k ↦ k (α.app (op W) t))
        (P.map_comp f.op a.op)).symm)
  obtain ⟨K, h, hh⟩ := (Types.FilteredColimit.isColimit_eq_iff' (i := T) hc s t).mp he'
  let U := unop K.left
  let g : U ⟶ W := h.left.unop
  let ψ : Vk ⟶ b.obj U := K.hom.unop
  let u : U.left := pullback.fst U.hom i (ψ.left y)
  refine ⟨U, g, u, ?_, hh⟩
  have hp : ψ.left ≫ pullback.snd U.hom i = Vk.hom :=
    MorphismProperty.Over.w ψ
  have hy' : a.left y = z := hy
  have hv : Vk.hom y = V.hom z := by
    have e := congrArg (fun k : Vk.left ⟶ Z ↦ k y) (MorphismProperty.Over.w a)
    exact e.symm.trans (congrArg V.hom hy')
  have ep := congrArg (fun k : (b.obj U).left ⟶ X ↦ k (ψ.left y))
    (pullback.condition (f := U.hom) (g := i))
  have ez := congrArg (fun k : Vk.left ⟶ Z ↦ k y) hp
  exact ep.trans (congrArg i (ez.trans hv))

end AlgebraicGeometry
