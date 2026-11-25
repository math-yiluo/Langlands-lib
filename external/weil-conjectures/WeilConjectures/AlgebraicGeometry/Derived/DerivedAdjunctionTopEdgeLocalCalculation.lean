/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
import WeilConjectures.AlgebraicGeometry.Derived.DerivedDirectImageSingleEdge
import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalClassEdge
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Local normalization of the truncated derived counit
Source: Stacks, cohomology.tex, Tags 079W, 0BKJ and 0D5X;
derived.tex, Tags 08J5 and 06XS.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w uA vA wA uB vB wB
open CategoryTheory TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem transpose_top_square
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (L : D ⥤ E) (l : A ⥤ B) (r : B ⥤ A) (a : l ⊣ r) (H : D ⥤ A) (H' : E ⥤ B)
    {P P' : D} {K K' : E} (f : P ⟶ P') (k : K ⟶ K')
    (d : L.obj P ⟶ K) (d' : L.obj P' ⟶ K')
    (hd : L.map f ≫ d' = d ≫ k)
    (κ : H'.obj (L.obj P) ⟶ l.obj (H.obj P))
    (κ' : H'.obj (L.obj P') ⟶ l.obj (H.obj P')) [IsIso κ] [IsIso κ']
    (hκ : H'.map (L.map f) ≫ κ' = κ ≫ l.map (H.map f)) :
    a.homEquiv _ _ (inv κ ≫ H'.map d) ≫ r.map (H'.map k) =
      H.map f ≫ a.homEquiv _ _ (inv κ' ≫ H'.map d') := by
  have hi : inv κ ≫ H'.map (L.map f) = l.map (H.map f) ≫ inv κ' := by
    apply (cancel_mono κ').1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc] using congrArg (fun z ↦ inv κ ≫ z) hκ
  rw [← a.homEquiv_naturality_right, Category.assoc, ← H'.map_comp, ← hd,
    H'.map_comp, ← Category.assoc, hi, Category.assoc, a.homEquiv_naturality_left]

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem paste_naturality_squares
    {C : Type*} [Category C] {X Y P Q M N : C}
    {f : X ⟶ Y} {p : X ⟶ P} {q : Y ⟶ Q} {g : P ⟶ Q}
    {a : P ⟶ M} {b : Q ⟶ N} {k : M ⟶ N}
    (h₁ : f ≫ q = p ≫ g) (h₂ : g ≫ b = a ≫ k) :
    f ≫ (q ≫ b) = (p ≫ a) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private theorem truncatedCounit_naturality {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) {K K' : schemeDerivedCategory T} (k : K ⟶ K') :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        ((schemeDerivedDirectImage g).map k) ≫ topEdgeTruncatedCounit g q K' =
      topEdgeTruncatedCounit g q K ≫ (Scheme.Modules.pushforward g).map
        ((DerivedCategory.homologyFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map k) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let R := schemeDerivedDirectImage g
  let P := (t.truncLE q).obj (R.obj K)
  let P' := (t.truncLE q).obj (R.obj K')
  let i := (t.truncLEι q).app (R.obj K)
  let i' := (t.truncLEι q).app (R.obj K')
  let f := (t.truncLE q).map (R.map k)
  let adj := @pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let d := (adj.homEquiv P K).symm i
  let d' := (adj.homEquiv P' K').symm i'
  have hP : P.IsLE q := by dsimp [P]; infer_instance
  have hP' : P'.IsLE q := by dsimp [P']; infer_instance
  have hi : f ≫ i' = i ≫ R.map k := (t.truncLEι q).naturality (R.map k)
  have hd : (derivedPullback g).map f ≫ d' = d ≫ k := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    change f ≫ (adj.homEquiv P' K') d' = (adj.homEquiv P K) d ≫ R.map k
    simpa only [d, d', Equiv.apply_symm_apply] using hi
  have := (derivedPullback_topCohomology g q P hP).choose_spec.2.1
  have := (derivedPullback_topCohomology g q P' hP').choose_spec.2.1
  have hκ := (derivedPullback_topCohomology g q P hP).choose_spec.2.2.1 P' hP' f
  have hh := transpose_top_square (derivedPullback g)
    (Scheme.Modules.tensorPullback g) (Scheme.Modules.pushforward g) a HS HT f k d d' hd
    (derivedPullbackTopCohomology g q P hP)
    (derivedPullbackTopCohomology g q P' hP') hκ
  have hii : IsIso (HS.map i) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (q + 1) q (by omega)
  have hii' : IsIso (HS.map i') :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (q + 1) q (by omega)
  have hf : HS.map (R.map k) ≫ inv (HS.map i') = inv (HS.map i) ≫ HS.map f := by
    apply (cancel_epi (HS.map i)).1
    apply (cancel_mono (HS.map i')).1
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id,
      Category.comp_id, ← HS.map_comp] using congrArg HS.map hi.symm
  change HS.map (R.map k) ≫ (inv (HS.map i') ≫
      a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q P' hP') ≫ HT.map d')) =
    (inv (HS.map i) ≫
      a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q P hP) ≫ HT.map d)) ≫ _
  exact paste_naturality_squares hf hh.symm

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem natural_edges_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
    (F : A ⥤ B) (q : ℤ)
    (hR : ∀ (K : DerivedCategory A) (n : ℤ), K.IsGE n → (R.obj K).IsGE n)
    (e e' : ∀ K : DerivedCategory A,
      (DerivedCategory.homologyFunctor B q).obj (R.obj K) ⟶
        F.obj ((DerivedCategory.homologyFunctor A q).obj K))
    (he : ∀ {K K' : DerivedCategory A} (k : K ⟶ K'),
      (DerivedCategory.homologyFunctor B q).map (R.map k) ≫ e K' =
        e K ≫ F.map ((DerivedCategory.homologyFunctor A q).map k))
    (he' : ∀ {K K' : DerivedCategory A} (k : K ⟶ K'),
      (DerivedCategory.homologyFunctor B q).map (R.map k) ≫ e' K' =
        e' K ≫ F.map ((DerivedCategory.homologyFunctor A q).map k))
    (hs : ∀ M : A, e ((DerivedCategory.singleFunctor A q).obj M) =
      e' ((DerivedCategory.singleFunctor A q).obj M)) (K : DerivedCategory A) :
    e K = e' K := by
  let H := DerivedCategory.homologyFunctor B q
  let H' := DerivedCategory.homologyFunctor A q
  let t := DerivedCategory.TStructure.t (C := A)
  have transport {X Y : DerivedCategory A} (i : X ≅ Y) (hy : e Y = e' Y) :
      e X = e' X := by
    apply (cancel_mono (F.map (H'.map i.hom))).1
    rw [← he i.hom, ← he' i.hom, hy]
  have hge (J : DerivedCategory A) (hJ : J.IsGE q) : e J = e' J := by
    have := hJ
    let P := (t.truncLE q).obj J
    have : P.IsLE q := by dsimp [P]; infer_instance
    have : P.IsGE q := by dsimp [P]; infer_instance
    obtain ⟨M, ⟨i⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE P q
    have hP : e P = e' P := transport i (hs M)
    let j := (t.truncLEι q).app J
    let T := R.mapTriangle.obj ((t.triangleLTGE (q + 1)).obj J)
    have hT : T ∈ distTriang _ :=
      R.map_distinguished _ (t.triangleLTGE_distinguished (q + 1) J)
    have hZ : T.obj₃.IsGE (q + 1) := hR _ _ (by infer_instance)
    have : IsIso (H.map (R.map j)) :=
      DerivedCategory.isIso_homologyMap_mor₁ T hT (q - 1) q (by omega)
        (DerivedCategory.isZero_of_isGE _ (q + 1) (q - 1) (by omega))
        (DerivedCategory.isZero_of_isGE _ (q + 1) q (by omega))
    apply (cancel_epi (H.map (R.map j))).1
    rw [he (K := P) (K' := J) j, he' (K := P) (K' := J) j, hP]
  let j := (t.truncGEπ q).app K
  have : IsIso (H'.map j) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K q q le_rfl
  apply (cancel_mono (F.map (H'.map j))).1
  rw [← he (K := K) (K' := (t.truncGE q).obj K) j,
    ← he' (K := K) (K' := (t.truncGE q).obj K) j, hge _ (by infer_instance)]

-- This is the standard bounded-below right-derived-functor comparison. Keeping it
-- local avoids importing an etale constructibility module just for this generic fact.
private theorem directImage_isGE {T S : Scheme.{u}} (g : T ⟶ S)
    (K : schemeDerivedCategory T) (n : ℤ) (hK : K.IsGE n) :
    ((schemeDerivedDirectImage g).obj K).IsGE n := by
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let K' : DerivedCategory.Plus (SheafOfModules.{u} (moduleRings T.toRingedSpace)) :=
    ⟨K, ⟨n, hK⟩⟩
  have : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 hK
  refine (DerivedCategory.isGE_iff _ n).2 fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K' n hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K')).symm

/-- The counit on the upper truncation of Rg_*K has the canonical local-class formula.
This assertion has no variable source C and no assertion about arbitrary adjuncts.
Source: Stacks, cohomology.tex, Tags 079W (normalized derived adjunction),
0BKJ (local classes), 0D5X (local Leray); derived.tex, Tags 08J5 and 06XS.
(blueprint: lem-weil-pbc-truncated-counit-local-class).

Proof: Construct the local-class edge e by sheafifying the inverse-open local
cocycle maps. It is natural in K, and its value on a single complex is normalized by
the right-derived unit. The explicit truncated counit is also natural: use naturality
of upper truncation and kappa, and the two adjunction bijections. On a single complex,
transpose the ordinary module counit using the pinned derived adjunction. The explicit
kappa on a single gives the same normalization, so the two edges agree there after
cancelling the invertible degree-q single direct-image comparison.
Two natural edges Hq(RK) -> g_* Hq(K) agreeing on singles agree everywhere. Project K
to J = tau_{>=q} K and cancel g_* Hq of this projection. For J at least q, include
P = tau_{<=q} J. This P is a single. The cone of P -> J is at least q+1, and the
right-derived direct image preserves this lower bound, so Hq(R(P -> J)) is invertible
by the homology sequence. Naturality and cancellation reduce equality on J to P.
Replace e by the now equal truncated counit in the sectionwise local-class equation.
The argument imposes no lower bound on K and works for all integer q, zero objects,
empty opens, and nonflat g. All local maps retain the fixed resolutions and scalar
actions from the data module. -/
theorem topEdgeTruncatedCounit_localClass {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (K : schemeDerivedCategory T) :
    ∀ V : (Opens S)ᵒᵖ,
      (RingedSpace.topEdgeLocalClass S.toRingedSpace q
        ((schemeDerivedDirectImage g).obj K)).app V ≫
        ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map
          (topEdgeTruncatedCounit g q K)).hom.app V =
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
        (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V := by
  obtain ⟨e, he, hn, hs⟩ := exists_topEdgeLocalClassEdge g q
  have hsingle (M : T.Modules) :
      topEdgeTruncatedCounit g q ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) =
        e ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) := by
    have h := topEdgeSingleDirectImageMap_counit g q M
    have := (hs M).1
    apply (cancel_epi ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        (topEdgeSingleDirectImageMap g q M))).1
    exact h.trans (hs M).2.symm
  have h := natural_edges_ext (schemeDerivedDirectImage g) (Scheme.Modules.pushforward g) q
    (directImage_isGE g) (topEdgeTruncatedCounit g q) e
    (truncatedCounit_naturality g q) hn hsingle K
  simpa only [h] using he K

end AlgebraicGeometry
