/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Finite free stalk lifts on an étale neighbourhood
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), finite generator lifting.
(blueprint: lem-weil-pbc-finite-free-constant-map-etale-factorization). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A finite free stalk map is represented by sections on one pointed neighbourhood.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), finite generator lifting.

Proof: Identify the stalk of the constant sheaf with its constant value. Represent the
images of the finitely many standard basis vectors under l by sections on pointed etale
neighbourhoods. Cofilteredness gives a common refinement. The finite free universal
property assembles their restrictions into t. The germ of each basis image is the
prescribed one, hence the displayed equality holds by linearity. For n = 0 the identity
neighbourhood and zero map suffice; the zero coefficient ring causes no exception. -/
private theorem exists_finite_free_stalk_sections
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (n : ℕ) (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F) :
    ∃ (V : X.Etale) (a : (pointSmallEtale (X.algClosurePoint x)).fiber.obj V)
      (t : (ModuleCat.of Λ (Fin n → Λ)) ⟶ F.obj.obj (Opposite.op V)),
      t ≫ (pointSmallEtale (X.algClosurePoint x)).toPresheafFiber V a F.obj =
        (CategoryTheory.toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Λ (Fin n → Λ)))).app (Opposite.op V) ≫
          (pointSmallEtale (X.algClosurePoint x)).toPresheafFiber V a
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))).obj ≫ l  := by
  classical
  let Φ := pointSmallEtale (X.algClosurePoint x)
  let P := ModuleCat.of Λ (Fin n → Λ)
  let B := Pi.basisFun Λ (Fin n)
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let m := (Φ.sheafFiberConstantSheafIso P).inv ≫ l
  have hi (i : Fin n) : ∃ (V : X.Etale) (a : Φ.fiber.obj V)
      (s : F.obj.obj (Opposite.op V)), Φ.toPresheafFiber V a F.obj s = m (B i) :=
    Φ.toPresheafFiber_jointly_surjective (m (B i))
  choose V a s hs using hi
  let j (i : Fin n) : Φ.fiber.Elements := Φ.fiber.elementsMk (V i) (a i)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let g (i : Fin n) : k ⟶ j i := (hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).some
  let t : P ⟶ F.obj.obj (Opposite.op k.1) := ConcreteCategory.ofHom
    (B.constr Λ (fun i ↦ F.obj.map (g i).1.op (s i)))
  refine ⟨k.1, k.2, t, ?_⟩
  have ht : t ≫ Φ.toPresheafFiber k.1 k.2 F.obj = m := by
    apply ModuleCat.hom_ext
    apply B.ext
    intro i
    have hw := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_w (g i).1 k.2 F.obj) (s i)
    have hg : Φ.fiber.map (g i).1 k.2 = a i := (g i).2
    change Φ.toPresheafFiber k.1 k.2 F.obj (t (B i)) = m (B i)
    have hti : t (B i) = F.obj.map (g i).1.op (s i) :=
      B.constr_basis Λ _ i
    rw [hti]
    exact
        (show Φ.toPresheafFiber k.1 k.2 F.obj (F.obj.map (g i).1.op (s i)) =
          Φ.toPresheafFiber (V i) (a i) F.obj (s i) by
          simpa only [ConcreteCategory.comp_apply, hg, j] using hw).trans (hs i)
  rw [ht]
  have hc : (CategoryTheory.toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj P)).app (Opposite.op k.1) ≫
      Φ.toPresheafFiber k.1 k.2
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P).obj =
      (Φ.sheafFiberConstantSheafIso P).inv := by
    apply (cancel_mono (Φ.sheafFiberConstantSheafIso P).hom).mp
    rw [Iso.inv_hom_id]
    dsimp only [GrothendieckTopology.Point.sheafFiberConstantSheafIso,
      Iso.trans_hom, Iso.symm_hom, asIso_inv]
    erw [Category.assoc, ← Φ.toPresheafFiber_naturality_assoc,
      IsIso.hom_inv_id_assoc, Φ.toPresheafFiber_presheafFiberConstIso_hom]
    rfl
  rw [← Category.assoc, hc]



set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Equality of germs of maps from a finite free module is witnessed on one refinement.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), equality after refinement.

Proof: Evaluate the germ equality on the finitely many standard basis vectors. Equality
in the filtered colimit defining the stalk gives a pointed refinement for each vector.
Cofilteredness gives a common refinement over V on which all these equalities hold.
Equality on the basis implies equality of the two linear maps. For rank zero the maps
are already equal and the identity refinement suffices. No finiteness of H is needed. -/
private theorem exists_finite_free_section_germ_equality
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (n : ℕ) (x : X) (V : X.Etale)
    (a : (pointSmallEtale (X.algClosurePoint x)).fiber.obj V)
    (s t : (ModuleCat.of Λ (Fin n → Λ)) ⟶ H.obj.obj (Opposite.op V))
    (h : s ≫ (pointSmallEtale (X.algClosurePoint x)).toPresheafFiber V a H.obj =
      t ≫ (pointSmallEtale (X.algClosurePoint x)).toPresheafFiber V a H.obj) :
    ∃ (W : X.Etale) (b : (pointSmallEtale (X.algClosurePoint x)).fiber.obj W)
      (r : W ⟶ V),
      (pointSmallEtale (X.algClosurePoint x)).fiber.map r b = a ∧
      s ≫ H.obj.map r.op = t ≫ H.obj.map r.op  := by
  classical
  let Φ := pointSmallEtale (X.algClosurePoint x)
  let B := Pi.basisFun Λ (Fin n)
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hi (i : Fin n) : ∃ (W : X.Etale) (r : W ⟶ V)
      (b : Φ.fiber.obj W), Φ.fiber.map r b = a ∧
      H.obj.map r.op (s (B i)) = H.obj.map r.op (t (B i)) := by
    apply (Φ.toPresheafFiber_eq_iff' V a (s (B i)) (t (B i))).mp
    exact ConcreteCategory.congr_hom h (B i)
  choose W r b hb he using hi
  let v : Φ.fiber.Elements := Φ.fiber.elementsMk V a
  let j (i : Fin n) : Φ.fiber.Elements := Φ.fiber.elementsMk (W i) (b i)
  let f (i : Fin n) : j i ⟶ v := Functor.Elements.homMk (r i) (hb i)
  obtain ⟨k, q, g, hg⟩ := IsCofiltered.wideCospan f
  refine ⟨k.1, k.2, q.1, q.2, ?_⟩
  apply ModuleCat.hom_ext
  apply B.ext
  intro i
  have hq : (g i).1 ≫ r i = q.1 := congrArg (fun m ↦ m.1) (hg i)
  have hei := congrArg (H.obj.map (g i).1.op) (he i)
  rw [← hq]
  simpa only [op_comp, H.obj.map_comp, ConcreteCategory.comp_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply] using hei



set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A compatible section map assembles into a factorization on the same etale object.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), assembly of lifted generators;
constant-sheaf adjunction, Stacks Project, Example 0H7J.

Proof: Pass to the site over V, whose terminal object is the identity of V. The
constant-sheaf/global-sections adjunction turns t into a map from the constant sheaf
to F.over V. The displayed equality says that composing this map with phi.over V
agrees with alpha.over V, by injectivity of that adjunction's hom equivalence.
Transport through the equivalence between sheaves on the over site and sheaves on
V.left. The pullback comparison for constant sheaves identifies the source with the
pullback of the original constant sheaf. Naturality gives exactly the conclusion.
This works for empty V, rank zero, and the zero ring; it uses no stalk hypothesis. -/
private theorem exists_finite_free_section_factorization
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) (n : ℕ)
    (α : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶ G)
    (V : X.Etale)
    (t : (ModuleCat.of Λ (Fin n → Λ)) ⟶ F.obj.obj (Opposite.op V))
    (h : t ≫ φ.hom.app (Opposite.op V) =
      (CategoryTheory.toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Λ (Fin n → Λ)))).app (Opposite.op V) ≫
        α.hom.app (Opposite.op V)) :
    ∃ (β : (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F),
      β ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map α := by
  let A := ModuleCat.{u + 1} Λ
  let J := X.smallEtaleTopology
  let P := ModuleCat.of Λ (Fin n → Λ)
  let Q := (constantSheaf J A).obj P
  let R := J.overPullback A V
  let adj := constantSheafAdj (J.over V) A Over.mkIdTerminal
  let c := constantSheafOverIso J A V P
  let γ := (adj.homEquiv P (F.over V)).symm t
  have hγ : γ ≫ R.map φ = c.hom ≫ R.map α := by
    apply (adj.homEquiv P (G.over V)).injective
    rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
    simp only [γ, Equiv.apply_symm_apply]
    change t ≫ φ.hom.app (Opposite.op V) =
      adj.homEquiv P (Q.over V) c.hom ≫ α.hom.app (Opposite.op V)
    change t ≫ φ.hom.app (Opposite.op V) =
      (constantSheafAdj (J.over V) A Over.mkIdTerminal).homEquiv P _
        (constantSheafOverHom J A V P) ≫ α.hom.app (Opposite.op V)
    rw [constantSheafAdj_homEquiv_constantSheafOverHom]
    exact h
  let δ : Q.over V ⟶ F.over V := c.inv ≫ γ
  have hδ : δ ≫ R.map φ = R.map α := by
    dsimp [δ]
    rw [Category.assoc, hγ, Iso.inv_hom_id_assoc]
  let E := (Etale.overSheafEquiv V A).functor
  let eQ := overSheafEquivFunctorObjOverIso A V Q
  let eF := overSheafEquivFunctorObjOverIso A V F
  refine ⟨eQ.inv ≫ E.map δ ≫ eF.hom, ?_⟩
  have nat (H K : Sheaf J A) (f : H ⟶ K) :
      (overSheafEquivFunctorObjOverIso A V H).hom ≫
          (Etale.upperStar A V.hom).map f =
        E.map (R.map f) ≫ (overSheafEquivFunctorObjOverIso A V K).hom := by
    dsimp only [overSheafEquivFunctorObjOverIso]
    simp only [Iso.trans_hom, Iso.symm_hom]
    erw [Category.assoc,
      ← (GrothendieckTopology.upperStarIsoLocalizationRestriction A
        @Etale @Etale le_rfl V.hom V.prop).inv.naturality]
    simp only [← Category.assoc]
    congr 1
    apply (sheafToPresheaf V.left.smallEtaleTopology A).map_injective
    ext U
    dsimp
    exact ConcreteCategory.congr_hom
      (f.hom.naturality (V.etaleToOverCompForgetIso.inv.app (Opposite.unop U)).op) _
  rw [Category.assoc, Category.assoc, nat F G φ, ← Category.assoc (E.map δ),
    ← E.map_comp, hδ]
  rw [← nat Q G α, Iso.inv_hom_id_assoc]



set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite free étale-local lifting step used by the open factorization theorem.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), finite generator lifting.
(blueprint: lem-weil-pbc-finite-free-constant-map-etale-factorization).

Proof: If n = 0, take the identity etale neighbourhood and the unique zero map.
For n > 0, write the standard basis of Λ^(Fin n).  The definition of the geometric
stalk is a filtered colimit over pointed etale neighbourhoods, so each image under l
is represented by a section of F on one such neighbourhood.  Cofilteredness of pointed
etale neighbourhoods gives one common refinement for the finitely many representatives.
The equality hl says that the two resulting germs in G agree.  Equality in the same
filtered colimit therefore gives a further common refinement on which the equalities
hold as sections.  The finite free universal property assembles these sections into a
Λ-linear map from Λ^(Fin n) to sections of F on that neighbourhood.  The
constant-sheaf/global-sections adjunction, together with the pullback comparison for
the constant sheaf, turns this linear map into β.  Checking on the standard basis gives
β ≫ upperStar(V.hom).map φ = upperStar(V.hom).map α.  The chosen pointed neighbourhood
contains x, so x lies in the range of V.hom.  This argument uses no monicity of φ and
works for the zero ring as well. -/
theorem exists_etale_factorization_of_finite_free_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) (n : ℕ)
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin n → Λ)) ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (V : X.Etale) (_hx : x ∈ Set.range V.hom)
      (β : (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Fin n → Λ))) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F),
      β ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map α := by
  classical
  let Φ := pointSmallEtale (X.algClosurePoint x)
  let P := ModuleCat.of Λ (Fin n → Λ)
  let Q := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj P
  let c := CategoryTheory.toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj P)
  obtain ⟨V, a, t, ht⟩ := exists_finite_free_stalk_sections n x l
  have hg : (t ≫ φ.hom.app (Opposite.op V)) ≫ Φ.toPresheafFiber V a G.obj =
      (c.app (Opposite.op V) ≫ α.hom.app (Opposite.op V)) ≫
        Φ.toPresheafFiber V a G.obj := by
    change l ≫ Φ.presheafFiber.map φ.hom = Φ.presheafFiber.map α.hom at hl
    calc
      _ = t ≫ Φ.toPresheafFiber V a F.obj ≫ Φ.presheafFiber.map φ.hom := by
        rw [Category.assoc, Φ.toPresheafFiber_naturality]
      _ = c.app (Opposite.op V) ≫ Φ.toPresheafFiber V a Q.obj ≫
          l ≫ Φ.presheafFiber.map φ.hom := by
        rw [← Category.assoc, ht]
        simp only [Category.assoc]
        rfl
      _ = c.app (Opposite.op V) ≫ Φ.toPresheafFiber V a Q.obj ≫
          Φ.presheafFiber.map α.hom := by rw [hl]
      _ = _ := by rw [Φ.toPresheafFiber_naturality, Category.assoc]
  obtain ⟨W, b, r, hr, he⟩ := exists_finite_free_section_germ_equality n x V a
    (t ≫ φ.hom.app (Opposite.op V))
    (c.app (Opposite.op V) ≫ α.hom.app (Opposite.op V)) hg
  have hs : (t ≫ F.obj.map r.op) ≫ φ.hom.app (Opposite.op W) =
      c.app (Opposite.op W) ≫ α.hom.app (Opposite.op W) := by
    calc
      _ = (t ≫ φ.hom.app (Opposite.op V)) ≫ G.obj.map r.op := by
        rw [Category.assoc, φ.hom.naturality, Category.assoc]
      _ = (c.app (Opposite.op V) ≫ α.hom.app (Opposite.op V)) ≫
          G.obj.map r.op := he
      _ = (c.app (Opposite.op V) ≫ Q.obj.map r.op) ≫
          α.hom.app (Opposite.op W) := by
        rw [Category.assoc, ← α.hom.naturality, Category.assoc]
      _ = _ := by
        have hc : c.app (Opposite.op V) ≫ Q.obj.map r.op =
            c.app (Opposite.op W) := by
          exact (c.naturality r.op).symm.trans (Category.id_comp _)
        rw [hc]
  obtain ⟨β, hβ⟩ := exists_finite_free_section_factorization φ n α W
    (t ≫ F.obj.map r.op) hs
  refine ⟨W, ?_, β, hβ⟩
  let w := pointSmallEtaleFiberObjToPreimage (X.algClosurePoint x)
    (X.algClosurePoint_base x default) b
  exact ⟨w.1, w.2⟩

end AlgebraicGeometry.Scheme
