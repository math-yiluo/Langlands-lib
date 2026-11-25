/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Pullback compatibility of the Artin--Schreier rows -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- Artin--Schreier rows commute with structural pullback of regular functions.
Source: Stacks Project, Tag 0A3J, opening sequence and its functoriality.
(blueprint: lem-pbc-artin-schreier-pullback-rows)

Proof: On U over C, map a section to its pullback along U ×_C C' → U,
using a and a' to identify both section groups with regular functions.
The pullback square and the naturality of a and a' make this a morphism
G → lowerStar G'. Its adjoint is q and satisfies the displayed section formula.
Ring pullback commutes with powers and subtraction. The adjunction, applied to
that sectionwise equality, proves the square with wp and wp'. Let i' be the
constant-sheaf comparison upperStar(constant Z/p) ≅ constant Z/p on C',
followed by i0. Both composites from the pulled-back constant sheaf agree on
the constant-presheaf unit: they send c to c.val times one. The sheafification
universal property and the adjunction prove the square with i. Transport the
second given short exact sequence by this constant-sheaf isomorphism; its
middle and right terms stay fixed. This gives z' and short exactness. The
construction also works on empty schemes; it asserts no cohomology comparison. -/
theorem exists_artinSchreier_pullback_rows
    {C C' : Scheme.{u}} (ι' : C' ⟶ C) (p : ℕ) [Fact p.Prime]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (wp : G ⟶ G) (wp' : G' ⟶ G')
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hwp' : ∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
      a' U (wp'.hom.app U x) = (a' U x) ^ p - a' U x)
    (i : C.constantZMod p ⟶ G) (i0 : C'.constantZMod p ⟶ G')
    (hi : ∀ (U : C.Etaleᵒᵖ) (c : ZMod p),
      a U (i.hom.app U
        ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)))
    (hi0 : ∀ (U : C'.Etaleᵒᵖ) (c : ZMod p),
      a' U (i0.hom.app U
        ((toSheafify C'.smallEtaleTopology
          ((Functor.const C'.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤)))
    (z0 : i0 ≫ wp' = 0) (hs0 : (ShortComplex.mk i0 wp' z0).ShortExact) :
    ∃ (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
      (i' : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj (C.constantZMod p) ⟶ G')
      (z' : i' ≫ wp' = 0),
      (ShortComplex.mk i' wp' z').ShortExact ∧
      (Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q = i' ∧
      (Etale.upperStar AddCommGrpCat.{u + 1} ι').map wp ≫ q = q ≫ wp' ∧
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ ι'
  let t : G ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} ι').obj G' :=
    ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
          ((a' (Opposite.op (B.obj U.unop))).symm.toAddMonoidHom.comp
            ((Limits.pullback.fst U.unop.hom ι').appTop.hom.toAddMonoidHom.comp
              (a U).toAddMonoidHom))
       naturality := by
         intro U V g
         ext x
         apply (a' (Opposite.op (B.obj V.unop))).injective
         change a' _ ((a' _).symm
             ((Limits.pullback.fst V.unop.hom ι').appTop
               (a V (G.obj.map g x)))) =
           a' _ (G'.obj.map (B.map g.unop).op
             ((a' _).symm ((Limits.pullback.fst U.unop.hom ι').appTop (a U x))))
         rw [AddEquiv.apply_symm_apply, ha, ha', AddEquiv.apply_symm_apply]
         change (Limits.pullback.fst V.unop.hom ι').appTop
             (g.unop.left.appTop (a U x)) =
           (B.map g.unop).left.appTop
             ((Limits.pullback.fst U.unop.hom ι').appTop (a U x))
         have h : (B.map g.unop).left ≫ Limits.pullback.fst U.unop.hom ι' =
             Limits.pullback.fst V.unop.hom ι' ≫ g.unop.left := by
           dsimp [B, MorphismProperty.Over.pullback]
           simp
         have hh := congrArg
           (fun f : Limits.pullback V.unop.hom ι' ⟶ U.unop.left ↦ f.appTop (a U x)) h
         simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hh
         exact hh.symm }⟩
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι'
  let q := (adj.homEquiv G G').symm t
  have ht : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a' (Opposite.op (B.obj U.unop)) (t.hom.app U x) =
        (Limits.pullback.fst U.unop.hom ι').appTop (a U x) := by
    intro U x
    exact (a' _).apply_symm_apply _
  have hw : wp ≫ t = t ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} ι').map wp' := by
    ext U x
    apply (a' (Opposite.op (B.obj U.unop))).injective
    change a' (Opposite.op (B.obj U.unop)) (t.hom.app U (wp.hom.app U x)) =
      a' (Opposite.op (B.obj U.unop))
        (wp'.hom.app (Opposite.op (B.obj U.unop)) (t.hom.app U x))
    rw [ht, hwp, hwp', ht]
    simp only [map_sub, map_pow]
  have hwq : (Etale.upperStar AddCommGrpCat.{u + 1} ι').map wp ≫ q = q ≫ wp' := by
    exact adj.homEquiv_naturality_right_square wp t t wp' hw
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} ι').app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))
  let i' := e.hom ≫ i0
  have z' : i' ≫ wp' = 0 := by simp [i', Category.assoc, z0]
  refine ⟨q, i', z', ?_, ?_, hwq, ?_⟩
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e (Iso.refl G') (Iso.refl G')
        (by simp [i']) (by simp)).symm hs0
  · let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod p))
    let ca := constantSheafAdj C.smallEtaleTopology AddCommGrpCat.{u + 1}
      Limits.terminalIsTerminal
    let cb := constantSheafAdj C'.smallEtaleTopology AddCommGrpCat.{u + 1}
      Limits.terminalIsTerminal
    let secIso := Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} ι'
    let aa := (ca.comp adj).ofNatIsoRight secIso
    have he : aa.homEquiv M G' (e.hom ≫ i0) = cb.homEquiv M G' i0 := by
      rw [Adjunction.homEquiv_naturality_right]
      have h := Adjunction.homEquiv_leftAdjointUniq_hom_app aa cb M
      change aa.homEquiv M ((constantSheaf C'.smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj M) e.hom = cb.unit.app M at h
      rw [h]
      exact (cb.homEquiv_unit M G' i0).symm
    apply (aa.homEquiv M G').injective
    change aa.homEquiv M G' ((Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q) =
      aa.homEquiv M G' (e.hom ≫ i0)
    rw [he]
    dsimp only [aa]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change ca.homEquiv M _ (adj.homEquiv _ G'
        ((Etale.upperStar AddCommGrpCat.{u + 1} ι').map i ≫ q)) ≫ _ = _
    rw [Adjunction.homEquiv_naturality_left]
    rw [show adj.homEquiv G G' q = t from (adj.homEquiv G G').apply_symm_apply t]
    ext c
    rcases c with ⟨c⟩
    apply (a' (Opposite.op (⊤_ C'.Etale))).injective
    simp only [ca, cb, constantSheafAdj_homEquiv_apply, AddCommGrpCat.comp_apply,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    dsimp only [secIso, Etale.lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents,
      NatTrans.app, Functor.mapIso, Iso.op, Iso.symm]
    erw [ha' _ _ (Limits.PreservesTerminal.iso (Scheme.Hom.Etale ι')).inv.op]
    erw [ht (Opposite.op (⊤_ C.Etale)), hi, hi0]
    simp only [map_natCast]
  · intro U x
    change a' _ (((adj.homEquiv G G') q).hom.app U x) = _
    rw [show adj.homEquiv G G' q = t from (adj.homEquiv G G').apply_symm_apply t]
    exact ht U x

end AlgebraicGeometry.IsCurve
