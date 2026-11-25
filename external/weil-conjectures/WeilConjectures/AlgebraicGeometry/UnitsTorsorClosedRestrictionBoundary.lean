/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction

/-!
# Boundary comparison for a pulled-back direct-image extension

Source: Stacks Project, Tags 02UV and 02FQ.
(blueprint: lem-sc-units-extension-pullback-boundary-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
private lemma equiv_zero_one (Y : Scheme.{u}) :
    (Sheaf.H.equiv₀
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) isTerminalTop).symm
      ((toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩) =
      Abelian.Ext.mk₀ (𝟙 _) := by
  apply (Sheaf.H.equiv₀ _ isTerminalTop).injective
  rw [AddEquiv.apply_symm_apply]
  have h : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀
      (𝟙 ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))) = 𝟙 _ :=
    Abelian.Ext.addEquiv₀.apply_symm_apply _
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_id]
  rfl


set_option backward.defeqAttrib.useBackward true in
/-- The inverse-image/counit comparison carries the boundary of one in the pullback
of a direct-image extension to the boundary of one in the original extension.

Source: Stacks Project, Cohomology of Sheaves, Lemma 02UV and the naturality of
connecting homomorphisms used in Lemma 02FQ.
(blueprint: lem-sc-units-extension-pullback-boundary-comparison).

Proof: Apply exact inverse image to the short exact pullback extension. Compose its
map to the inverse image of the direct-image extension with the counit. Naturality
of the counit makes this a map of short exact sequences to the original extension.
On the kernel its map is the counit of the units sheaf, because the first projection
of k is the direct image of a. On the quotient, the comparison of constant integer
sheaves and the restriction identity for r carry the section one to one. The Ext
boundary is composition with the extension class. Exact inverse image preserves
extension classes, and naturality of the extension class for this map of sequences
therefore gives the displayed equality, after precomposition with the constant
sheaf comparison. This is precisely the definition of
unitsPushforwardCohomologyComparison. The argument also applies to an empty Z,
where the original boundary is zero. -/
theorem units_extension_pullback_boundary_comparison
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (E : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : Z.unitsSheaf ⟶ E)
    (p : E ⟶ (constantSheaf (Opens.grothendieckTopology Z)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (w : a ≫ p = 0) (hS : (ShortComplex.mk a p w).ShortExact)
    (r : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      ((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj
        ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hr : ∀ (U : Opens X) (n : ℤ),
      r.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op U) ⟨n⟩) =
        (toSheafify (Opens.grothendieckTopology Z)
          ((Functor.const (Opens Z)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app
              (op ((Opens.map i.base).obj U)) ⟨n⟩)
    (k : ((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj Z.unitsSheaf ⟶
      pullback (((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).map p) r)
    (hkfst : k ≫ pullback.fst _ _ =
      ((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).map a)
    (hk : k ≫ pullback.snd _ _ = 0)
    (hP : (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact) :
    unitsPushforwardCohomologyComparison i 1
      (Sheaf.H.δSections hP isTerminalTop
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)) =
      Sheaf.H.δSections hS isTerminalTop
        ((toSheafify (Opens.grothendieckTopology Z)
          ((Functor.const (Opens Z)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩) := by
  -- Reuse the ambient sheaf and Ext instances throughout the comparison.
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u} := inferInstance
  let : Abelian (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  let : Abelian (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) := inferInstance
  let g := Opens.map i.base
  let R := g.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  have : R.IsRightAdjoint := inferInstance
  let L := g.sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let adj : L ⊣ R := g.sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
  let := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) g
  let : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  let : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  have : L.PreservesZeroMorphisms := inferInstance
  let := preservesBinaryBiproducts_of_preservesBinaryProducts L
  let := Functor.additive_of_preservesBinaryBiproducts L
  let S := ShortComplex.mk a p w
  let P : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    ShortComplex.mk k (pullback.snd _ _) hk
  let e := (g.constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
    isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))
  let φ : P.map L ⟶ S :=
    { τ₁ := adj.counit.app Z.unitsSheaf
      τ₂ := L.map (pullback.fst _ _) ≫ adj.counit.app E
      τ₃ := L.map r ≫ adj.counit.app S.X₃
      comm₁₂ := by
        change adj.counit.app Z.unitsSheaf ≫ a =
          L.map k ≫ (L.map (pullback.fst _ _) ≫ adj.counit.app E)
        rw [← Category.assoc, ← L.map_comp, hkfst]
        exact (adj.counit_naturality a).symm
      comm₂₃ := by
        change (L.map (pullback.fst _ _) ≫ adj.counit.app E) ≫ p =
          L.map (pullback.snd _ _) ≫ (L.map r ≫ adj.counit.app S.X₃)
        rw [Category.assoc, ← adj.counit_naturality p,
          ← Category.assoc, ← L.map_comp, pullback.condition,
          L.map_comp, Category.assoc] }
  have hδP : Sheaf.H.δSections hP isTerminalTop
      ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩) = hP.extClass := by
    rw [Sheaf.H.δ_apply, equiv_zero_one, Abelian.Ext.mk₀_id_comp]
  have hδS : Sheaf.H.δSections hS isTerminalTop
      ((toSheafify (Opens.grothendieckTopology Z)
        ((Functor.const (Opens Z)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩) = hS.extClass := by
    rw [Sheaf.H.δ_apply, equiv_zero_one, Abelian.Ext.mk₀_id_comp]
  rw [hδP, hδS]
  change Sheaf.H.map (adj.counit.app Z.unitsSheaf) 1
    (Sheaf.H.mapFunctor L e (R.obj Z.unitsSheaf) 1 hP.extClass) = hS.extClass
  rw [Sheaf.H.map_apply, Sheaf.H.mapFunctor_apply,
    Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)]
  have hn : (hP.extClass.mapExactFunctor L).comp (Abelian.Ext.mk₀ φ.τ₁)
      (add_zero 1) = (Abelian.Ext.mk₀ φ.τ₃).comp hS.extClass (zero_add 1) := by
    rw [Abelian.Ext.mapExactFunctor_extClass]
    exact (hP.map_of_exact L).extClass_naturality hS φ
  rw [hn, ← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
    Abelian.Ext.mk₀_comp_mk₀]
  have he : e.hom ≫ φ.τ₃ = 𝟙 _ := by
    have h3 : φ.τ₃ = e.inv := by
      let adjX := constantSheafAdj (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} isTerminalTop
      let adjZ := constantSheafAdj (Opens.grothendieckTopology Z)
        AddCommGrpCat.{u} isTerminalTop
      let adjC := (adjX.comp adj).ofNatIsoRight
        (g.sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z) (op ⊤))
      apply (adjC.homEquiv _ _).injective
      have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app adjC adjZ
        (AddCommGrpCat.of (ULift.{u} ℤ))
      change adjC.homEquiv _ _ e.inv = adjZ.unit.app _ at hu
      rw [hu]
      change adjX.homEquiv _ (R.obj S.X₃) (adj.homEquiv _ S.X₃
        (L.map r ≫ adj.counit.app S.X₃)) = adjZ.unit.app _
      have ha : adj.homEquiv _ S.X₃
          (L.map r ≫ adj.counit.app S.X₃) = r := by
        rw [← adj.homEquiv_symm_apply _ S.X₃ r]
        exact (adj.homEquiv _ S.X₃).apply_symm_apply r
      rw [ha]
      ext n
      rcases n with ⟨n⟩
      change r.hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨n⟩) = _
      exact hr ⊤ n
    rw [h3, e.hom_inv_id]
  rw [he, Abelian.Ext.mk₀_id_comp]

end AlgebraicGeometry.Scheme
