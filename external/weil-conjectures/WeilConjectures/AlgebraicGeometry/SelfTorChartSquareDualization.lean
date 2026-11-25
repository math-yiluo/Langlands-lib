/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorCompatibleAffineMaps
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Dualizing one affine self-Tor coordinate square

Source: Stacks Project, Tag 01CM (internal Hom on smaller opens).
(blueprint: new-n1-self-tor-chart-square-dualization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Precompose local dual sections with a morphism on O.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private noncomputable def chartRestrictedDualMap
    {Z : Scheme.{u}} (O V : Z.Opens) {E Q : Z.Modules}
    (φ : E.over O ⟶ Q.over O) :
    (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual Q)).over
      (V.ι ⁻¹ᵁ O)) ⟶
    (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual E)).over
      (V.ι ⁻¹ᵁ O)) :=
  { val :=
    { app := fun D ↦ ModuleCat.ofHom
        { toFun := fun ψ ↦
            PresheafOfModules.restrictOverMap
              (homOfLE ((V.ι.image_mono (leOfHom D.unop.hom)).trans
                (V.ι.image_preimage_le O))) φ.val ≫ ψ
          map_add' := by
            intro ψ χ
            apply PresheafOfModules.hom_ext
            intro A
            ext x
            rfl
          map_smul' := by
            intro r ψ
            apply PresheafOfModules.hom_ext
            intro A
            ext x
            rfl }
      naturality := by
        intro D D' g
        ext ψ
        rfl } }

/-- Precomposition by the identity leaves every dual section unchanged.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private theorem chartRestrictedDualMap_id {Z : Scheme.{u}} (O V : Z.Opens)
    (E : Z.Modules) : chartRestrictedDualMap O V (𝟙 (E.over O)) = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro D
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  rfl

/-- Precomposition reverses the order of two local morphisms.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private theorem chartRestrictedDualMap_comp {Z : Scheme.{u}} (O V : Z.Opens)
    {E Q P : Z.Modules} (φ : E.over O ⟶ Q.over O) (χ : Q.over O ⟶ P.over O) :
    chartRestrictedDualMap O V (φ ≫ χ) =
      chartRestrictedDualMap O V χ ≫ chartRestrictedDualMap O V φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro D
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  rfl

/-- The local operation on a global map is its restricted transpose.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private theorem chartRestrictedDualMap_global {Z : Scheme.{u}} (O V : Z.Opens)
    {E Q : Z.Modules} (τ : E ⟶ Q) :
    chartRestrictedDualMap O V (τ.over O) =
      ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over
        (V.ι ⁻¹ᵁ O) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro D
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  rfl

/-- A local isomorphism induces an isomorphism of restricted duals.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private noncomputable def chartRestrictedDualIso {Z : Scheme.{u}} (O V : Z.Opens)
    {E Q : Z.Modules} (e : E.over O ≅ Q.over O) :
    (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual Q)).over
      (V.ι ⁻¹ᵁ O)) ≅
    (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual E)).over
      (V.ι ⁻¹ᵁ O)) where
  hom := chartRestrictedDualMap O V e.hom
  inv := chartRestrictedDualMap O V e.inv
  hom_inv_id := by
    rw [← chartRestrictedDualMap_comp, e.inv_hom_id, chartRestrictedDualMap_id]
  inv_hom_id := by
    rw [← chartRestrictedDualMap_comp, e.hom_inv_id, chartRestrictedDualMap_id]

/-- Dualize a single local coordinate square and restrict to V intersect O.
Source: Stacks Project, Tag 01CM.
(blueprint: new-n1-self-tor-chart-square-dualization). -/
private theorem dualizeLocalCoordinateSquare {Z : Scheme.{u}} (O V : Z.Opens)
    {E Q A B : Z.Modules} (τ : E ⟶ Q) (c : A ⟶ B)
    (s : E.over O ≅ A.over O) (t : B.over O ≅ Q.over O)
    (h : τ.over O = s.hom ≫ c.over O ≫ t.hom) :
    ∃ (a : (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual Q)).over
          (V.ι ⁻¹ᵁ O)) ≅
        (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual B)).over
          (V.ι ⁻¹ᵁ O)))
      (b : (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual A)).over
          (V.ι ⁻¹ᵁ O)) ≅
        (((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.Modules.dual E)).over
          (V.ι ⁻¹ᵁ O))),
      ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over
          (V.ι ⁻¹ᵁ O) = a.hom ≫
        ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap c)).over
          (V.ι ⁻¹ᵁ O) ≫ b.hom := by
  refine ⟨chartRestrictedDualIso O V t, chartRestrictedDualIso O V s, ?_⟩
  have hd := congrArg (chartRestrictedDualMap O V) h
  rw [chartRestrictedDualMap_global, chartRestrictedDualMap_comp,
    chartRestrictedDualMap_comp, chartRestrictedDualMap_global] at hd
  simpa only [chartRestrictedDualIso, Category.assoc] using hd

/-- Duality and open restriction carry an undualized affine coordinate square to
its dual coordinate square. This is a statement about one chart and an arbitrary
morphism, not the existence or gluing of a global comparison.

Source: Stacks Project, Tag 01CM (the internal Hom sheaf as local linear maps).
(blueprint: new-n1-self-tor-chart-square-dualization).

Proof: For O=i^{-1}U, a map φ:E|_O -> Q|_O acts on dual sections by
precomposition. On an open D of V contained in W=V∩O, its image in Z lies in O.
Restrict φ to that image and precompose the local linear map representing the
section of Q's dual. This is linear in the section and commutes with restriction,
so chartRestrictedDualMap constructs a morphism on the over-W site. Check on each
section and each smaller open that it preserves identities, reverses composition,
and sends τ|_O to the restriction of dualMap τ. Applying it to an isomorphism and
its inverse gives chartRestrictedDualIso, with both inverse laws proved from those
identities. Apply this operation to the coordinate square in hτ. The target
coordinate becomes a and the source coordinate becomes b; reverse composition
and identify the middle map with the functorial image of c.op. Associativity gives
the desired equality. No finiteness, regularity, derived tensor computation, or
descent is used. Empty W and n=0 obey the same section formulas. -/
theorem selfTor_affine_chart_square_dualization
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (U : Y.affineOpens) (n : ℕ)
    (E Q : Z.Modules) (τ : E ⟶ Q)
    (hτ : IsAffineSelfTorChartMap i U n E Q (τ.over (i ⁻¹ᵁ U.1)))
    (V : Z.Opens) :
    let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
    let T := tilde.functor Γ(Y, U.1) ⋙
      Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let F := T.op ⋙ Scheme.Modules.dualFunctor Z ⋙
      Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor _ W
    let c := selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ (a : (((Scheme.Modules.restrictFunctor V.ι).obj
          (Scheme.Modules.dual Q)).over W) ≅ F.obj (op _))
      (b : F.obj (op _) ≅ (((Scheme.Modules.restrictFunctor V.ι).obj
          (Scheme.Modules.dual E)).over W)),
      ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over W =
        a.hom ≫ F.map c.op ≫ b.hom := by
  obtain ⟨s, t, h⟩ := hτ
  exact dualizeLocalCoordinateSquare (i ⁻¹ᵁ U.1) V τ _ s t h

end AlgebraicGeometry
