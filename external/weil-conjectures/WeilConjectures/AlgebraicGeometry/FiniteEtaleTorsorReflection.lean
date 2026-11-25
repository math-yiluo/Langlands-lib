/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

import WeilConjectures.AlgebraicGeometry.FiniteTorsorPullbackHomBijective
import WeilConjectures.AlgebraicGeometry.TorsorUnitEquivarianceReflection

/-!
# Finite étale equivalences and transport of torsors

Source: Stacks Project Tag 0A5G, final paragraph, and Tag 03RV.
(blueprint: lem-weil-pbc-finite-etale-torsor-reflection)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Transport by inverse image reflects isomorphisms of finite constant torsors.
Source: Stacks Project Tag 0A5G, final paragraph, using Tag 03RV.
(blueprint: lem-weil-pbc-finite-etale-torsor-reflection)

Proof: A torsor under the finite constant group M is étale locally the finite set M,
so Tag 03RV represents its underlying sheaf by a finite étale scheme. Yoneda represents
each constant action map. Inverse image of a representable is the representable of its
base change. For each m in M, translation is a sheaf endomorphism, represented by Yoneda.
The displayed equation for g the constant section m says its inverse image agrees
with translation by m on τ T: after adjunction the two maps agree on every T(W),
so the adjunction bijection makes them equal. Any section of the constant sheaf
is locally constant; naturality and the sheaf condition extend this equality to
all coefficient sections. Thus the equation specifies the full pulled-back action.
An isomorphism between τ T₁ and τ T₂ is therefore an equivariant isomorphism between
the base changes of the representatives. Fullness lifts it and its inverse; faithfulness
lifts their inverse equations and each equivariance equation. Yoneda then gives an
isomorphism of the original sheaf torsors. Empty schemes and the trivial group are
included: the argument uses neither a point nor a nonempty base. -/
theorem finiteEtale_reflects_torsor_transport
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (τ : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) →
      Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (hτ : ∀ T : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)), ∃ eT : (Scheme.etaleSetPullback i).obj T.sheaf ≅ (τ T).sheaf,
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
      eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
            (T.vadd (op W) g t)) =
      (τ T).vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))))
    (T₁ T₂ : Sheaf.Torsor
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)))
    (h : τ T₁ ≈ τ T₂) : T₁ ≈ T₂ := by
  obtain ⟨e₁, he₁⟩ := hτ T₁
  obtain ⟨e₂, he₂⟩ := hτ T₂
  obtain ⟨φ⟩ := h
  let L := Scheme.etaleSetPullback i
  let α := e₁.hom ≫ φ.iso.hom ≫ e₂.inv
  let β := e₂.hom ≫ φ.iso.inv ≫ e₁.inv
  obtain ⟨f, hf⟩ := (finite_torsor_pullback_hom_bijective i hFE M T₁ T₂).2 α
  obtain ⟨g, hg⟩ := (finite_torsor_pullback_hom_bijective i hFE M T₂ T₁).2 β
  change L.map f = α at hf
  change L.map g = β at hg
  have hfg : f ≫ g = 𝟙 T₁.sheaf := by
    apply (finite_torsor_pullback_hom_bijective i hFE M T₁ T₁).1
    change L.map (f ≫ g) = L.map (𝟙 T₁.sheaf)
    rw [L.map_comp, L.map_id, hf, hg]
    simp [α, β, Category.assoc]
  have hgf : g ≫ f = 𝟙 T₂.sheaf := by
    apply (finite_torsor_pullback_hom_bijective i hFE M T₂ T₂).1
    change L.map (g ≫ f) = L.map (𝟙 T₂.sheaf)
    rw [L.map_comp, L.map_id, hg, hf]
    simp [α, β, Category.assoc]
  refine ⟨⟨⟨f, g, hfg, hgf⟩, ?_⟩⟩
  apply torsor_map_equivariant_of_unit i M T₁ T₂ (τ T₁) (τ T₂)
    e₁ e₂ he₁ he₂ f (finite_torsor_pullback_hom_bijective i hFE M T₁ T₂).1
    φ.iso.hom φ.map_vadd
  change L.map f ≫ e₂.hom = e₁.hom ≫ φ.iso.hom
  rw [hf]
  simp [α, Category.assoc]

end AlgebraicGeometry.Etale
