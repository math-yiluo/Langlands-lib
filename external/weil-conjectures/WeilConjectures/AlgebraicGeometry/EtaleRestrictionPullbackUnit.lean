/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnitEq

/-!
# Étale restriction and pullback units

Source: Stacks Project, Sites, Tags 03CF and 03EF (unit-side counterpart).
(blueprint: lem-weil-pbc-etale-restriction-pullback-unit)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Unit compatibility for an étale object in a cartesian square.
Source: Stacks Project, Sites, Tags 03CF and 03EF (unit-side counterpart).
(blueprint: lem-weil-pbc-etale-restriction-pullback-unit)

Proof (the node's five steps):
1. Put h = g' ≫ p = p' ≫ g. Form P₀ = W ×ₓ W, P₁ = W ×ₓ Y, Q = W ×ₓ W'.
   The diagonal δ and the maps θ = (g',id), τ = (δg',id), σ = (ι,id) give
   φτ = φ'σ = γ = (g',id), for the two pullback-pasting isomorphisms φ, φ'.
   Use def-pc-fibre-product and lem-weil-pbc-inverse-image-composition (1).
2. The unit description and naturality of the restriction comparison in
   lem-weil-pbc-etale-inverse-image-restriction (2), restricted along δ, give
   (p⁻¹F)(δ)ηₚ(W) = ρF(W)⁻¹. Restricting the analogous formula along σ gives
   (p'⁻¹g⁻¹F)(σ)ηₚ'(P₁) = ρg⁻¹F(W')⁻¹(g⁻¹F)(ι).
3. Evaluate the unit equation of lem-weil-pbc-inverse-image-composition (2)
   for (p,g') at W and restrict along τ. Naturality of c and ηg', and step 2,
   identify the result with cₚ,g'(W')ηg'(W)ρF(W)⁻¹ = (h⁻¹F)(γ)ηh(W).
   The value of ηg'(W) here includes restriction along θ.
4. Apply the same composition unit equation for (g,p') and restrict along σ.
   The result is c_g,p'(W')ρg⁻¹F(W')⁻¹(g⁻¹F)(ι)ηg(W) = (h⁻¹F)(γ)ηh(W).
5. Equate steps 3 and 4, cancel c_g,p', and compose with the two restriction
   comparisons. Evaluating at any section gives the assertion. Étaleness of p'
   follows from base-change stability and the isomorphism ι, as in
   situation-conventions (1).

The existential proof hp' records the conclusion that p' is étale before using
it to type the restriction comparison. The equality of abelian-group homomorphisms
is the displayed equality for every section a. The maps eW and eW' only remove
identity composites in the structure maps of the terminal étale objects.
-/
theorem etale_restriction_pullback_unit
    {X Y W W' : Scheme.{u}}
    (g : Y ⟶ X) (p : W ⟶ X) (g' : W' ⟶ W) (p' : W' ⟶ Y)
    (hcomm : g' ≫ p = p' ≫ g)
    (ι : W' ⟶ pullback p g)
    (hι₁ : ι ≫ pullback.fst p g = g')
    (hι₂ : ι ≫ pullback.snd p g = p')
    [IsIso ι] [hp : Etale p] :
    ∃ hp' : Etale p',
      let A := AddCommGrpCat.{u + 1}
      let w : W.Etale := Scheme.Etale.mk (𝟙 W)
      let w' : W'.Etale := Scheme.Etale.mk (𝟙 W')
      let wx : X.Etale := Scheme.Etale.mk p
      let wy' : Y.Etale := @Scheme.Etale.mk _ _ p' hp'
      let eW : (MorphismProperty.Over.map ⊤ hp).obj w ≅ wx :=
        MorphismProperty.Over.isoMk (Iso.refl W) (by simp [wx, w])
      let eW' : (MorphismProperty.Over.map ⊤ hp').obj w' ≅ wy' :=
        MorphismProperty.Over.isoMk (Iso.refl W') (by simp [wy', w'])
      let theta : w' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g').obj w :=
        MorphismProperty.Over.homMk (pullback.lift g' (𝟙 W')
          (by exact (Category.comp_id g').trans (Category.id_comp g').symm))
          (by simp [w'])
      let iotaSite : wy' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj wx :=
        MorphismProperty.Over.homMk ι hι₂
      ∀ F : Sheaf X.smallEtaleTopology A,
        let pF := (Etale.upperStar A p).obj F
        let gF := (Etale.upperStar A g).obj F
        let K := (Etale.upperStar A g').obj pF
        let rhoF := (Etale.upperStarIsoLocalizationRestriction A p hp).hom.app F
        let rhoG := (Etale.upperStarIsoLocalizationRestriction A p' hp').hom.app gF
        let kappa := (Etale.upperStarComp A g' p).inv.app F ≫
          (Etale.upperStarComp A p' g (g' ≫ p) hcomm).hom.app F
        ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.app (op w) ≫
            K.obj.map theta.op ≫ kappa.hom.app (op w') ≫
            rhoG.hom.app (op w') ≫ gF.obj.map eW'.inv.op =
          rhoF.hom.app (op w) ≫ F.obj.map eW.inv.op ≫
            ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op wx) ≫
            gF.obj.map iotaSite.op := by
  let hp' : Etale p' := by
    have hs : Etale (pullback.snd p g) := inferInstance
    have hh := (MorphismProperty.arrow_mk_iso_iff (P := @Etale) (Arrow.isoMk (asIso ι)
      (Iso.refl Y) (by simpa using hι₂))).mpr hs
    simpa using hh
  exact ⟨hp', etale_restriction_pullback_unit_eq g p g' p' hcomm ι hι₁ hι₂ hp'⟩

end AlgebraicGeometry
