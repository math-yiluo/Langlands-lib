/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # The strict-local germ restriction is an isomorphism

Source: Stacks Project, Tags 03QO and 03Q9.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical germ restriction identifies a geometric stalk with strict-local sections.
Source: Stacks Project, Tag 03QO and the restriction construction of Tag 03Q9
(blueprint: lem-weil-pbc-strict-local-germ-restriction-iso).

Proof: choose an affine chart containing the image of `s`. The comparison
`lem-weil-pbc-etale-local-ring-triples` identifies the chosen coordinate-ring colimit with
that of étale residue triples over this chart, compatibly with every pointed ring map.
`lem-weil-pbc-strict-henselization-triples` makes the latter strictly henselian local and
identifies its residue field with the relative separable closure inside Ω. Transport the
local-ring structure through the colimit isomorphism and compose its residue map with the
inclusion into Ω. This gives the distinguished geometric closed point of the chosen
strict-local scheme above `s`, with the required equality after the structural map.
The inverse-image stalk comparison identifies the stalk of the pulled-back sheaf
there with the original stalk. On a strictly henselian local scheme, every pointed étale
neighbourhood of the closed point admits a section: shrink it to an affine neighbourhood,
then split its étale algebra into the factor containing that point and its complement.
Consequently evaluation at the identity neighbourhood computes this stalk, and the global
sections-to-stalk map is an isomorphism (03QO). Compose its inverse with the inverse-image
stalk comparison. On a representative neighbourhood its composite with the germ is the
adjunction unit followed by restriction along the strict-local limit leg. These are precisely
`strictHenselizationSectionRestriction`, so uniqueness of the germ restriction identifies
this isomorphism with `r`.
-/
theorem isIso_strictHenselizationStalkRestriction
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictLocalizationToBase s)).obj G))
    (hr : IsStrictHenselizationStalkRestriction s G r) : IsIso r := by
  classical
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
    strictHenselizationResidue s rfl
  let := hlocal
  let y := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization s))))
  let g := Scheme.strictLocalizationToBase s
  let P := (upperStar AddCommGrpCat.{v + 1} g).obj G
  have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselization s) := by
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization s)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  let e := (Sheaf.ΓNatIsoSheafSections
    (Scheme.strictLocalization s).smallEtaleTopology AddCommGrpCat.{v + 1}
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
        (Scheme.strictLocalization s))
      (Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s))) Over.mkIdTerminal))
  let γ := (Scheme.pointSmallEtale y).toPresheafFiber
    (Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s)))
    (Over.homMk y (Category.comp_id y)) P.obj
  have : IsIso γ :=
    (Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 P
  -- Transport the inverse-image comparison to the specified geometric point.
  have comparison : ∀ (t : Spec (.of Ω) ⟶ S) (ht : y ≫ g = t),
      ∃ c : (Scheme.pointSmallEtale y).sheafFiber.obj P ≅
          (Scheme.pointSmallEtale t).sheafFiber.obj G,
        ∀ (U : S.Etale) (ū : (Scheme.pointSmallEtale t).fiber.obj U)
          (a : Scheme.Etale.mk (𝟙 (Scheme.strictLocalization s)) ⟶ g.Etale.obj U),
          y ≫ a.left ≫ pullback.fst U.hom g = ū.left →
          ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} g).unit.app G).hom.app
            (op U) ≫ P.obj.map a.op ≫ γ ≫ c.hom =
            (Scheme.pointSmallEtale t).toPresheafFiber U ū G.obj := by
    intro t ht
    subst t
    obtain ⟨c, hc⟩ := inverseImage_stalk_germ g y
    refine ⟨c.app G, ?_⟩
    intro U ū a ha
    have hp : (Scheme.pointSmallEtale y).fiber.map a
        (Over.homMk y (Category.comp_id y)) =
        (Scheme.pointSmallEtaleFiberEtaleIso g y).inv.app U ū := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
        change (y ≫ a.left) ≫ pullback.fst U.hom g = ū.left
        exact ha
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
        change (y ≫ a.left) ≫ pullback.snd U.hom g = y
        rw [Category.assoc]
        have hw := a.w
        change a.left ≫ pullback.snd U.hom g = 𝟙 _ at hw
        rw [hw]
        rfl
    dsimp only [γ]
    rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hp]
    exact hc G U ū
  obtain ⟨c, hc⟩ := comparison s hbase
  let r₀ := c.inv ≫ inv γ ≫ e.inv.app P
  have hr₀ : IsStrictHenselizationStalkRestriction s G r₀ := by
    intro j
    let n := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j
    have ha : y ≫ (strictHenselizationNeighbourhoodSection s j).left ≫
        pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom g = n.2.left := by
      dsimp only [g, n]
      simp only [strictHenselizationNeighbourhoodSection,
        MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
      simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint j
    have h := hc ((Scheme.AffineEtale.Spec S).obj n.1) n.2
      (strictHenselizationNeighbourhoodSection s j) ha
    dsimp only [r₀, strictHenselizationSectionRestriction]
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
    rfl
  have hEq : r = r₀ := (existsUnique_strictHenselizationStalkRestriction s G).unique hr hr₀
  rw [hEq]
  dsimp only [r₀]
  infer_instance

end AlgebraicGeometry.Etale
