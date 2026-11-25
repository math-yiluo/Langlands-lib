/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Base change and the neighbourhood limit

Source: Weil conjectures blueprint, `sec-curve-estimates/lem-sc-second-kummer-divisors`,
(blueprint: lemma-weil-pbc-fibre-product-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical base-change cone over all pointed étale neighbourhoods is limiting.
The existential structure map and cone legs are specified by their restrictions to the
chosen affine representatives: these are the spectra of the coordinate-ring colimit maps.
This states the canonical isomorphism with the inverse limit without assuming that limit
exists beforehand. The order of the two factors is immaterial: `Over.pullback f` uses
`V ×_S X` with its projection to `X`.

Source: blueprint `sec-curve-estimates/lem-sc-second-kummer-divisors`,
(blueprint: lemma-weil-pbc-fibre-product-limit).

Proof:
1. The strict-henselization cone is limiting on the small affine representatives by
   `lem-weil-pbc-spec-small-colimit-limit`. Transport through the affine spectrum
   equivalence, and then along the initial affine inclusion
   (`lemma-weil-pbc-affine-neighbourhood-cofinal` and
   `lem-weil-pbc-colimit-initial-full-subcategory`), to get the full neighbourhood cone.
   Its leg at `(S,s)` is the structure map `p`; all its legs are over `S`.
2. A compatible cone to the fibre products gives a compatible cone to the neighbourhoods
   and hence a unique map to the strict henselization. Its components to `X` agree:
   cofilteredness (`definition-torsion-sheaves--3`) supplies common
   refinements. The component at `(S,s)` ensures that the two maps agree over `S`.
3. The fibre-product universal property (`def-pc-fibre-product`) gives the unique map to
   the vertex of the displayed cone. Equality of its two components proves uniqueness,
   so this cone is limiting and gives the canonical comparison isomorphism. -/
theorem fibre_product_neighbourhood_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    ∃ (p : Scheme.strictLocalization s ⟶ S)
      (q : (Functor.const (Scheme.pointSmallEtale s).fiber.Elements).obj (Over.mk p) ⟶
        Functor.Elements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget S),
      (∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
        (q.app ((Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).obj
            ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              j))).left =
          (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) ≫
            (Spec (unop
              ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
                j).1.left)).isoSpec.inv) ∧
      Nonempty (IsLimit ((Over.pullback f ⋙ Over.forget X).mapCone
        { pt := Over.mk p, π := q })) := by
  classical
  let J := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)
  let R := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let F := R ⋙ Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
    (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let D := Functor.Elements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget S
  obtain ⟨hF, hJ, ⟨hlim⟩⟩ := Scheme.strictHenselizationAffineProperties s
  let : F.Initial := hF
  let : IsCofiltered J := hJ
  let : IsConnected J := IsCofiltered.isConnected J
  -- Identify the affine spectra with their neighbourhoods, preserving the chosen legs.
  let c := (Scheme.strictHenselizationAffineCone s).whisker (opOp J)
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv (opOp J) _).symm hlim
  let e : (opOp J ⋙ (Scheme.strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec) ≅
      F ⋙ D ⋙ Over.forget S := NatIso.ofComponents
    (fun j ↦ (Spec (unop (R.obj j).1.left)).isoSpec.symm)
    (by
      intro i j g
      exact Scheme.isoSpec_inv_naturality (Spec.map (R.map g).1.left.unop))
  let c' : Cone (F ⋙ D ⋙ Over.forget S) := (Cone.postcompose e.hom).obj c
  have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv e c).symm hc
  -- Connected limits lift to the over category with the same underlying vertex.
  let b : Cone (F ⋙ D) := CostructuredArrow.CreatesConnected.raiseCone c'
  have hb : IsLimit b := CostructuredArrow.CreatesConnected.isLimitRaiseCone hc'
  -- Initiality extends this cone to all pointed neighbourhoods.
  let a : Cone D := Functor.Initial.extendCone.obj b
  refine ⟨a.pt.hom, a.π, ?_, ?_⟩
  · intro j
    change (a.π.app (F.obj j)).left = (b.π.app j).left
    have hj := Functor.Initial.extendCone_obj_π_app' (F := F) (G := D)
      b (𝟙 (F.obj j))
    rw [D.map_id] at hj
    exact congrArg (fun k ↦ k.left) (hj.trans (Category.comp_id (b.π.app j)))
  -- Check the base-changed cone after restriction to the small connected category.
  · apply Nonempty.intro
    apply (Functor.Initial.isLimitWhiskerEquiv F _).toFun
    exact (isLimitOfPreserves (Over.pullback f ⋙ Over.forget X) hb).ofIsoLimit
      ((Cone.functoriality _ (Over.pullback f ⋙ Over.forget X)).mapIso
        ((Functor.Initial.conesEquiv F D).unitIso.app b))

end AlgebraicGeometry
