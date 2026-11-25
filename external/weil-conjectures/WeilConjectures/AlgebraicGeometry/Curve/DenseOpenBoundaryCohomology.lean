/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomologyExtension

/-!
# Cohomology of the closed boundary of a dense open curve

Source: Stacks Project, Tag 0GJA, proof of lemma-restrict-to-open.
(blueprint: lem-pbc-g2-dense-open-boundary-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The closed-boundary sheaf has finite degree-zero cohomology and zero positive-degree cohomology.
Source: Stacks Project, Tag 0GJA, proof of lemma-restrict-to-open, finite stalk product.
(blueprint: lem-pbc-g2-dense-open-boundary-cohomology).

Proof: Since X is finite type over k, it is Noetherian. A dense open meets each irreducible
component at its generic point. Thus its closed complement in a space of dimension at most
one has dimension zero. It is a finite set of closed points, each with residue field k.
The vanishing ideal gives the reduced induced closed subscheme Z on that complement.
The pullback of F to Z has finite stalks: constructibility gives finitely generated
Lambda-modules, and Lambda is finite. The etale cohomology of this zero-dimensional scheme
is the finite product of those stalks in degree zero and zero in positive degrees.
The closed immersion i is finite, so its direct image is exact and Leray identifies
H^q(X, i_*i^*F) with H^q(Z, i^*F). Forgetting the module structure preserves these
identifications. This proves the two conclusions. For U = X, Z is empty, the product is the
zero group, and the same argument applies; for empty X both conclusions are immediate. -/
theorem dense_open_boundary_cohomology (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (U : X.Opens) (hU : Dense (U : Set X)) :
    let I := Scheme.IdealSheafData.vanishingIdeal U.compl
    let B := (I.subschemeι)_*[ModuleCat.{u + 1} Λ].obj
      ((I.subschemeι)^*[ModuleCat.{u + 1} Λ].obj F)
    let B' := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj B
    Finite (Sheaf.H B' 0) ∧ (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H B' q)) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal U.compl
  let Z := I.subscheme
  let i : Z ⟶ X := I.subschemeι
  let G := (i)^*[ModuleCat.{u + 1} Λ].obj F
  let E : ModuleCat.{u + 1} Λ ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : Limits.PreservesColimitsOfSize.{u, u} E :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let A := (sheafCompose Z.smallEtaleTopology E).obj G
  -- Embed the boundary in the zero-dimensional complement of a smaller dense open.
  have hdim : topologicalKrullDim Z ≤ 0 := by
    obtain ⟨n, V, hVU, _, _, _, hVdim, _⟩ := exists_dense_irreducible_opens f U hU
    let b : Z → ↥(⋃ a, (V a : Set X))ᶜ := fun z ↦ ⟨i.base z, by
      have hz : i.base z ∈ (U : Set X)ᶜ := U.range_closedComplement ▸ ⟨z, rfl⟩
      intro hv
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
      exact hz (hVU a ha)⟩
    have hb : Topology.IsInducing b :=
      (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp
        i.isClosedEmbedding.isInducing
    exact hb.topologicalKrullDim_le.trans hVdim
  -- Constructibility supplies finite stalks after restriction to the boundary.
  have hG : Scheme.IsConstructibleSheaf G := Scheme.IsConstructibleSheaf.upperStar i F
  have : Scheme.IsFiniteSheaf G := hG.isFiniteSheaf
  let s := Z.algClosurePoint
  have hcoh := zero_dimensional_etale_cohomology k Z (i ≫ f) hdim A
    (fun z ↦ AlgebraicClosure (Z.residueField z)) s
    (fun z ↦ Z.algClosurePoint_base z default)
  have : Finite Z := hcoh.1
  let T : Z → AddCommGrpCat.{u + 1} := fun z ↦
    (Scheme.pointSmallEtale (s z)).presheafFiber.obj A.obj
  have hT (z : Z) : Finite (T z) := by
    let M : ModuleCat.{u + 1} Λ := (Scheme.pointSmallEtale (s z)).sheafFiber.obj G
    have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).mp
      (Scheme.IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := G) _ (s z))
    have : Finite M := Module.finite_of_finite Λ
    let e : T z ≅ E.obj M :=
      ((Scheme.pointSmallEtale (s z)).sheafFiberCompIso E).app G
    exact Finite.of_injective e.addCommGroupIsoToAddEquiv
      e.addCommGroupIsoToAddEquiv.injective
  have : ∀ z, Finite (T z) := hT
  have : Finite ↑(∏ᶜ T) := Finite.of_injective
    (fun (a : ↑(∏ᶜ T)) (z : Z) ↦ Limits.Pi.π T z a) (by
      intro a b h
      apply Limits.Concrete.isLimit_ext (Discrete.functor T) (Limits.productIsProduct T) a b
      intro z
      exact congrFun h z.as)
  -- The dimension-zero theorem identifies degree-zero cohomology with this finite product.
  let c :=
    (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}) A 0).hom ≫
    (Functor.rightDerivedZeroIsoSelf
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app A ≫
    A.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 Z))) ≫
    Limits.Pi.lift (fun z : Z ↦ (Scheme.pointSmallEtale (s z)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 Z))
      (Over.homMk (s z) (Category.comp_id (s z))) A.obj)
  have : IsIso c := hcoh.2.2
  have hA0 : Finite (Sheaf.H A 0) := by
    let e := (Scheme.nonempty_sheafH_extDerivedIso Z 0).some.app A
    exact Finite.of_injective (fun a ↦ c (e.hom a))
      ((asIso c).addCommGroupIsoToAddEquiv.injective.comp
        e.addCommGroupIsoToAddEquiv.injective)
  -- Finite pushforward identifies cohomology on the boundary with cohomology on X.
  have : Finite (Sheaf.H
      ((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).obj A) 0) := hA0
  change Finite (Sheaf.H ((i)_*[AddCommGrpCat.{u + 1}].obj A) 0) ∧ _
  refine ⟨Finite.of_injective _ (bijective_edgeMap_of_isFinite i A 0).injective, ?_⟩
  intro q hq
  let e := (Scheme.nonempty_sheafH_extDerivedIso Z q).some.app A
  have hAq : Subsingleton (Sheaf.H A q) := by
    constructor
    intro a b
    exact e.addCommGroupIsoToAddEquiv.injective ((hcoh.2.1 q hq).elim _ _)
  have : Subsingleton (Sheaf.H
      ((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).obj A) q) := hAq
  change Subsingleton (Sheaf.H ((i)_*[AddCommGrpCat.{u + 1}].obj A) q)
  exact (bijective_edgeMap_of_isFinite i A q).injective.subsingleton

end AlgebraicGeometry.IsCurve
