/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime

/-!
# Étale sections after extension of a separably closed base field

Source: Stacks Project, Etale Cohomology, Lemma 0A3I
(etale-cohomology-lemma-sections-base-field-extension)
(blueprint: lem-weil-pbc-sections-base-field-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Etale Cohomology, Lemma 0A3I
(blueprint: lem-weil-pbc-sections-base-field-extension).
Let `k` be separably closed, `K/k` a field extension, and `S` a `k`-scheme.
Pullback induces a bijection on sections of every sheaf of sets on `S`'s small étale site.
The map is the inverse-image/direct-image adjunction unit evaluated at the identity
étale object of `S`. Its target is the inverse image evaluated at the base change of
that object, canonically isomorphic to the identity object of `S_K`; composing with
this isomorphism gives exactly the canonical map to global sections on `S_K`.
The inverse image is the same Kan-extension/sheafification construction as the recorded
`Scheme.etaleSetPullback`, rather than an independently chosen equivalence of section sets.

Proof:
1. The map `Spec K ⟶ Spec k` is flat (a field extension is a free module) and
   quasi-compact (its source has one point). Thus its base change `p : S_K ⟶ S`
   is flat and quasi-compact, by lem-weil-pbc-flat-morphism-base-change and
   lem-pc-quasi-compact-base-change.
2. Over a geometric point `Spec L ⟶ S`, the fibre is `Spec (K ⊗[k] L)`.
   By lem-weil-pbc-field-tensor-irreducible, this ring has a unique minimal prime;
   its spectrum is irreducible, hence connected.
3. Apply lem-weil-pbc-etale-sections-flat-qc-connected-fibres (Stacks 0A3H) to `p`
   and `F`. This gives bijectivity of the canonical pullback map on sections. -/
theorem etale_sections_base_field_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosed k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤
          (pullback.fst (S ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
        (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        ((pullback (S ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).smallGrothendieckTopology
            @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S)))) := by
  refine etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres
    (pullback.fst (S ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ?_ F
  intro s
  let L := AlgebraicClosure (S.residueField s)
  let g : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫
      S.fromSpecResidueField s
  let a := S ↘ Spec (.of k)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let φ := (Spec.preimage (g ≫ a)).hom
  let : Algebra k L := φ.toAlgebra
  have hg : g ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    exact (Spec.map_preimage (g ≫ a)).symm
  let e := pullbackSymmetry (pullback.fst a b) g ≪≫
    pullbackRightPullbackFstIso a b g ≪≫
    pullback.congrHom hg rfl ≪≫ pullbackSpecIso k L K
  exact e.schemeIsoToHomeo.connectedSpace_iff.mpr
    (IsSepClosed.field_tensor_unique_minimalPrime k L K).2.2

end AlgebraicGeometry
