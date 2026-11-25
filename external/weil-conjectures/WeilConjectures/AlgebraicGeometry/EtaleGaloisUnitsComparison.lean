/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStalkContinuousCohomology
public import WeilConjectures.AlgebraicGeometry.EtaleUnitsGaloisPointStalk

/-!
# Degree-two comparison for the multiplicative sheaf over a field

The cohomological Brauer group `H²(Spec K_ét, 𝔾ₘ)` of a field `K` is the second continuous
Galois cohomology of the units of a separable closure.

Source: Stacks Project, Lemmas 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-galois-units-comparison).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The second étale cohomology of the multiplicative group over a field `K` is the second
continuous Galois cohomology of the units of the separable closure `Ks` of `K`.

This is `AlgebraicGeometry.Scheme.sheafHAddEquivContinuousCohomology` for `𝔾ₘ`, whose stalk
at the Galois point is identified with `Ksˣ` by evaluation of germs at the geometric point
(`AlgebraicGeometry.Scheme.gmSheafFiberGaloisPointAddEquiv`). It is the composite of the
comparison of étale cohomology over a field with `Ext` in discrete Galois modules
(`AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`) and the computation of this `Ext` by
continuous homogeneous cochains (`DiscreteModule.hAddEquivContinuousCohomology`). The stalk of
`𝔾ₘ` is the group of units of `Ks` even when `K` is imperfect. This additive equivalence and
its inverse supersede the former one-sided embeddings
(blueprint: lem-sc-etale-units-h2-forward-embedding)
(blueprint: lem-sc-etale-units-h2-reverse-embedding).

Source: Stacks Project, Lemmas 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-galois-units-comparison). -/
noncomputable def cohomologicalBrauerGroupAddEquivGaloisUnitsH2 (K : Type u) [Field K] :
    (Spec (.of K)).CohomologicalBrauerGroup ≃+ Field.GaloisUnitsH2 K :=
  haveI : DiscreteTopology (Field.galoisUnitsTopRep K).V := ⟨rfl⟩
  sheafHAddEquivContinuousCohomology K (SeparableClosure K) (Spec (.of K)).gmSheaf
    (Field.galoisUnitsTopRep K) (gmSheafFiberGaloisPointAddEquiv K)
    (gmSheafFiberGaloisPointAddEquiv_presheafFiberAct K) 2

end AlgebraicGeometry.Scheme
