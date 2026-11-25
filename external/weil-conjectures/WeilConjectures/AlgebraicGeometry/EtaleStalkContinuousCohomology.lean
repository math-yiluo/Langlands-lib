/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.RepresentationTheory.DiscreteModule.ContinuousCohomology
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Continuous cohomology of the geometric stalk over a field

Let `Ks` be a separable closure of a field `K`. The étale cohomology of an abelian sheaf `F` on
`Spec K` is the continuous cohomology, computed by continuous homogeneous cochains, of any
discrete topological `Gal(Ks/K)`-module identified equivariantly with the stalk of `F` at the
Galois point `AlgebraicGeometry.Scheme.galoisPoint K Ks`.

Source: Stacks Project, Tags 04JQ, 03QU and Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosed Ks]
  [Algebra.IsSeparable K Ks]

/-- Étale cohomology of an abelian sheaf `F` on `Spec K` is the homogeneous continuous
cohomology of its stalk at the Galois point: given an additive equivalence `c` from the stalk
of `F` at `galoisPoint K Ks` to a discrete topological `Gal(Ks/K)`-module `M`, intertwining the
Galois action on the stalk (`galoisPointAct`) with the action on `M`, this is the induced
additive equivalence `Hⁿ(Spec K_ét, F) ≃+ Hⁿ_cont(Gal(Ks/K), M)`.

It is the composite of the comparison `Hⁿ(Spec K_ét, F) ≃+ Extⁿ(ℤ, F_{Ks})` in discrete
modules (`AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`) with the computation of `Ext` from
`ℤ` by continuous cochains (`DiscreteModule.hAddEquivContinuousCohomology`), transported
along `c`.

Source: Stacks Project, Tags 04JQ and 03QU; Section 0DVG.
(blueprint: lem-sc-etale-stalk-continuous-cohomology). -/
noncomputable def sheafHAddEquivContinuousCohomology
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (M : TopRep.{u} ℤ Gal(Ks/K)) [DiscreteTopology M.V]
    (c : ((galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F ≃+ M.V)
    (hc : ∀ (σ : Gal(Ks/K))
      (v : ((galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
      c ((galoisPoint K Ks).presheafFiberAct (galoisPointAct K Ks) F.obj σ v) = M.ρ σ (c v))
    (n : ℕ) :
    Sheaf.H F n ≃+ continuousCohomology n M :=
  haveI : IsSepClosure K Ks := ⟨inferInstance, inferInstance⟩
  (sheafHAddEquivGaloisH K Ks F n).trans
    (DiscreteModule.hAddEquivContinuousCohomology.{u + 1, u, u} Gal(Ks/K)
      ((etaleSheafEquivDiscreteModule K Ks).functor.obj F) M c hc n)

end AlgebraicGeometry.Scheme
