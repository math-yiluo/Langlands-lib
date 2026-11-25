module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.ENatToNat
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.CompleteNoetherian
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFP
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.RingTheory.Ideal.SmulTop

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Exactness of adic completion and of limits of towers of modules

For `R` Noetherian, this file proves that `R → R^∧` is faithfully flat when `I` is contained in
the Jacobson radical, and that completion carries short exact sequences with finite middle term to
short exact sequences. It then gives the auxiliary results for
`flat_limit_and_tensor_limit_of_flat_quotients`: levelwise tensor products of towers, pro-zero
towers of `Tor₁`, Mittag-Leffler towers, and criteria for the induced map on limits of a map of
towers of modules to be injective, surjective or right exact.

## Main results

* `AdicCompletion.faithfullyFlat_of_le_ringJacobson`
* `adicCompletion_shortExact`
-/

@[expose] public section

universe u v

/-- Let `I` be an ideal of a Noetherian ring `R` and let `R^∧` be the `I`-adic completion of `R`.
If `I` is contained in the Jacobson radical of `R`, then the ring map `R → R^∧` is faithfully flat.
In particular, if `(R, 𝔪)` is a Noetherian local ring, then the completion `lim_n R/𝔪ⁿ` is
faithfully flat over `R`. -/
@[stacks 00MC "Stated as the class `Module.FaithfullyFlat R (AdicCompletion I R)`, the shape of the
flatness half `AdicCompletion.flat_of_isNoetherian`; the `in particular` is the case `I = 𝔪`. See
the module docstring."]
public theorem AdicCompletion.faithfullyFlat_of_le_ringJacobson {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    Module.FaithfullyFlat R (AdicCompletion I R) := by
  rw [Module.faithfullyFlat_iff]
  refine ⟨AdicCompletion.flat_of_isNoetherian I, fun {m} hm => ?_⟩
  refine smul_top_ne_top_of_surjective m
    (f := (AdicCompletion.evalOneₐ I).toLinearMap) (AdicCompletion.evalOneₐ_surjective I) ?_
  rw [ne_eq, smul_top_quotient_eq_top_iff,
    sup_eq_left.mpr (hI.trans (Ring.jacobson_le_of_isMaximal m))]
  exact hm.ne_top

/-! For an ideal `I` of a Noetherian ring `R`, completion preserves injectivity of a map into a
finite module (`AdicCompletion.map_injective`), carries a short exact sequence of finite modules
to a short exact sequence (together with `AdicCompletion.map_surjective` and
`AdicCompletion.map_exact`), and satisfies `M^∧ = M ⊗_R R^∧` for finite `M`
(`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`). -/

/-! Part (1) of Stacks 00MB, that for a Noetherian ring `R` and any ideal `I` the canonical ring
map `R → R^∧` is flat, is Mathlib's instance `AdicCompletion.flat_of_isNoetherian`. -/

section FlatLimit

set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits

end FlatLimit

end
