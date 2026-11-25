module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import StacksFrontier.RingTheory.Nagata.Japanese.EssFiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese.Localization
public import StacksFrontier.RingTheory.Nagata.Japanese.N1Criterion
public import StacksFrontier.RingTheory.Nagata.Japanese.NagataScheme
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# N-1 descends from the Laurent polynomial ring

All rings are commutative with `1`, and a *domain* is a nonzero integral domain.
For a domain `R` we write `K = Frac R` for its field of fractions, viewed as a ring
containing `R`. The *integral closure of `R` in `K`* is the set
`R' = {x ∈ K | x integral over R}` of those `x ∈ K` satisfying a monic equation
`xⁿ + c_{n-1} x^{n-1} + ⋯ + c₀ = 0` with coefficients in `R`; it is a subring of `K`
containing `R`, and naturally an `R`-module.

A domain `R` with fraction field `K` is *N-1* when the integral closure `R'` of `R`
in `K` is a finite, that is finitely generated, `R`-module.

For a domain `R`, the Laurent polynomial ring `R[z, z⁻¹]` is the ring of Laurent
polynomials in `z` over `R`, equivalently the localization `R[z]_z` of the polynomial
ring at the powers of `z`; its elements are the finite sums `∑_j a_j zʲ` with
`a_j ∈ R` and `j` ranging over a finite set of possibly negative integers. Since `R`
is a domain so is `R[z, z⁻¹]`, so the notion of N-1 applies to it. It is realized by
Mathlib's `LaurentPolynomial R`, written `R[T;T⁻¹]`.

The main result is that for a Noetherian domain `R`, if `R[z, z⁻¹]` is N-1 then so is
`R`: if the integral closure of `R[z, z⁻¹]` in its fraction field
`Frac (R[z, z⁻¹]) = K(z)` is a finite `R[z, z⁻¹]`-module, then the integral closure
`R'` of `R` in `K` is a finite `R`-module.

## Conventions and the shape of the argument

Since `R` is a domain, `K = Frac R` is a field, and the fraction field of `R[z, z⁻¹]`
is `K(z)`, the field of rational functions in `z` over `K`, giving the chain
`R ⊂ R[z, z⁻¹] ⊂ K[z, z⁻¹] ⊂ K(z)`.

Write `S'` for the integral closure of `R[z, z⁻¹]` in `K(z)`. The field `K(z)` is also
the fraction field of the normal domain `K[z, z⁻¹]`, a localization of the principal
ideal domain `K[z]`, hence a unique factorization domain and so integrally closed in
its fraction field. Any element of `K(z)` integral over `R[z, z⁻¹]` is in particular
integral over `K[z, z⁻¹]` and therefore lies in `K[z, z⁻¹]`. Thus `S' ⊂ K[z, z⁻¹]`,
and clearly `R' ⊂ S'`.

Suppose `f₁, …, f_n ∈ S'` generate `S'` as an `R[z, z⁻¹]`-module and write each
`f_i = ∑_j a_{ij} zʲ` as a finite sum with `a_{ij} ∈ K`. For `x ∈ R'` we have `x ∈ S'`,
so `x = ∑_i h_i f_i` with `h_i ∈ R[z, z⁻¹]`; comparing coefficients of powers of `z`
shows that `x` lies in the finitely generated `R`-submodule `∑_{i,j} R a_{ij} ⊂ K`.
Hence `R'` is contained in a finite `R`-submodule of `K`, and since `R` is Noetherian
every submodule of a finite `R`-module is finite, so `R'` is a finite `R`-module.

The Noetherian hypothesis on `R` is used precisely to conclude that the `R`-submodule
`R'` of the finite `R`-module `∑_{i,j} R a_{ij}` is itself finitely generated, and the
N-1 hypothesis on `R[z, z⁻¹]` supplies the finite generating set of `S'`.
-/

@[expose] public section

open scoped Polynomial LaurentPolynomial

/-- Reduction lemma: over a Noetherian ring, if the integral closure of `R` in
`K` is contained (as an `R`-submodule) in a finitely generated `R`-submodule of
`K`, then the integral closure is itself a finite `R`-module. -/
theorem isN1_of_le_fg {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [IsNoetherianRing R] (M : Submodule R K) (hM : M.FG)
    (hsub : (integralClosure R K).toSubmodule ≤ M) :
    Module.Finite R (integralClosure R K) := by
  have hMnoeth : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M hM
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hsub)

/-! ## Decomposition of the main containment

Notation throughout: `K = Frac R`, `S = R[z,z⁻¹]`, `L = Frac S`,
`T = K[z,z⁻¹] = LaurentPolynomial K`, `S' = integralClosure S L` and
`R' = integralClosure R K`. The argument factors into four mathematically
independent pieces, which are the sub-lemmas below.
-/

/-! ### The containment `S' ⊆ K[z,z⁻¹]`

Every element of `L = Frac (R[z,z⁻¹])` integral over `S = R[z,z⁻¹]` lies in
`T = K[z,z⁻¹]`. Indeed `L = Frac S` is also the fraction field of `T`, both being
`K(z)`, because `T` is the localization of `S` obtained by inverting the nonzero
elements of `R`. Any element of `L` integral over `S` is a fortiori integral over
the larger ring `T`, and `T` is integrally closed in its fraction field `L`, so such
an element lies in `T`. Concretely a generator `f ∈ S'`, written in `L = K(z)`, is a
Laurent polynomial with coefficients in `K`, which turns a spanning set in `L` into
Laurent polynomials with `K`-coefficients and so allows coefficient extraction.

This step has no standalone statement of its own: a faithful one would first have to
fix the identification `Frac (R[z,z⁻¹]) ≃ K(z)` and the embedding `T ↪ L`, which are
set up inside `exists_fg_containing` itself.
-/

/-! ### The fraction-field identification `Frac(R[z,z⁻¹]) = Frac(K[z,z⁻¹]) = K(z)`

This namespace builds:
* the coefficient-change algebra `R[T;T⁻¹] → K[T;T⁻¹]` (`instAlg_S_T`) with its
  coefficient formula (`algST_coeff`);
* the scalar towers through `R[X]` (`instST1`, `instST2`);
* the fact that `K[T;T⁻¹]` is the localization of `R[T;T⁻¹]` obtained by inverting
  the nonzero constants of `R` (`instLoc_main`), by applying `IsLocalization.commutes`
  to the coefficient and `Away X` localizations of `R[X]`;
* the transfer lemma `isFractionRing_of_isLocalization_le`, that a fraction ring of a
  localization at `M ≤ nonZeroDivisors` is a fraction ring of the base;
* and hence that `Frac(K[T;T⁻¹])` is a fraction ring of `R[T;T⁻¹]`
  (`instFracRing_S_L`), the common field `L = K(z)`.

On top of these come the transfer of N-1 finiteness to `L`, the integral closure
containment `S' ⊆ K[T;T⁻¹]`, and the comparison of `z⁰`-coefficients.
-/
namespace exists_fg_containing

variable (R : Type*) [CommRing R] [IsDomain R]

/-! ### The three intermediate pieces

With `K = FractionRing R`, `S = LaurentPolynomial R`, `T = LaurentPolynomial K` and
`L = FractionRing T` the common field `K(z)`, a fraction ring of `S` by
`instFracRing_S_L`, the three mathematical pieces of the argument are captured below,
and `exists_fg_containing` combines them.
-/

end exists_fg_containing

-- ===== merged from Sec161/Tag032K =====

/-!
# N-1 and N-2 descend along a finite extension of domains

All rings are commutative with unit. A *domain* is an integral domain, a nonzero
commutative ring with no zero divisors, and `Frac R` denotes the field of fractions of
a domain `R`.

For a ring extension `A ⊂ B` and a subset `C` with `A ⊂ C`, the *integral closure of
`A` in `C`* is the set of `c ∈ C` satisfying a monic equation
`cⁿ + a_{n-1} c^{n-1} + ⋯ + a₀ = 0` with all `aᵢ ∈ A`; it is a subring of `C`
containing `A`, and is `integralClosure A C : Subalgebra A C`. A ring map `A → B` is
*finite* when `B` is a finitely generated `A`-module. A *finite extension of domains*
is an inclusion `R ⊂ S` of domains making `S` a finitely generated `R`-module, modelled
below by an injective algebra map `R → S`.

A domain `R` is *N-1* when the integral closure of `R` in `K = Frac R` is a finite
`R`-module, and *N-2*, or *Japanese*, when for every finite field extension `L/K` the
integral closure of `R` in `L` is a finite `R`-module.

The main results: let `R` be a Noetherian domain and `R ⊂ S` a finite extension of
domains. If `S` is N-1 then `R` is N-1, and if `S` is N-2 then `R` is N-2.

The role of `K = Frac R` is played by Mathlib's `FractionRing R`. A finite field
extension `L/K` is modelled by a field `L` with a finite-dimensional
`(FractionRing R)`-algebra structure together with a compatible `R`-algebra structure,
the integral closure of `R` in `L` being taken along the tower `R ⊂ K ⊂ L`.
-/

@[expose] public section

universe u v w uR uS

/-- Core lemma: integral closure of `R` in a field `K` injects (as `R`-module) into the
integral closure of `S` in `L`, given an injective `R`-algebra map `K →ₐ[R] L`. -/
theorem isN_core
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K]
    [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (hfin : Module.Finite R S)
    (φ : K →ₐ[R] L) (hφ : Function.Injective φ)
    (hS : Module.Finite S (integralClosure S L)) :
    Module.Finite R (integralClosure R K) := by
  -- `integralClosure S L` is finite over `R`, hence Noetherian over `R`.
  have : Module.Finite R (integralClosure S L) :=
    Module.Finite.trans S (integralClosure S L)
  have : IsNoetherian R (integralClosure S L) :=
    isNoetherian_of_isNoetherianRing_of_finite R (integralClosure S L)
  -- Membership: `φ` maps `integralClosure R K` into `integralClosure S L`.
  -- Build the `R`-linear map.
  let g : (integralClosure R K) →ₗ[R] L :=
    φ.toLinearMap.comp (integralClosure R K).val.toLinearMap
  have hmem (c : integralClosure R K) : g c ∈ Subalgebra.toSubmodule (integralClosure S L) :=
    (show IsIntegral S (φ c) from (IsIntegral.map φ c.property).tower_top)
  let f : (integralClosure R K) →ₗ[R] ↥(Subalgebra.toSubmodule (integralClosure S L)) :=
    { toFun := fun c => ⟨g c, hmem c⟩
      map_add' := by
        intro a b
        ext
        simp [g]
      map_smul' := by
        intro r a
        ext
        simp [g] }
  have hinjf : Function.Injective f := fun a b hab =>
    Subtype.ext (hφ (show φ a = φ b from congrArg Subtype.val hab))
  have : IsNoetherian R ↥(Subalgebra.toSubmodule (integralClosure S L)) := this
  exact Module.Finite.of_injective f hinjf

/-- An injective algebra map `R → S` of domains lifts to an injective `R`-algebra map
`Frac R → Frac S`. -/
private theorem exists_injective_algHom_fractionRing (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S)) :
    ∃ φ : FractionRing R →ₐ[R] FractionRing S, Function.Injective φ := by
  have halg : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (FaithfulSMul.algebraMap_injective S (FractionRing S)).comp hinj
  exact ⟨IsFractionRing.liftAlgHom (g := Algebra.ofId R (FractionRing S)) halg,
    RingHom.injective _⟩

/-- **Statement 1 (N-1 descends, part of Stacks Tag 032K).**
Let `R` be a Noetherian domain and `R ⊂ S` a finite extension of domains
(modelled by an injective algebra map `R → S` with `S` finite over `R`).
If `S` is N-1, then `R` is N-1. -/
@[stacks 032K "(1)"]
theorem isN1_of_finite_of_isN1
    (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : StacksIsN1 S) : StacksIsN1 R := by
  -- `L = FractionRing S` is an `R`-algebra and an `S`-algebra with a scalar tower.
  -- The fraction field `K = FractionRing R` embeds into `L` as an `R`-algebra map.
  obtain ⟨φ, hφ⟩ := exists_injective_algHom_fractionRing R S hinj
  exact isN_core R S (FractionRing R) (FractionRing S) hfin φ hφ hS

-- `small_of_finite_field` and `shrink_isScalarTower`, used just below, moved to
-- `StacksFrontier.RingTheory.Nagata.Shrink`: the transport lemmas of `Nagata.Japanese` came to need
-- them, and that file is upstream of this one.

-- this proof's elaboration needs more than the default heartbeat budget
open scoped TensorProduct in
/-- **Per-extension reduction step for Statement 2 (Stacks Tag 032K, N-2 case).**

Fix a single finite field extension `L / K`, where `K = FractionRing R`.  This lemma
is the heart of the N-2 descent: it produces, for this `L`, the conclusion
`Module.Finite R (integralClosure R L)`.  Quantifying over all such `L` (done in
`isN2_of_finite_of_isN2` below by `intro`) gives `IsN2_032k R`.

Let `K = FractionRing R` and `E = FractionRing S`. The structure map `R → S → E` lifts
to an injective `R`-algebra, hence `K`-algebra, embedding `φ₀ : K →ₐ[R] E`, exactly as in
the N-1 case, making `E` a finite field extension of `K`. One then builds a compositum
`M` of `L` and `E` over `K`:

* form the finite `E`-algebra `T = E ⊗[K] L`, finite over `E` by base change of the
  finite `K`-module `L`;
* `T` is a nonzero commutative ring, so it has a maximal ideal `I`; set `M = T ⧸ I`, a
  field finite-dimensional over `E`;
* the right inclusion `L → T → M` gives an injective `K`-algebra, hence `R`-algebra,
  map `φ : L →ₐ[R] M`, injective because it is a ring homomorphism out of the field `L`.

Since `S` is N-2 and `M/E` is a finite field extension, `integralClosure S M` is a
finite `S`-module. The core lemma `isN_core` then transports finiteness back down:
`integralClosure R L` embeds as an `R`-submodule of `integralClosure S M`, which is
`R`-finite because it is `S`-finite and `S` is `R`-finite, and `R` Noetherian makes the
submodule finite. Hence `integralClosure R L` is a finite `R`-module. -/
theorem isN2_step
    (R S L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field L] [Algebra (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : IsN2_032k S) : Module.Finite R (integralClosure R L) := by
  -- `IsN2_032k S` unfolds to the universe-coupled `IsN2Aux S`, which quantifies over
  -- fields in `S`'s own universe -- exactly what the shrunk compositum `N` needs.
  change IsN2Aux S at hS
  -- E := FractionRing S receives K = FractionRing R via the lifted structure map (as in N-1).
  obtain ⟨φ₀, -⟩ := exists_injective_algHom_fractionRing R S hinj
  let : Algebra (FractionRing R) (FractionRing S) := φ₀.toRingHom.toAlgebra
  have htow : IsScalarTower R (FractionRing R) (FractionRing S) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R (FractionRing S) x = φ₀ (algebraMap R (FractionRing R) x)
    rw [AlgHom.commutes φ₀ x]
  -- Compositum T := E ⊗[K] L, finite over E; M := T ⧸ (maximal ideal) is a field.
  have : Module.Finite (FractionRing S) ((FractionRing S) ⊗[FractionRing R] L) :=
    Module.Finite.base_change (FractionRing R) (FractionRing S) L
  obtain ⟨I, hI⟩ := Ideal.exists_maximal ((FractionRing S) ⊗[FractionRing R] L)
  have : I.IsMaximal := hI
  let : Field (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) := Ideal.Quotient.field I
  -- Embedding φ : L →ₐ[R] M (right inclusion into the tensor product, then quotient).
  let incR : L →ₐ[FractionRing R] ((FractionRing S) ⊗[FractionRing R] L) :=
    Algebra.TensorProduct.includeRight
  let φ : L →ₐ[R] (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    ((Ideal.Quotient.mkₐ (FractionRing R) I).comp incR).restrictScalars R
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  -- `M := T ⧸ I` lives in universe `max u_S u_L`, so `hS M` would fail the (monomorphic)
  -- universe check of `IsN2_032k S` (which only quantifies over fields in S's own universe).
  -- Since `M` is finite-dimensional over `FractionRing S : Type u_S`, it is `Small.{u_S}`;
  -- shrink it to `N : Type u_S` (a `FractionRing S`-algebra-isomorphic copy), apply `hS`
  -- there, and transport the embedding `φ` and the finiteness conclusion across the equiv.
  have hMfin : Module.Finite (FractionRing S)
      (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (FractionRing S) I).toLinearMap Ideal.Quotient.mk_surjective
  have hsmall : Small.{_} (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    small_of_finite_field (E := FractionRing S) (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)
  -- universe-`u_S` model `N`, with the `FractionRing R`-algebra equivalence to `M`.
  let N := Shrink.{_} (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)
  -- scalar towers on `N`, transported from the (universe-`max u_S u_L`) compositum.
  have towRFRN : IsScalarTower R (FractionRing R) N :=
    shrink_isScalarTower (R := R) (S := FractionRing R)
      (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  have towRSN : IsScalarTower R S N :=
    shrink_isScalarTower (R := R) (S := S) (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  have towSFSN : IsScalarTower S (FractionRing S) N :=
    shrink_isScalarTower (R := S) (S := FractionRing S)
      (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  let eFR : N ≃ₐ[FractionRing R] (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    Shrink.algEquiv (FractionRing R) _
  -- transport the embedding `φ : L →ₐ[R] M` to `φN : L →ₐ[R] N`
  let φN : L →ₐ[R] N := (eFR.symm.toAlgHom.restrictScalars R).comp φ
  have hφNinj : Function.Injective φN := eFR.symm.injective.comp hφinj
  -- `N` is `FractionRing S`-algebra-isomorphic to the compositum, so it inherits its
  -- finite-dimensionality; this is the `[FiniteDimensional (FractionRing S) _]` argument
  -- of `IsN2Aux S`, which is not synthesized through `Shrink` on its own.
  have hNfin : Module.Finite (FractionRing S) N :=
    Module.Finite.equiv
      (Shrink.algEquiv (FractionRing S)
        (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)).symm.toLinearEquiv
  -- now `N : Type u_S`, so S's N-2 hypothesis applies, and `isN_core` descends to `R ⊂ L`.
  have hSN : Module.Finite S (integralClosure S N) := @hS N _ _ _ towSFSN hNfin
  exact isN_core R S L N hfin φN hφNinj hSN

/-- **Statement 2 (N-2 descends, part of Stacks Tag 032K).**
Let `R` be a Noetherian domain and `R ⊂ S` a finite extension of domains
(modelled by an injective algebra map `R → S` with `S` finite over `R`).
If `S` is N-2, then `R` is N-2. -/
@[stacks 032K "(2)"]
theorem isN2_of_finite_of_isN2
    (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : IsN2_032k S) : IsN2_032k R := by
  -- N-2 means: for every finite field extension `L / FractionRing R`, the integral
  -- closure of `R` in `L` is `R`-finite.  Fix such an `L` and apply `isN2_step`.
  change IsN2Aux R
  intro L _ _ _ _ _
  exact isN2_step R S L hinj hfin hS

-- ===== merged from Sec161/Tag032M =====

/-!
# In characteristic zero, N-1 and N-2 agree

Let `R` be an integral domain with field of fractions `K = Frac R`.

`R` is *N-1* when the integral closure of `R` in `K` is a finite `R`-module, that is,
finitely generated as an `R`-module. The integral closure of a domain in its own
fraction field is its normalization, so `R` is N-1 exactly when its normalization is
module-finite over `R`. `R` is *N-2*, also called *Japanese*, when for every finite
field extension `L/K` the integral closure of `R` in `L` is a finite `R`-module.

The main result: let `R` be a Noetherian domain whose fraction field `K` has
characteristic zero. Then `R` is N-1 if and only if `R` is N-2.

That N-2 implies N-1 holds for any domain, by taking `L = K`. For the converse,
replace `R` by its normalization `R'`, which is finite over `R` by N-1; then `R'` is a
Noetherian normal domain with fraction field `K`, and for a finite extension `L/K` the
integral closure of `R` in `L` equals that of `R'` in `L`. Since `K` has characteristic
zero every finite extension `L/K` is separable, so the integral closure of `R'` in `L`
is finite over `R'`, hence over `R`.

Being a finite `R`-module is `Module.Finite R M`, and the integral closure of `R` in an
extension ring or field is the subalgebra `integralClosure R L` of elements integral
over `R`. The characteristic-zero hypothesis is placed on the fraction field `K`,
equivalently on `R`, and is used solely to guarantee separability of every finite
extension of `K`.
-/

@[expose] public section

-- Main Statement(s)

end
end
end

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false

end
