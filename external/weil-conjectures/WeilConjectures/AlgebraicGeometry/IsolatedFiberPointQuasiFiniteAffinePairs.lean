/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Isolated fibre points and quasi-finiteness on affine pairs

Source: Stacks Project, Morphisms, Tag 01TH, (2) implies (4), and Tag 01T2
(blueprint: lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An isolated point of the fibre of a locally finite type morphism gives a finite-type
ring map, quasi-finite at the corresponding prime, on every affine pair containing the
point. Source: Stacks Project, Morphisms, Tag 01TH, (2) implies (4), and Tag 01T2
(blueprint: lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs).

Proof:
1. Apply `lem-weil-pbc-lft-affine-pairs` (Tag 01T2) to obtain finite type of the
   map on sections of the affine opens.
2. By `lem-weil-pbc-affine-open-spec-points` and
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`, the affine charts identify
   the point with its prime q and its image with the contracted prime p. By
   `lem-weil-pbc-fibre-ring-primes-bijection`, q determines a unique fibre-ring prime.
3. Apply `lem-weil-pbc-residue-field-point-naturality` to the target open immersion and
   `lem-weil-pbc-open-fibre-product` to identify the fibre of the restricted morphism
   with the open inverse image of the source open in the original fibre.
4. Use `lem-weil-pbc-spec-residue-field-identification`, residue-field naturality, and
   `lem-weil-pbc-fibre-product-affine-spectra` to identify that open fibre with the
   spectrum of the fibre ring, compatibly with the projection to the source.
5. Injectivity of the affine chart and uniqueness in the fibre-prime bijection identify
   the given fibre point with the fibre-ring prime of q. Its singleton is open in the
   original fibre, hence in this open piece, hence in the fibre-ring spectrum.
6. Together with finite type from step 1, this is precisely
   `def-weil-pbc-ring-map-quasi-finite-at-prime`.

The algebra structure is the one induced by the map on sections. The existential
finite-type witness supplies the instance needed by `Algebra.IsQuasiFiniteAtPrime`. -/
theorem Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hisolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x))))
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hx : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := (f.appLE V U hUV).hom.toAlgebra
    ∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U),
      letI := hft
      Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩) := by
  let := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  refine ⟨inferInstance, ?_⟩
  have hq := (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hisolated).quasiFiniteAt
    hU hV hUV hx
  have hopen := (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
    (R := Γ(S, V)) (hU.primeIdealOf ⟨x, hx⟩)).mp hq
  let q := hU.primeIdealOf ⟨x, hx⟩
  let e := PrimeSpectrum.preimageHomeomorphFiber Γ(S, V) Γ(X, U)
    (q.comap (algebraMap Γ(S, V) Γ(X, U)))
  change IsOpen {e ⟨q, rfl⟩}
  rw [← Set.image_singleton, e.isOpen_image]
  exact hopen

end AlgebraicGeometry
