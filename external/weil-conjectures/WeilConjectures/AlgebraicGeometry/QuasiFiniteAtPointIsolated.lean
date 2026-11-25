/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finite at a point implies isolated in the fibre

Source: Stacks Project, Morphisms, Lemma 01TH
(blueprint: lem-weil-pbc-quasi-finite-at-point-isolated).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism locally of finite type and quasi-finite at a point has an isolated
point in its scheme-theoretic fibre (Stacks Project, Lemma 01TH).
(blueprint: lem-weil-pbc-quasi-finite-at-point-isolated)

Proof (Stacks 01TH, (1) implies (2), with the node's affine identifications):
1. Unpack `IsQuasiFiniteAtPoint` (`pqf-def-quasifinite`, Stacks 01TD) to obtain affine
   opens `U = Spec A` containing `x` and `V = Spec R` containing its image, with
   `f(U) ⊆ V`. The finite-type ring map is quasi-finite at the prime corresponding
   to `x`; by `def-weil-pbc-ring-map-quasi-finite-at-prime`, the corresponding prime
   of the fibre ring is an open singleton.
2. The residue field of `V` at `s = f x` is that of `S`, compatibly with its canonical
   point map (`lem-weil-pbc-residue-field-point-naturality`). Consequently the fibre
   of `U → V` embeds as the open subset `p⁻¹(U)` of `X_s`, compatibly with the first
   projection (`lem-weil-pbc-open-fibre-product`).
3. Identify this fibre with the spectrum of `A ⊗[R] κ(p)` using
   `lem-weil-pbc-spec-residue-field-identification` and
   `lem-weil-pbc-fibre-product-affine-spectra`. Uniqueness of fibre products
   (`def-pc-fibre-product`) gives a homeomorphism onto `p⁻¹(U)` respecting projections.
4. The homeomorphism `fiberHomeo` (`def-pc-scheme-fibre`) supplies the unique point
   `ξ = f.asFiber x` over `x`. It lies in `p⁻¹(U)` and corresponds to the fibre prime from step 1
   by `lem-weil-pbc-fibre-ring-primes-bijection`. Its singleton is therefore open
   in `p⁻¹(U)`, hence in `X_s` since `p⁻¹(U)` is open.
5. Transport the singleton through `fiberHomeo` to the point `⟨x, rfl⟩` in the
   subspace `f⁻¹({s})`. This gives the second, equivalent, openness statement.

The point `ξ` is Mathlib's `f.asFiber x = (f.fiberHomeo (f x)).symm ⟨x, rfl⟩`, the unique
point of the fibre over `x` (`fiberι_asFiber`); isolation is spelled as in the landed
consumers (`IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`, STATE line QUASI-FINITE).
-/
theorem quasiFiniteAtPoint_isolated_in_fiber
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType f] (x : X)
    (hfx : IsQuasiFiniteAtPoint f x) :
    IsOpen ({f.asFiber x} : Set (f.fiber (f x))) ∧
      IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := by
  obtain ⟨U, hx, hU, V, hV, e, hft, hq⟩ := hfx
  let := (f.appLE V U e).hom.toAlgebra
  let := hft
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := q.comap (algebraMap Γ(S, V) Γ(X, U))
  let H := PrimeSpectrum.preimageHomeomorphFiber Γ(S, V) Γ(X, U) p
  have ho : IsOpen ({⟨q, rfl⟩} : Set
      (PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) ⁻¹' {p})) := by
    rw [← H.isOpen_image, Set.image_singleton]
    exact hq
  have hqa : Algebra.QuasiFiniteAt Γ(S, V) q.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q ho
  -- Identify the affine stalk map with the map between the localizations.
  have hqm : f.QuasiFiniteAt x := by
    rw [QuasiFiniteAt,
      RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f V hV U hU e hx)]
    apply RingHom.QuasiFinite.of_comp
      (g := algebraMap Γ(S, V)
        (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal))
    have heq : (Localization.localRingHom _ _ (f.appLE V U e).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx).1).symm).comp
        (algebraMap Γ(S, V)
          (Localization.AtPrime (hV.primeIdealOf ⟨f x, e hx⟩).asIdeal)) =
        algebraMap Γ(S, V) (Localization.AtPrime q.asIdeal) := by
      ext a
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      rfl
    exact heq.symm ▸ RingHom.quasiFinite_algebraMap.mpr hqa
  have hfiber : IsOpen ({f.asFiber x} : Set (f.fiber (f x))) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqm
  refine ⟨hfiber, ?_⟩
  simpa only [Set.image_singleton, asFiber, Homeomorph.apply_symm_apply] using
    (f.fiberHomeo (f x)).isOpenMap _ hfiber

end AlgebraicGeometry.Scheme.Hom
