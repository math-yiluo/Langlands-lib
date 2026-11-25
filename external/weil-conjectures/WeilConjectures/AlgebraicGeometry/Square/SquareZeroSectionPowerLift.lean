/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Section.SectionAffineOpenKillsCohomology
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerObstruction

/-! # Lifting a tensor power of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1)
and the boundary calculation following it.
(blueprint: lem-sc-square-zero-section-power-lift).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Some positive tensor power of the given section lifts, after the tensor-power
and pullback identifications. The conclusion is equality of section morphisms;
it makes no assertion about nonvanishing loci or affineness upstairs.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1)
and the following boundary calculation.
(blueprint: lem-sc-square-zero-section-power-lift).

Proof:
1. Put N = j^*L and M_d = I tensor L^d. Invertibility makes tensoring the
   closed-immersion ideal sequence exact. The unit-quotient theorem identifies
   its quotient with j_*j^*(L^d). Pullback commutes with tensor products, giving
   j_*(N^d). Both I and M_d are quasi-coherent, and I M_d = 0 by I^2 = 0.
2. The annihilated-module theorem identifies M_d with j_*G_d, G_d = j^*M_d.
   The affine-morphism edge isomorphism identifies H^1(X,M_d) with H^1(Z,G_d).
   The degree-n exact sequence gives a connecting class xi for s.
3. Take the direct sums over all d of these exact sequences, with the tensor
   multiplication on powers of L. Locally a frame makes the algebra a polynomial
   algebra, hence commutative. Its kernel has square zero because I^2 = 0.
   The boundary derivation theorem gives partial(s^k) = k s^(k-1) xi by induction.
   Naturality for inclusion and projection of each graded summand identifies
   this boundary with the boundary of the degree-nk exact sequence.
4. Local Noetherianity implies quasi-separatedness. The affine-open cohomology
   killing theorem on Z, applied to N^n, s, G_n, and xi, gives e with s^e xi = 0.
   Naturality of the edge isomorphism for multiplication by s^e transports this
   equality to X. Thus partial(s^(e+1)) = 0; exactness supplies t in L^(n*(e+1)).
5. Set k = e+1. Iterate the pullback tensor comparison and the associators to
   identify j^*(L^(n*k)) with (N^n)^k. For n = 0 use the monoidal unit comparison;
   for positive n use the tensor comparisons inductively. Choose this isomorphism
   as e in the conclusion. These comparisons send the restriction of t to s^k,
   so the corresponding morphisms from the structure module are equal as stated.
   No fibre or nonvanishing calculation is needed here. -/
theorem exists_section_power_lift_of_square_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Z] [CompactSpace Z]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (s : (((tensorPullback j).obj L).tensorPow n).val.presheaf.obj
      (Opposite.op ⊤)) (U : Z.Opens)
    (hU : (U : Set Z) = nonvanishingLocus (((tensorPullback j).obj L).tensorPow n) s)
    (hAffine : IsAffineOpen U) :
    ∃ k : ℕ, 0 < k ∧
      ∃ t : (L.tensorPow (n * k)).val.presheaf.obj (Opposite.op ⊤),
        ∃ e : (tensorPullback j).obj (L.tensorPow (n * k)) ≅
            (((tensorPullback j).obj L).tensorPow n).tensorPow k,
          homOfGlobalSection ((tensorPullback j).obj (L.tensorPow (n * k)))
              (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
                (L.tensorPow (n * k))).val.app (Opposite.op ⊤) t) ≫ e.hom =
            tensorPowSection (homOfGlobalSection
              (((tensorPullback j).obj L).tensorPow n) s) k := by
  classical
  have : ((tensorPullback j).obj L).IsInvertible :=
    ((invertible_pullback_tensor j).1 L).2
  let F := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
  obtain ⟨hF, xi, hlift⟩ := exists_square_zero_section_power_obstruction j L hI n s
  have : F.IsQuasicoherent := hF
  obtain ⟨e, he⟩ := exists_tensorPowSection_cohomology_eq_zero Z
    (((tensorPullback j).obj L).tensorPow n) s U hU hAffine F 1 (by decide) xi
  obtain ⟨t, a, ha⟩ := hlift e he
  exact ⟨e + 1, Nat.zero_lt_succ e, t, a, ha⟩

end AlgebraicGeometry.Scheme.Modules
