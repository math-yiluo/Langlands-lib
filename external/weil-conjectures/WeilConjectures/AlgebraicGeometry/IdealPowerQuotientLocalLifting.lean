/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.IdealPowerQuotientLiftingSection

/-! # IdealPowerQuotientLocalLifting

Source: Stacks Project, Properties, Lemma 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Finite affine gluing gives eventual vanishing and lifting of sections for the
quotients by ideal-power annihilators. These are stagewise criteria, not statements
about a colimit or a choice of diagram.

Proof: On an affine open, identify F with the sheaf of M, I with a finitely generated
ideal J, and A_n with the sheaf of M_n = {x : J^n x = 0}. The specified annihilator
condition determines this identification. The cokernel is the sheaf of M/M_n.
For eventual vanishing, the denominator calculation of 01PM applied to the map
J^n -> M/M_n gives a higher power on which the map is zero, and it remains zero
after the quotient transition. Choose a finite affine cover, take the maximum of
these powers, and use sheaf uniqueness for the global map.
For lifting, represent a section on the principal opens D(f_i) of the complement
by fractions x_i/f_i^k. Clearing denominators on the overlaps yields
f_j^k x_i = f_i^k x_j after enlarging k. Put K = {x : f_i^k x = 0 for every i}.
A monomial of sufficiently large degree d has an exponent at least k; send it to
the corresponding monomial with that exponent reduced by k, multiplied by x_i.
Relations between monomials map into K, because multiplying by each f_j^k turns
the relation into the original relation times x_j. Thus this defines J^d -> M/K.
Enlarge d so K is contained in M_d, and compose with M/K -> M/M_d. It evaluates
to the section. This supplies local lifts on a finite affine cover of X.
Quasi-separatedness supplies finite affine covers of all pairwise overlaps.
Apply eventual vanishing to differences of the two local lifts after transporting
them to a common degree. Take the maximum of all cover and overlap exponents;
the local maps then agree on overlaps and glue to a global homomorphism. Its
value equals the desired section by sheaf uniqueness and injectivity of the
quotient projection on U. The empty scheme and empty complement use zero maps;
the unit ideal has zero annihilators and evaluation is ordinary sections.

Source: Stacks Project, Properties, Lemma 01PQ and its reduction to Lemma 01PM.
(blueprint: lem-weil-pbc-ideal-power-quotient-local-lifting). -/
theorem ideal_power_quotient_local_lifting
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
    (hq : ∀ (n m : ℕ) (h : n ≤ m),
      cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) :
    (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), r n m h ≫ φ ≫ q n m h = 0) ∧
    (∀ s : Γ(F, U), ∃ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      (cokernel.π (a n)).app U s = φ.app U (one n)) := by
  constructor
  · intro n φ hφ
    let : (A n).IsQuasicoherent := hqc n
    let : (cokernel (a n)).IsQuasicoherent := Modules.isQuasicoherent_cokernel (a n)
    obtain ⟨m, h, hm⟩ := ideal_power_evaluation_eventually_zero
      ι (cokernel (a n)) U one r hU hone hr n φ hφ
    refine ⟨m, h, ?_⟩
    rw [← Category.assoc, hm, zero_comp]
  · exact ideal_power_quotient_local_lifting_section
      ι F U one r hU hone hr A a hmono hqc hann hquot q hq

end AlgebraicGeometry.Scheme
