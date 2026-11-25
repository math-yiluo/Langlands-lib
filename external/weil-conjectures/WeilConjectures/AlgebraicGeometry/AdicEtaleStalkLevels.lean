/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAlgebraTower
public import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.AlgebraicGeometry.CoefficientConnectedContractibleCover
import WeilConjectures.AlgebraicGeometry.CoefficientConnectedStalkConstant
import WeilConjectures.AlgebraicGeometry.CoefficientEtaleStalkScalarExtension
import all WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity

/-! # Algebraic levels of a normalized etale quotient system

Source: Stacks Project, proetale.tex, Tag 09C6, first paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A normalized constructible etale quotient system with lisse residue has perfect
algebraic stalk levels on an affine weakly contractible cover. The input consists only
of finite etale complexes; no complete complex or completed coefficient ring occurs.
Source: Stacks Project, proetale.tex, Tag 09C6, first paragraph; Tags 094I and 09BI.
(auxiliary; not a blueprint node).

Proof: Induct on n. The canonical quotient from A/J^(n+2) to A/J^(n+1)
is surjective with square-zero kernel, since 2(n+1) is at least n+2.
The given beta and nilpotent-coefficient reflection therefore propagate lisse
finite-type cohomology from C_n to C_(n+1); bounded-above follows from hC.
Cover X by its open connected components and refine each by affine spectra of
w-contractible rings. Disjoint refinements of their covers prove weak
contractibility on the actual coefficient-sized slices. This construction handles
the empty scheme with an empty family. Choose the specified point z in the
component containing each covering member, and let E_n be the explicit exact
derived stalk of C_n at the algebraic closure of the residue field of z.
The single-complex connected-stalk theorem gives perfect E_0 and the individual
constant-realization isomorphisms for every level. The scalar-extension/stalk
comparison, followed by the stalk of beta n, gives the consecutive algebraic
reduction isomorphisms. No inverse limit, reconstruction, or simultaneous choice
of compatible constant markings is used. -/
theorem adicEtale_stalk_levels
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (C : ∀ n : ℕ, adicFiniteEtale.{u, v} X J n)
    (hC : ∀ n : ℕ, IsCoefficientBoundedConstructibleEtale.{u, v}
      X (adicFiniteCoeff J n) (C n))
    (a b : ℤ)
    (hTor : ∀ n : ℕ, HasCoefficientModelTorAmplitude
      (CategoryTheory.ConstantCompletion.finite
        (smallModelComparisonEtaleTopology.{u, v} X) A J n) (C n) a b)
    (hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J 0)
      ((adicResidueCohomology
        (CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) q).obj (C 0)))
    (beta : ∀ n : ℕ,
      (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
        (adicFiniteFactor J (Nat.le_succ n))).obj (C (n + 1)) ≅ C n) :
    ∃ (I : Type (max v (u + 1)))
      (V : I → coefficientProEtaleSiteModel.{u, v} X)
      (f : ∀ i : I, V i ⟶
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      Sieve.ofArrows V f ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ i : I,
        IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
          (V i)).left ∧
        AdicResidueSliceWeaklyContractible.{u, v} X (V i) ∧
        ∃ E : ∀ n : ℕ, DerivedCategory (ModuleCat.{max v (u + 1)} (adicFiniteCoeff J n)),
          DerivedCategory.IsPerfect (E 0) ∧
          (∀ n : ℕ, Nonempty
            ((ConstantScalarRealization.moduleDerivedExtension
              (Ideal.Quotient.factorPowSucc J (n + 1))).obj (E (n + 1)) ≅ E n)) ∧
          ∀ n : ℕ, Nonempty
            ((adicResidueFiniteConstant.{u, v} X J (V i) n).obj (E n) ≅
              (adicResidueRestriction
                (CategoryTheory.ConstantCompletion.finite
                  (coefficientProEtaleModelTopology.{u, v} X) A J n) (V i)).obj
                  ((adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj (C n))) := by
  classical
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : HasPullbacks (smallModelComparisonEtaleSite.{u, v} X) :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale)
  have hlevels (n : ℕ) (q : ℤ) : SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n)
      ((coefficientModelCohomology _ q).obj (C n)) := by
    induction n generalizing q with
    | zero => exact hlisse q
    | succ n ih =>
      have hn : J ^ (n + 1 + 1) ≤ J ^ (n + 1) :=
        Ideal.pow_le_pow_right (by omega)
      have hnil : IsNilpotent (RingHom.ker (adicFiniteFactor J (Nat.le_succ n))) := by
        change IsNilpotent (RingHom.ker (Ideal.Quotient.factor hn))
        rw [Ideal.Quotient.factor_ker]
        refine ⟨2, ?_⟩
        rw [← Ideal.map_pow, ← pow_mul]
        change (J ^ ((n + 1) * 2)).map (Ideal.Quotient.mk (J ^ (n + 1 + 1))) = ⊥
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
        apply Ideal.pow_le_pow_right
        omega
      apply SheafOfModules.lisse_of_nilpotent_coefficient_surjection
        (smallModelComparisonEtaleTopology.{u, v} X)
        (adicFiniteFactor J (Nat.le_succ n))
        (Ideal.Quotient.factor_surjective hn) hnil (C (n + 1)) ?_ ?_ q
      · obtain ⟨c, d, _, hd⟩ := (hC (n + 1)).2
        exact ⟨d, fun j hj ↦ hd j (Or.inr hj)⟩
      · intro j
        exact SheafOfModules.lisse_iso _ _
          ((coefficientModelCohomology _ j).mapIso (beta n)) (ih j)
  obtain ⟨I, V, f, hcover, hV⟩ :=
    exists_coefficient_connected_contractible_cover.{u, v} X
  refine ⟨I, V, f, hcover, ?_⟩
  intro i
  obtain ⟨haff, hweak, z, himage⟩ := hV i
  let E (n : ℕ) : DerivedCategory (ModuleCat.{max v (u + 1)} (adicFiniteCoeff J n)) :=
    (coefficientEtaleDerivedStalk X (adicFiniteCoeff J n) (X.algClosurePoint z)).obj (C n)
  have hlocal (n : ℕ) := coefficient_connected_stalk_constant X (adicFiniteCoeff J n)
    z (V i) haff hweak himage (C n) (by
      obtain ⟨c, d, _, hd⟩ := (hC n).2
      exact ⟨c, d, hd⟩) (hlevels n) a b (hTor n)
  refine ⟨haff, hweak, E, (hlocal 0).1, ?_, fun n ↦ (hlocal n).2⟩
  intro n
  obtain ⟨e⟩ := coefficientEtale_stalk_scalarExtension X
    (Ideal.Quotient.factorPowSucc J (n + 1)) (X.algClosurePoint z) (C (n + 1))
  exact ⟨e ≪≫
    (coefficientEtaleDerivedStalk X (adicFiniteCoeff J n) (X.algClosurePoint z)).mapIso
      (beta n)⟩

end AlgebraicGeometry.Scheme
