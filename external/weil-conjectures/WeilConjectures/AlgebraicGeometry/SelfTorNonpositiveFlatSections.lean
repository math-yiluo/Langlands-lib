/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.SelfTorNonpositiveChosenComparisons
import WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Affine coordinates for nonpositive flat resolutions

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS.
(blueprint: new-n4-self-tor-nonpositive-flat-sections). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Nonpositive termwise flat resolutions have affine quotient-tensor coordinates.
This lemma does not construct algebraic augmented comparison maps, and does not
compare an unbounded K-flat resolution with a bounded one.

Source: Stacks Project, Tag 08DX(2), affine calculation; Tags 06YG and 06YB,
K-flat tensor comparison; Tag 01I9, affine sections; Tag 00LS(1), comparison
of augmented resolutions.
(blueprint: new-n4-self-tor-nonpositive-flat-sections).

Proof: On each affine chart U identify B restricted to U with tilde(A/I),
using the closed-immersion quotient presentation and its quotient section map.
Sheafify the chosen projective resolution of A/I and extend it from degree j
in the chain complex to cochain degree -j. Exactness of tilde makes its
augmentation p a quasi-isomorphism. The terms are flat and vanish in positive
cochain degrees, so this complex L is K-flat. The restriction of K is likewise
nonpositive and flat, hence K-flat. The augmented zigzag
K|U tensor B|U[0] <- K|U tensor L -> B|U[0] tensor L
-> L tensor B|U[0] uses id tensor p, q|U tensor id, and braiding. The first
two legs are quasi-isomorphisms by the acyclic-cone criterion for K-flatness.
Take homology, invert these legs, use the affine total-tensor comparison,
exactness of tilde, and extension homology in degree -n. Compose with the
normalized tilde section unit to obtain c_U; these units fix the normalization
simultaneously, so the c_U are not arbitrary chart equivalences.

For a supplied augmented comparison a on a basic inclusion V in U, its
associated sheaf map commutes with the augmentations: on affine sections this
is exactly the augmentation equation; tilde full faithfulness promotes it to
an equality of sheaf maps. The quotient equation identifies the coefficient
map with restriction of B, and the pure tensor equation identifies the map
associated to k with the tensor of a and that coefficient map. Restrict the U
zigzag to V and compare with the V zigzag. Tensor functoriality, the preceding
augmentation square, and naturality of braiding make each square commute.
Taking homology and cancelling the isomorphism legs gives the comparison
square. Naturality of the tilde section unit and the exact restriction-of-
scalars homology isomorphism give the displayed element equation. This works
for any supplied lift and requires no selection or construction of lifts here.
For n=0 the same homology/augmentation calculation applies. For I=top, zero
coordinate rings, and empty basic opens all relevant quotient modules are
zero and the same diagrams and isomorphisms remain valid. -/
theorem exists_selfTor_nonpositive_flat_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hbounded : ∀ j : ℤ, 0 < j → IsZero (K.X j))
    (hflat : ∀ j : ℤ, SheafOfModules.IsFlat (K.X j)) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj B)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).mapHomologicalComplex (.down ℕ)).obj
            (projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
              ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).complex).homology n) ≃ₗ[Γ(Y, U.1)]
              Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  -- Keep the tensor homology object named while unpacking the comparison data.
  intro B S Q
  obtain ⟨c, hc⟩ := exists_selfTor_nonpositive_chosen_comparisons
    i K q hbounded hflat hq n
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk
  obtain ⟨ψ₀, a₀, k₀, hψ₀, ha₀, hk₀, hc₀⟩ := hc V U h hbasic
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hψ₀ x).trans (hψ x).symm
  subst ψ₀
  have hH : Nonempty (Homotopy k₀ k) :=
    ModuleCat.quotient_tensor_resolution_lift_homotopy
      I J φ P R ψ a₀ a k₀ k hψ ha₀ ha hk₀ hk
  obtain ⟨H⟩ := hH
  have heq := H.homologyMap_eq n
  intro e x
  exact (hc₀ x).trans
    (congrArg (fun y ↦ c V (e.hom y)) (ConcreteCategory.congr_hom heq x))


end AlgebraicGeometry
