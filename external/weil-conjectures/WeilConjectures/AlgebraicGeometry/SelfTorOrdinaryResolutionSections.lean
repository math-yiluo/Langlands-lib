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
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons
import WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Affine sections of ordinary tensor with a K-flat quotient resolution

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS.
(blueprint: new-b3-self-tor-ordinary-resolution-sections). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Affine tensor-resolution homology computes the sections of the ordinary total tensor
with a global K-flat resolution. This is a statement entirely about complexes and homology;
no derived tensor or existence of algebraic resolution lifts occurs in its conclusion.
Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS.
(blueprint: new-b3-self-tor-ordinary-resolution-sections).

Proof: Restrict K and q to each affine chart. Identify the restricted closed structure
sheaf B with the associated sheaf of A/I, using the canonical quotient identification.
Sheafify the chosen projective resolution P of A/I and extend it to nonpositive
cochain degrees. Its augmentation is a quasi-isomorphism by exactness of tilde,
and it is K-flat since its terms are flat and it is bounded above. Restriction
of K remains K-flat. Use the two augmentations in the zigzag
K tensor B <- K tensor P -> B tensor P -> P tensor B (with the last arrow the
braiding). The two first arrows are quasi-isomorphisms: tensor with a K-flat
complex preserves quasi-isomorphisms. Thus the zigzag induces a homology
isomorphism. The termwise tilde tensor comparison identifies P tensor B with
tilde of the quotient tensor resolution, with chain degree n in cochain degree -n.
Exact tilde commutes with homology, and its affine sections unit gives c_U.

For a basic inclusion, associate a sheaf map on V to the semilinear map a by
scalar extension, the tilde adjunction, and the affine restriction comparison.
The quotient equation identifies the associated map of quotient sheaves with
the restriction of B. The augmentation equation, tested on affine sections
and transported by full faithfulness of tilde, says that the augmented sheaf
resolutions commute. The pure tensor identity, by extensionality on pure
tensors, identifies the associated tensor map of k with a tensor this quotient
map. Restrict the preceding zigzag for U to V and compare it with the zigzag
for V. Each square commutes by tensor functoriality, the augmentation square,
and naturality of the braiding. Take homology and invert the two isomorphism
legs to obtain the equality of the two composite comparisons. Naturality of
the tilde sections unit turns this equality into the displayed section formula.
Exact restriction of scalars supplies mapHomologyIso. This is true for every lift;
no inverse is chosen at chain level. The construction applies to degree zero,
the zero quotient, and the empty basic open, using zero rings and zero modules. -/
theorem exists_selfTor_ordinary_resolution_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
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
  intro B S Q
  obtain ⟨c, hc⟩ := exists_selfTor_ordinary_localized_comparisons i K q hK hq n
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk
  obtain ⟨ψ₀, a₀, k₀, hlift⟩ := hc V U h hbasic
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hlift.1 x).trans (hψ x).symm
  subst ψ₀
  obtain ⟨H⟩ := ModuleCat.quotient_tensor_resolution_lift_homotopy
    I J φ P R ψ a₀ a k₀ k hψ hlift.2.1 ha hlift.2.2.1 hk
  have heq := H.homologyMap_eq n
  intro e x
  exact (hlift.2.2.2 x).trans
    (congrArg (fun y ↦ c V (e.hom y)) (ConcreteCategory.congr_hom heq x))


end AlgebraicGeometry
