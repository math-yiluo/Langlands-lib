/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists

/-! # Resolving complexes for an arbitrary simultaneous reduction
Source: diagonal tower system proof, steps (2) and (3).
(blueprint: lem-sfb-diagonal-reduction-resolution). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] diagonalScalarExtension diagonalForget diagonalScalarAdjunction

/-- Every object has a common torsion-free representative on which the counit of the
supplied universal derived reduction is invertible.
Source: diagonal tower system proof, steps (2) and (3).
(blueprint: lem-sfb-diagonal-reduction-resolution).
Proof: use flat-term resolutions to resolve every complex by complexes on which all
positive prime-power maps are monomorphisms. Exact scalar extension preserves these
monomorphisms. The quotient short exact sequences imply that ordinary simultaneous
reduction preserves quasi-isomorphisms between these representatives. Derive on this
resolving class, and compare its counit with the supplied counit by uniqueness of left
derived functors. The counit-compatible comparison is invertible, so invertibility on
the resolving class transfers to the supplied reduction. -/
theorem diagonal_reduction_resolution (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (K : DerivedCategory (DiagonalAb W)) :
    ∃ (P : CochainComplex (DiagonalAb W) ℤ) (_e : DerivedCategory.Q.obj P ≅ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ IsIso (D.ε.app P) := by
  let L := diagonalScalarExtension ℓ W
  let : L.Additive := scalarExtension_additive ℓ W
  let : PreservesFiniteLimits L := scalarExtension_exact ℓ W
  have : PreservesColimits L := (diagonalScalarAdjunction ℓ W).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits L := inferInstance
  let good : CochainComplex (DiagonalAb W) ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))
  have res : ∀ K : CochainComplex (DiagonalAb W) ℤ,
      ∃ (P : CochainComplex (DiagonalAb W) ℤ) (p : P ⟶ K), good P ∧ QuasiIso p := by
    intro K
    obtain ⟨P, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    refine ⟨P, p, ?_, hp⟩
    intro n i
    exact flat_multiplication_mono _
      (integerUnit_mono W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)
  have hm (P : CochainComplex (DiagonalAb W) ℤ) (hP : good P) (n : ℕ) (i : ℤ) :
      Mono (ℓ ^ (n + 1) • 𝟙 (L.obj (P.X i))) := by
    let := hP n i
    have h : Mono (L.map (ℓ ^ (n + 1) • 𝟙 (P.X i))) := inferInstance
    rw [Functor.map_nsmul, L.map_id] at h
    exact h
  obtain ⟨T, ε, hu, _, _, hc⟩ := cochainDerivedFullExists D.ordinary.E good res (by
    intro P Q f hf hP hQ
    let := hf
    exact reductionTower_quasiIso ℓ L D.ordinary f (hm P hP) (hm Q hQ))
  let := hu
  let := D.universal
  let c := Functor.leftDerivedNatIso D.T T D.ε ε
    (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ)) (Iso.refl _)
  obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage K)
  let := hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  refine ⟨P, e, hP, ?_⟩
  have h : c.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = D.ε.app P := by
    dsimp only [c, Functor.leftDerivedNatIso]
    simpa only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app D.T T D.ε ε
        (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ)) (𝟙 _) P
  let := hc P hP
  rw [← h]
  infer_instance

end AlgebraicGeometry.ProEtale
