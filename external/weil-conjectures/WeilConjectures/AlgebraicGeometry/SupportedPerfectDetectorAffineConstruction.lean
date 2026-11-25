/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.KoszulOpenOrthogonality
import WeilConjectures.AlgebraicGeometry.AffineDerivedOpenTransport
import WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties
import Mathlib.Topology.Compactness.Bases
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Koszul construction with its open restriction unit
Source: Stacks Project, Tags 0A9A and 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine-construction).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Kernel and cokernel closure give quasi-coherent homology, then descend through Q. -/
private theorem qcoh_of_qcoh_terms (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hL : ∀ n, (L.X n).IsQuasicoherent) :
    schemeDerivedQCohProperty Y (DerivedCategory.Q.obj L) := by
  intro n
  let S := L.sc n
  have : S.X₁.IsQuasicoherent := hL _
  have : S.X₂.IsQuasicoherent := hL _
  have : S.X₃.IsQuasicoherent := hL _
  have := Scheme.Modules.isQuasicoherent_kernel S.g
  have hq := Scheme.Modules.isQuasicoherent_cokernel (kernel.lift S.g S.f S.zero)
  exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
    ((S.homologyIsoCokernelLift).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).app L).symm) hq

/-- Construct the supported Koszul object and its orthogonality comparison with the open unit.
Source: Stacks Project, Tags 0A9A and 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine-construction).

Proof:
1. Present X as Spec A. The quasi-compact complement U is covered by finitely many D(f_i).
   Sheafify and localize the finite Koszul complex on these functions to obtain E.
2. Finite free Koszul terms make E perfect and its homology quasi-coherent. Multiplication
   by each f_i is null-homotopic, so the homology stalks vanish on U (Tag 0663).
3. Exact restriction to U has a derived right adjoint R. Transport Tag 09IR along the
   affine presentation: for any quasi-coherent K orthogonal
   to all shifts of E, the canonical unit K to R(K restricted to U) is invertible.
   The empty tuple and the empty scheme satisfy the same assertion. -/
theorem supported_perfect_detector_affine_construction
    (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : (U : Set X) = Tᶜ) :
    ∃ (E : schemeDerivedQCohCategory X)
      (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X)
      (adj : (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R),
      Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsIso (adj.unit.app K.obj) := by
  classical
  let A := Γ(X, ⊤)
  let a : Spec (.of A) ≅ X := X.isoSpec.symm
  have hcover : U ⊔ a.hom ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso, sup_top_eq]
  have hqc : IsCompact (a.hom ⁻¹ᵁ U : Set (Spec (.of A))) := by
    apply a.hom.homeomorph.isCompact_preimage.mpr
    change IsCompact (U : Set X)
    rwa [hU]
  have hUo : IsOpen (U : Set X) := by
    rw [hU]
    exact hT.isOpen_compl
  obtain ⟨s, hs, hsU⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
      (fun f : A ↦ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))
      PrimeSpectrum.isTopologicalBasis_basic_opens
      (a.hom ⁻¹ᵁ U : Set (Spec (.of A))) hqc (hUo.preimage a.hom.continuous)
  let := hs.fintype
  let r := Fintype.card s
  let e : Fin r ≃ s := (Fintype.equivFin s).symm
  let f : Fin r → A := fun i ↦ (e i).val
  have hZ : ∀ x : PrimeSpectrum A, x ∉ a.hom ⁻¹ᵁ U ↔ ∀ i : Fin r, f i ∈ x.asIdeal := by
    intro x
    change x ∉ (a.hom ⁻¹ᵁ U : Set (Spec (.of A))) ↔ _
    rw [hsU]
    simp only [Set.mem_iUnion, not_exists]
    constructor
    · intro hx i
      exact not_not.mp (hx (e i).val (e i).property)
    · intro hx b hb
      obtain ⟨i, hi⟩ := e.surjective ⟨b, hb⟩
      exact not_not.mpr (by simpa only [f, hi] using hx i)
  obtain ⟨hD, hO, F, RS, RX, adjS, adjX, _, hqF, hqI, hpF, hsF, hshift, hunit⟩ :=
    affine_derived_open_transport X A a U
  let := hD
  let := hO
  obtain ⟨hshift⟩ := hshift
  let := hshift
  let Q : schemeDerivedCategory (Spec (.of A)) := DerivedCategory.Q.obj
    ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
  obtain ⟨hpQ, hsQ⟩ := affine_koszul_geometric_properties A r f
  have hqQ : schemeDerivedQCohProperty (Spec (.of A)) Q := by
    apply qcoh_of_qcoh_terms
    intro n
    change ((tilde.functor (.of A)).obj _).IsQuasicoherent
    infer_instance
  let E : schemeDerivedQCohCategory X := ⟨F.functor.obj Q, hqF Q hqQ⟩
  refine ⟨E, RX, adjX, hpF Q hpQ, ?_, ?_⟩
  · have hsQ' : ∀ (n : ℤ) (x : Spec (.of A)), x ∈ a.hom ⁻¹ᵁ U →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
            Q).val.presheaf x)) := by
      intro n x hx
      apply hsQ n x
      simpa only [not_forall] using (hZ x).not.mp (not_not.mpr hx)
    intro n x hx
    apply hsF Q hsQ' n x
    change x ∈ (U : Set X)
    rwa [hU]
  · intro K horth
    apply (hunit K.obj).mp
    apply (koszul_open_orthogonality X U A a.hom hcover hqc r f hZ RS adjS
      (F.inverse.obj K.obj) (hqI K.obj K.property)).mpr
    intro n
    let eHom := (Iso.homCongr ((F.functor.commShiftIso n).app Q).symm
      (Iso.refl K.obj)).trans (F.toAdjunction.homEquiv (Q⟦n⟧) K.obj)
    exact eHom.subsingleton_congr.mp (horth n)

end AlgebraicGeometry
