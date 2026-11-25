/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.AffineQuotientRestrictedIso
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Finite free sheafification of an augmented Koszul complex

Source: Stacks Project, Tags 068C and 0BQZ, affine Koszul resolution.
(blueprint: lem-sc-affine-koszul-finite-free-resolution). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_presentation {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (U : Y.affineOpens) :
    ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)),
    i ∣_ U.1 ≫ U.1.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (i.ker.ideal U))) := by
  let g := i ∣_ U.1 ≫ U.2.isoSpec.hom
  let φ := (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫ g.appTop
  have hφ : φ = i.app U.1 ≫ (i ⁻¹ᵁ U.1).topIso.inv := by
    change (Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (i ∣_ U.1 ≫ U.2.isoSpec.hom).appTop = _
    rw [Scheme.Hom.comp_appTop, U.2.isoSpec_hom_appTop]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Scheme.Hom.appLE_eq_app]
  have hker : RingHom.ker φ.hom = i.ker.ideal U := by
    rw [hφ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).1,
      Scheme.Hom.ker_apply]
  have hsurj : Function.Surjective φ := by
    rw [hφ]
    exact (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U.1).topIso.inv).2.comp
      (i.app_surjective U.1 U.2)
  have : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  let er := RingEquiv.ofBijective φ.hom.kerLift
    ⟨φ.hom.kerLift_injective, Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj⟩
  let e := Scheme.isoSpec (i ⁻¹ᵁ U.1).toScheme ≪≫ Scheme.Spec.mapIso
    er.toCommRingCatIso.op
  have he : g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (RingHom.ker φ.hom))) := by
    dsimp [e, er]
    simp only [Iso.op_hom,
      Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp]
    change g = (i ⁻¹ᵁ U.1).toScheme.isoSpec.hom ≫ Spec.map φ
    simp only [Scheme.isoSpec, asIso_hom, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, φ]
    simp
  have hex : ∃ e : (i ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of ((Γ(Y, U.1) : Type u) ⧸ RingHom.ker φ.hom)),
      g = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) :=
    ⟨e, he⟩
  rw [hker] at hex
  exact hex

/-- Sheafification of an already augmented algebraic Koszul resolution is a
bounded-above finite free resolution of the restricted closed pushforward.

Source: Stacks Project, Tag 068C, affine quotient resolution, and Tag 0BQZ.
(blueprint: lem-sc-affine-koszul-finite-free-resolution).

Proof: The closed immersion identifies its inverse image over U with Spec(A/I),
where A = Gamma(Y,U) and I = i.ker.ideal U. On basic opens the quotient modules
and the restricted pushforward both have sections (A/I)[1/g], compatibly with
restrictions. This identifies their module sheaves. Tilde is exact because its
stalks are localizations; chart restriction is exact because it is an equivalence.
Map the supplied integer-indexed augmentation by their composite and the single
complex comparison, then the single complex of the quotient identification.
This gives the augmentation in the conclusion and preserves its quasi-isomorphism.
There are no positive cochain terms: extension sends chain degree k to -k.
In degree -k, the wedge basis indexed by k-element subsets of Fin n identifies
its associated sheaf with the finite free sheaf on that finite set, enumerated
by Fin r and lifted to universe u. Terms outside the extension image are zero,
which is the free sheaf of rank zero. This also covers n=0, zero rings and empty U.
No regularity is assumed here: it is supplied by the given quasi-isomorphism. -/
theorem affine_koszul_finite_free_resolution
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1))
    (ε : (ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f).extend
        ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat (Γ(Y, U.1) : Type u)) 0).obj
        (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))) [QuasiIso ε] :
    let E := ((tilde.functor Γ(Y, U.1) ⋙
      Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((ExteriorAlgebra.koszulComplex (Γ(Y, U.1) : Type u) n f).extend
            ComplexShape.embeddingDownNat)
    (∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p)) ∧
    (∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.1.toScheme.toRingedSpace)
        (ULift.{u} (Fin r)))) ∧
    ∃ a : E ⟶ (CochainComplex.singleFunctor U.1.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.1.ι).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
      QuasiIso a := by
  classical
  let A := (Γ(Y, U.1) : Type u)
  let L := ExteriorAlgebra.koszulComplex A n f
  let T := tilde.functor Γ(Y, U.1)
  let R := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let : R.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction U.2.isoSpec.hom).isLeftAdjoint
  let F := T ⋙ R
  let E := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (L.extend ComplexShape.embeddingDownNat)
  have hpos (p : ℤ) (hp : 0 < p) : IsZero (E.X p) := by
    apply F.map_isZero
    apply L.isZero_extend_X
    intro k
    change -(k : ℤ) ≠ p
    omega
  refine ⟨⟨0, hpos⟩, ?_, ?_⟩
  · intro p
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hp
      let J := Set.powersetCard (Fin n) k
      let b := (Finsupp.basisSingleOne : Module.Basis (Fin n) A
        (Fin n →₀ A)).exteriorPower k
      let v : J ≃ ULift.{u} (Fin (Fintype.card J)) :=
        (Fintype.equivFin J).trans Equiv.ulift.symm
      let c := (b.reindex v).repr.toModuleIso
      let t := T.mapIso c ≪≫ tildeFinsupp (ULift.{u} (Fin (Fintype.card J)))
      let r := (SheafOfModules.mapFreeIso R (ULift.{u} (Fin (Fintype.card J)))
        (Scheme.Modules.restrictUnitIso U.2.isoSpec.hom).symm).symm
      exact ⟨Fintype.card J, ⟨F.mapIso
        (L.extendXIso ComplexShape.embeddingDownNat rfl) ≪≫ R.mapIso t ≪≫ r⟩⟩
    · have hz : IsZero (SheafOfModules.free
          (R := moduleRings U.1.toScheme.toRingedSpace) (ULift.{u} (Fin 0))) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply Sigma.hom_ext
        intro j
        exact Fin.elim0 j.down
      exact ⟨0, ⟨(hpos p (by omega)).iso hz⟩⟩
  · obtain ⟨e, he⟩ := quotient_presentation i U
    obtain ⟨c⟩ := affine_quotient_restricted_iso i U.1 U.2 (i.ker.ideal U) e he
    let : PreservesFiniteLimits T := tilde_preserves_finite_limits A
    let : PreservesFiniteLimits R := by dsimp [R]; infer_instance
    let : PreservesFiniteColimits R := by dsimp [R]; infer_instance
    let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
    let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
    let a := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app
        (ModuleCat.of A (A ⧸ i.ker.ideal U)) ≫
      (CochainComplex.singleFunctor U.1.toScheme.Modules 0).map c.hom
    exact ⟨a, by dsimp [a]; infer_instance⟩

end AlgebraicGeometry
