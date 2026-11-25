/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Module sheaves on discrete schemes over an algebraically closed field

Source: Stacks Project, Tags 06LH, 04DZ and 03P5; step 4 of the parent node.
(blueprint: lem-weil-pbc-discrete-scheme-module-locally-constant)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem isConstant_module_spec
    (Λ : Type (u + 1)) [CommRing Λ] (K : Type u) [Field K] [IsAlgClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F.IsConstant (Spec (.of K)).smallEtaleTopology := by
  let J := (Spec (.of K)).smallEtaleTopology
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  have : IsIso ((constantSheafAdj J (Type (u + 1))
      CategoryTheory.Limits.terminalIsTerminal).counit.app ((sheafCompose J U).obj F)) :=
    (spec_algClosed_etale_sheaf_constant K ((sheafCompose J U).obj F)).1
  have h : IsIso ((sheafCompose J U).map
      ((constantSheafAdj J (ModuleCat.{u + 1} Λ)
        CategoryTheory.Limits.terminalIsTerminal).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  have : IsIso ((constantSheafAdj J (ModuleCat.{u + 1} Λ)
      CategoryTheory.Limits.terminalIsTerminal).counit.app F) :=
    isIso_of_reflects_iso _ (sheafCompose J U)
  exact F.isConstant_of_isIso_counit_app J

/-- Every module sheaf on a discrete scheme locally of finite type over an algebraically
closed field is locally constant. No finiteness condition is imposed on the module.
Source: Stacks Project, Tags 06LH, 04DZ and 03P5.
(blueprint: lem-weil-pbc-discrete-scheme-module-locally-constant)

Proof: Cover Z by its singleton open subschemes T. At the unique point t of T the
residue-field map Spec kappa(t) -> T is a closed immersion and is surjective, hence is a
universal homeomorphism. The Nullstellensatz identifies kappa(t) with k, since T is locally
of finite type over k and t is closed. Every set sheaf on Spec kappa(t) has an invertible
constant-sheaf counit. The constant-sheaf counit for a module sheaf becomes that counit
under the forgetful functor, up to the constant-sheaf comparison isomorphism. Forgetting
module structure reflects isomorphisms, so the module counit is invertible too and the
module sheaf is constant. Its pullback along the residue-field map is therefore locally
constant. Universal-homeomorphism invariance descends this to T. Finally local constancy
is etale local, so the singleton open cover gives local constancy on Z. The empty scheme
uses the empty cover. Infinite discrete schemes are allowed because the cover need not
be finite; no finite generation or Noetherian coefficient hypothesis is used. -/
theorem isLocallyConstantSheaf_of_discrete_finiteType_module
    (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {Z : Scheme.{u}} [DiscreteTopology Z]
    (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsLocallyConstantSheaf F := by
  classical
  let O : Z → Z.Opens := fun z ↦ ⟨{z}, isOpen_discrete _⟩
  let C : Scheme.Cover Scheme.etalePrecoverage Z :=
    { I₀ := Z
      X := fun z ↦ (O z).toScheme
      f := fun z ↦ (O z).ι
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨?_, fun z ↦ inferInstance⟩
        intro z
        exact ⟨z, ⟨z, rfl⟩, rfl⟩ }
  have hlocal (z : Z) : IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (C.f z)).obj F) := by
    let T := (O z).toScheme
    let t : T := ⟨z, rfl⟩
    let : Subsingleton T := ⟨fun a b ↦ Subtype.ext
      ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
    let q := T.fromSpecResidueField t
    have ht : IsClosed ({t} : Set T) := isClosed_discrete _
    let : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp ht
    let : Surjective q := ⟨fun a ↦ by
      obtain ⟨b, hb⟩ := (T.range_fromSpecResidueField t).symm ▸
        (show t ∈ ({t} : Set T) from rfl)
      exact ⟨b, hb.trans (Subsingleton.elim t a)⟩⟩
    let : IsAlgClosed (T.residueField t) := IsAlgClosed.of_ringEquiv k _
      (Iso.commRingCatIsoToRingEquiv (residueFieldIsoBase ((O z).ι ≫ p) t ht)).symm
    let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (C.f z)).obj F
    have hconstant := isConstant_module_spec Λ (T.residueField t)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G)
    have : IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G) :=
      hconstant.isLocallyConstantSheaf
    exact IsLocallyConstantSheaf.of_upperStar q G
  exact IsLocallyConstantSheaf.of_cover C F

end AlgebraicGeometry.Scheme
