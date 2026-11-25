/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Limits

/-! # Sections of covers of finite algebras over a strictly henselian ring

## References

* Stacks Project, Tags 04GH, 04GK and 0EYG
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A surjective étale morphism to a finite algebra over a strictly henselian local
ring admits a section. -/
theorem finite_strict_henselian_algebra_etale_section
    (H A : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [CommRing A] [Algebra H A] [Module.Finite H A]
    {E : Scheme.{u}} (p : E ⟶ Spec (.of A)) [Etale p]
    (hp : Function.Surjective p) :
    ∃ σ : Spec (.of A) ⟶ E, σ ≫ p = 𝟙 _ := by
  classical
  obtain ⟨n, B, rings, algebras, henselian, localMaps, ⟨e⟩, hfin, hres⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi H A
  let := rings
  let := algebras
  let := henselian
  let := localMaps
  let := hfin
  let := hres
  have hstrict (j : Fin n) : IsStrictlyHenselianLocalRing (B j) := by
    have : IsSepClosed (IsLocalRing.ResidueField (B j)) :=
      Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField H)
    exact ⟨inferInstance⟩
  let C (j : ULift.{u} (Fin n)) := B j.down
  let e' := e.trans (AlgEquiv.piCongrLeft' H B Equiv.ulift.symm)
  let iso : Spec (.of (∀ j, C j)) ≅ Spec (.of A) :=
    Scheme.Spec.mapIso e'.toRingEquiv.toCommRingCatIso.op
  let t (j : ULift.{u} (Fin n)) : Spec (.of (C j)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C j)) ≫ iso.hom
  let : Surjective p := ⟨hp⟩
  have hsect (j : ULift.{u} (Fin n)) : ∃ s : Spec (.of (C j)) ⟶ E, s ≫ p = t j := by
    let := hstrict j.down
    let pj := pullback.snd p (t j)
    obtain ⟨y, hy⟩ := pj.surjective (IsLocalRing.closedPoint (C j))
    obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing pj y hy
    refine ⟨σ ≫ pullback.fst p (t j), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ,
      Category.id_comp]
  choose s hs using hsect
  let d := sigmaSpec (fun j ↦ CommRingCat.of (C j)) ≫ iso.hom
  have : IsIso (sigmaSpec (fun j ↦ CommRingCat.of (C j))) := by
    infer_instance
  have : IsIso d := (asIso (sigmaSpec (fun j ↦ CommRingCat.of (C j))) ≪≫ iso).isIso_hom
  refine ⟨inv d ≫ Sigma.desc s, ?_⟩
  have heq : Sigma.desc s ≫ p = d := by
    apply Sigma.hom_ext
    intro j
    change Sigma.ι (fun j ↦ Spec (.of (C j))) j ≫ Sigma.desc s ≫ p =
      Sigma.ι (fun j ↦ Spec (.of (C j))) j ≫
        sigmaSpec (fun j ↦ CommRingCat.of (C j)) ≫ iso.hom
    rw [← Category.assoc, Sigma.ι_comp_desc, ← Category.assoc, ι_sigmaSpec]
    exact hs j
  rw [Category.assoc, heq, IsIso.inv_hom_id]

end AlgebraicGeometry.Scheme
