/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldLocalSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses

/-!
# Flatness over the constant field sheaf

Source: Stacks Project, Modules on Sites, Tags 03ER and 08FC; Fields, Tag 09FN.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

/-- Every module sheaf over a constant field sheaf is flat.
Source: Stacks Project, Tags 03ER, 08FC and 09FN
(auxiliary; not a blueprint node).
Proof: intersect the finitely many covering image sieves of the coefficients of a relation.
On each arrow of this covering sieve the coefficients lift to field elements. Restrict the
module action along the field-to-sections ring map. This gives a vector space, hence a flat
module. Its finite relation factors through finitely many vectors with zero coefficient
relations. Map the factorization coefficients back to the ring sheaf; the ring-map identities
give the same factorization there. The independent-universe local relation criterion proves
sheaf flatness, including on objects with an empty covering sieve. -/
theorem isFlat_constantFieldModule
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
    (κ : Type r) [Field κ]
    (N : ringedSiteModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)))) :
    IsFlatOnSite N := by
  classical
  let R := (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of κ)
  apply isFlatOnSite_of_local_equationalCriterion R N
  intro U n a s hs
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of κ))
  have hη : Presheaf.IsLocallySurjective J η := constantFieldUnit_locallySurjective J κ
  let S : J.Cover U := Finset.univ.inf fun p : Fin n ↦
    ⟨Presheaf.imageSieve η (a p), Presheaf.imageSieve_mem J η (a p)⟩
  refine ⟨S.val, S.property, ?_⟩
  intro V f hf
  have hlift (p : Fin n) : ∃ c : κ, (η.app (Opposite.op V)) c =
      R.obj.map f.op (a p) := by
    have hp : S ≤ (⟨Presheaf.imageSieve η (a p),
        Presheaf.imageSieve_mem J η (a p)⟩ : J.Cover U) :=
      Finset.inf_le (Finset.mem_univ p)
    exact hp f hf
  choose c hc using hlift
  let ρ : κ →+* R.obj.obj (Opposite.op V) := (η.app (Opposite.op V)).hom
  let : Module κ (N.val.obj (Opposite.op V)) := Module.compHom _ ρ
  have heq : (∑ p : Fin n, c p •
      (show N.val.obj (Opposite.op V) from N.val.map f.op (s p))) = 0 := by
    change (∑ p : Fin n, ρ (c p) • N.val.restrictₛₗ f.op (s p)) = 0
    simp_rw [show ∀ p, ρ (c p) = R.obj.map f.op (a p) from hc]
    have hh := congrArg (fun z ↦ (show N.val.obj (Opposite.op V) from
      N.val.map f.op z)) hs
    rw [map_sum, map_zero] at hh
    have hh' : (∑ p : Fin n, (show N.val.obj (Opposite.op V) from
        N.val.map f.op (a p • s p))) = 0 := hh
    calc
      _ = ∑ p : Fin n, (show N.val.obj (Opposite.op V) from
          N.val.map f.op (a p • s p)) := by
        apply Finset.sum_congr rfl
        intro p _
        exact (N.val.map_smul f.op (a p) (s p)).symm
      _ = 0 := hh'
  have : Module.Flat κ (N.val.obj (Opposite.op V)) := inferInstance
  obtain ⟨l, b, t, hb, hbt⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero heq
  refine ⟨l, fun p q ↦ ρ (b p q), t, hb, ?_⟩
  intro q
  simp_rw [← hc]
  change (∑ p : Fin n, ρ (c p) * ρ (b p q)) = 0
  simpa only [map_sum, map_mul, map_zero] using congrArg ρ (hbt q)

end SheafOfModules
