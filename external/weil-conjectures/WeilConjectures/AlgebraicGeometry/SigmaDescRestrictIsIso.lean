/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-! # Transferring an isomorphism through a component coproduct -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private noncomputable def sigmaRestrictInclusion
    (X : Scheme.{u}) (n : ℕ) (C : Fin n → Scheme.{u})
    (ι : ∀ i, C i ⟶ X) (U : X.Opens) (i : Fin n) :
    (ι i ⁻¹ᵁ U).toScheme ⟶ (Limits.Sigma.desc ι ⁻¹ᵁ U).toScheme :=
  (Limits.Sigma.ι C i).resLE _ _ (by
    rw [← Scheme.Hom.comp_preimage, Limits.Sigma.ι_comp_desc])

private theorem isIso_sigmaRestrictInclusion
    (X : Scheme.{u}) (n : ℕ) (C : Fin n → Scheme.{u})
    (ι : ∀ i, C i ⟶ X) (U : X.Opens) :
    IsIso (Limits.Sigma.desc (sigmaRestrictInclusion X n C ι U)) := by
  let a := sigmaRestrictInclusion X n C ι U
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts (Limits.coproductIsCoproduct C)
  have hc : Nonempty (Limits.IsColimit (Limits.Cofan.mk _ a)) := by
    apply hau (Limits.Cofan.mk _ a)
      (Discrete.natTrans fun i ↦ (ι i.as ⁻¹ᵁ U).ι) (Limits.Sigma.desc ι ⁻¹ᵁ U).ι
    · ext i
      simp [a, sigmaRestrictInclusion]
    · exact NatTrans.Equifibered.of_discrete _
    · intro i
      change IsPullback (a i.as) (ι i.as ⁻¹ᵁ U).ι
        (Limits.Sigma.desc ι ⁻¹ᵁ U).ι (Limits.Sigma.ι C i.as)
      apply IsOpenImmersion.isPullback
      · simp [a, sigmaRestrictInclusion]
      · simp [← Scheme.Hom.comp_preimage]
  exact (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc

/-- If a coproduct map is an isomorphism over U and each summand modification is
an isomorphism over the corresponding inverse image, their composite coproduct
map is an isomorphism over U.
Source: the coproduct and restriction gluing in
`theorem-cohomology-curves`, step 3 (Stacks Project,
Morphisms, Tag 0BAJ, componentwise reduction).

Proof: Write p = Sigma.desc ι and q = Sigma.map ν. The composite q ≫ p is
Sigma.desc (fun i ↦ ν i ≫ ι i) by the coproduct universal property.
Base change along the open U identifies p's restricted source with the coproduct
of C i restricted to ι i's inverse image of U. Under this identification the
restriction of q is the coproduct of the restrictions of ν i. Each is an
isomorphism by hypothesis, so their coproduct is an isomorphism. Compose with
the given isomorphism p restricted to U, using morphismRestrict_comp.
This works for an empty family as well, since the coproduct of an empty family
of isomorphisms is the identity of an initial object.
(blueprint: lem-weil-pbc-sigma-desc-restrict-iso) -/
theorem isIso_sigmaDesc_comp_restrict
    (X : Scheme.{u}) (n : ℕ) (C Y : Fin n → Scheme.{u})
    (ι : ∀ i, C i ⟶ X) (ν : ∀ i, Y i ⟶ C i) (U : X.Opens)
    (hι : IsIso (CategoryTheory.Limits.Sigma.desc ι ∣_ U))
    (hν : ∀ i, IsIso (ν i ∣_ ι i ⁻¹ᵁ U)) :
    IsIso (CategoryTheory.Limits.Sigma.desc (fun i ↦ ν i ≫ ι i) ∣_ U) := by
  let a := sigmaRestrictInclusion X n C ι U
  let f := Limits.Sigma.desc (fun i ↦ ν i ≫ ι i)
  let b := sigmaRestrictInclusion X n Y (fun i ↦ ν i ≫ ι i) U
  let := hι
  let := hν
  let : IsIso (Limits.Sigma.desc a) := isIso_sigmaRestrictInclusion X n C ι U
  let : IsIso (Limits.Sigma.desc b) :=
    isIso_sigmaRestrictInclusion X n Y (fun i ↦ ν i ≫ ι i) U
  have heq : Limits.Sigma.desc b ≫ f ∣_ U =
      Limits.Sigma.map (fun i ↦ ν i ∣_ ι i ⁻¹ᵁ U) ≫
        Limits.Sigma.desc a ≫ Limits.Sigma.desc ι ∣_ U := by
    apply Limits.Sigma.hom_ext
    intro i
    apply (cancel_mono U.ι).mp
    simp [a, b, f, sigmaRestrictInclusion, Category.assoc]
  have : IsIso (Limits.Sigma.desc b ≫ f ∣_ U) := by
    rw [heq]
    infer_instance
  exact (isIso_comp_left_iff (Limits.Sigma.desc b) (f ∣_ U)).mp inferInstance

end AlgebraicGeometry
