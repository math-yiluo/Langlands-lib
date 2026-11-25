/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import Mathlib.Algebra.Exact.Basic

import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisPullback
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Identify cohomology on the fibre-product scheme with cohomology on the inverse-image
open, using inverse-image composition and forgetting module structure. -/
private theorem module_open_pullback_cohomology_equiv
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (T : X.Opens) (q : ℕ) :
    Nonempty (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst T.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((T.ι)^*[ModuleCat.{u + 1} Λ].obj J))) q ≃+
      Sheaf.H (((i ⁻¹ᵁ T).ι)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj J))) q) := by
  let e : pullback T.ι i ≅ (i ⁻¹ᵁ T).toScheme :=
    pullbackSymmetry T.ι i ≪≫ pullbackRestrictIsoRestrict i T
  let K := (pullback.fst T.ι i)^*[ModuleCat.{u + 1} Λ].obj
    ((T.ι)^*[ModuleCat.{u + 1} Λ].obj J)
  let A := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj K
  have hc : (i ⁻¹ᵁ T).ι ≫ i = (e.inv ≫ pullback.fst T.ι i) ≫ T.ι := by
    simp only [e, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_fst]
    exact (morphismRestrict_ι i T).symm
  let em := ((upperStarComp (ModuleCat.{u + 1} Λ) e.inv
      (pullback.fst T.ι i)).symm.app ((T.ι)^*[ModuleCat.{u + 1} Λ].obj J)) ≪≫
    ((upperStarComp (ModuleCat.{u + 1} Λ) (e.inv ≫ pullback.fst T.ι i)
      T.ι ((i ⁻¹ᵁ T).ι ≫ i) hc).symm.app J) ≪≫
    ((upperStarComp (ModuleCat.{u + 1} Λ) (i ⁻¹ᵁ T).ι i).app J)
  let ef := (sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso em
  obtain ⟨ea⟩ := pullback_forget_modules_iso Λ e.inv K
  obtain ⟨eb⟩ := pullback_forget_modules_iso Λ (i ⁻¹ᵁ T).ι
    ((i)^*[ModuleCat.{u + 1} Λ].obj J)
  let eh := (Sheaf.functorH _ q).mapIso (ea.symm ≪≫ ef ≪≫ eb)
  exact ⟨(cohomologyEquiv e.inv A q).trans eh.addCommGroupIsoToAddEquiv⟩

/-- An exact Mayer--Vietoris segment for the underlying abelian groups of
module-sheaf pullbacks. There are no vanishing hypotheses.
Source: Stacks Project, Tag 0A50; module inverse image, Tags 03D3 and 03D7.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-module-exact-segment)

Proof: Let F be the underlying abelian sheaf of i^*J on Z. Pull U and V back
as opens of Z. Their union is Z since inverse image preserves unions and top;
their intersection is the inverse image of U ∩ V. The base changes of the
three open immersions are open immersions isomorphic to these inverse-image
opens. For each T = U, V, U ∩ V, the equality of the two composites in the
pullback square and the inverse-image composition isomorphisms identify
pr_1^*(T.ι^*J) with pr_2^*(i^*J). Forgetting modules commutes with inverse
image, so this identifies the underlying abelian sheaf with F restricted to
the corresponding inverse-image open, transported across its scheme
isomorphism. The induced additive cohomology isomorphisms identify all four
displayed groups with the groups of the two-open Mayer--Vietoris sequence of
F on Z. Tag 0A50 constructs this sequence by applying sections to an injective
resolution: in every degree the sheaf condition gives exactness on the left
and in the middle, and injectivity gives surjectivity onto intersection
sections. The resulting short exact sequence of complexes gives an exact
cohomology segment in degrees r and r + 1. Equivalently use etale_mayerVietoris
and nonempty_sheafH_extDerivedIso to express this segment in Sheaf.H. Transport
its connecting and restriction homomorphisms through the four additive
isomorphisms. Isomorphisms preserve images and kernels, hence the transported
maps δ and ρ are exact. This construction also works for r = 0 and for empty
or repeated cover members. -/
theorem Etale.exists_module_mayer_vietoris_exact_segment
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (r : ℕ) :
    ∃ δ : (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst (U ⊓ V).ι i)^*[ModuleCat.{u + 1} Λ].obj
          (((U ⊓ V).ι)^*[ModuleCat.{u + 1} Λ].obj J))) r) →+ (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) (r + 1)),
      ∃ ρ : (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) (r + 1)) →+ ((Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst U.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((U.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1)) × (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((pullback.fst V.ι i)^*[ModuleCat.{u + 1} Λ].obj
          ((V.ι)^*[ModuleCat.{u + 1} Λ].obj J))) (r + 1))),
        Function.Exact δ ρ := by
  classical
  let F := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
    ((i)^*[ModuleCat.{u + 1} Λ].obj J)
  have hc : (i ⁻¹ᵁ U) ⊔ (i ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  obtain ⟨a, b, c, d, e, f, g, h, j, k, l, δ, ε, hseq⟩ :=
    etale_mayerVietoris_pullback (𝟙 Z) (i ⁻¹ᵁ U) (i ⁻¹ᵁ V) hc F
  have hex := hseq.2.2.2.2.2.2.2.2.2.2.2.2.1 r
  obtain ⟨eI⟩ := module_open_pullback_cohomology_equiv Λ i J (U ⊓ V) r
  obtain ⟨eU⟩ := module_open_pullback_cohomology_equiv Λ i J U (r + 1)
  obtain ⟨eV⟩ := module_open_pullback_cohomology_equiv Λ i J V (r + 1)
  refine ⟨(δ r).comp eI.toAddMonoidHom,
    ((eU.symm.toAddMonoidHom.comp (a (r + 1))).prod
      (eV.symm.toAddMonoidHom.comp (b (r + 1)))), ?_⟩
  intro x
  constructor
  · intro hx
    have hz : (a (r + 1) x, b (r + 1) x) = 0 := by
      change (eU.symm (a (r + 1) x), eV.symm (b (r + 1) x)) = (0, 0) at hx
      apply Prod.ext
      · apply eU.symm.injective
        exact (congrArg Prod.fst hx).trans (map_zero eU.symm).symm
      · apply eV.symm.injective
        exact (congrArg Prod.snd hx).trans (map_zero eV.symm).symm
    obtain ⟨y, hy⟩ := (hex.2.2 x).mp hz
    refine ⟨eI.symm y, ?_⟩
    change δ r (eI (eI.symm y)) = x
    rw [eI.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    have hz := (hex.2.2).apply_apply_eq_zero (eI y)
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.comp_apply]
    change (eU.symm (a (r + 1) (δ r (eI y))),
      eV.symm (b (r + 1) (δ r (eI y)))) = 0
    simp only [Prod.mk_eq_zero] at hz ⊢
    exact ⟨by rw [hz.1, map_zero], by rw [hz.2, map_zero]⟩

end AlgebraicGeometry
