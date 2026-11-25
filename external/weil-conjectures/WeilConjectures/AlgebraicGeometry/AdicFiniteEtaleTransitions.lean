/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicComparisonComposition
import WeilConjectures.AlgebraicGeometry.AdicExactComparison
import WeilConjectures.AlgebraicGeometry.AdicReductionCocycle
import WeilConjectures.AlgebraicGeometry.AdicScalarExtensionBound
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent

/-! # AdicFiniteEtaleTransitions
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

private theorem liftIsoOnProperty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (P : C → Prop)
    (hF : ∀ K L, P K → P L →
      Function.Bijective (F.map : (K ⟶ L) → (F.obj K ⟶ F.obj L)))
    (K L : C) (hK : P K) (hL : P L) (e : F.obj K ≅ F.obj L) :
    ∃ t : K ≅ L, F.map t.hom = e.hom := by
  obtain ⟨f, hf⟩ := (hF K L hK hL).surjective e.hom
  obtain ⟨g, hg⟩ := (hF L K hL hK).surjective e.inv
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (hF K K hK hK).injective
    rw [F.map_comp, hf, hg, e.hom_inv_id, F.map_id]
  · apply (hF L L hL hL).injective
    rw [F.map_comp, hf, hg, e.inv_hom_id, F.map_id]

private theorem adicBounded_of_iso
    {C : Type*} [SmallCategory C] {T : GrothendieckTopology C}
    {R : Sheaf T CommRingCat} {K L : ConstantCompletion.D R} (e : K ≅ L)
    (hL : AlgebraicGeometry.ProEtale.coefficientCohomologyBounded R L) :
    AlgebraicGeometry.ProEtale.coefficientCohomologyBounded R K := by
  obtain ⟨a, b, hab, h⟩ := hL
  exact ⟨a, b, hab, fun q hq ↦ (h q hq).of_iso
    ((coefficientModelCohomology R q).mapIso e)⟩

/-- Arbitrarily marked bounded constructible finite-Tor etale origins inherit
all normalized quotient isomorphisms and their cocycle.
Source: Stacks Project, proetale.tex, Tag 09AL, full faithfulness, applied to
the quotient balancing in Tag 09C2; parent proof steps 8-10.
(auxiliary; not a blueprint node).

Proof: For n <= m, scalar extension of Cn at m to A/J^(n+1) has the same
Tor interval: on a flat-term K-flat representative the double tensor test
balances to the original tensor test. It is bounded by testing against the
unit. Refine the finite stratifications of its source cohomology on each
affine open. On each stratum, bounded-above locally constant tensor preserves
finite-type cohomology. The quotient scalar action makes the resulting local
models modules of finite type over A/J^(n+1), so the extended complex is
constructible. The comparison functor is fully faithful on these bounded
constructible objects. Lift the isomorphism given by the inverse coefficient
comparison followed by scalar extension of alpha m, then rho, then inverse
alpha n. Lift its inverse as well; faithfulness proves that the lifts are
mutual inverses, yielding beta and the compatibility equation. For a triple
r >= m >= n apply comparison and postcompose with alpha n. Substitute the
compatibility equations, use naturality of the scalar comparison and cancel
alpha m with its inverse. Both composites are the same triple balanced tensor
map. On pure tensors they multiply the three scalar factors in the same
order; the ordinary normalizations and uniqueness on K-flat representatives
identify them with the specified adicFiniteExtensionComp and adicFiniteRho.
Faithfulness gives the cocycle. Repeated indices use scalar multiplication by
one, so identity reductions are included. No normalization of alpha 0 is
required, and no completeness assumption is used. -/
theorem adicFiniteEtale_transitions
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (a b : ℤ)
    (Cn : ∀ n : ℕ, adicFiniteEtale.{u, v} X J n)
    (hCn : ∀ n : ℕ, IsCoefficientBoundedConstructibleEtale.{u, v} X
      (adicFiniteCoeff J n) (Cn n))
    (hTor : ∀ n : ℕ, HasCoefficientModelTorAmplitude
      (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n)) (Cn n) a b)
    (alpha : ∀ n : ℕ, (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).obj (Cn n) ≅
      adicFiniteReduction.{u, v} X J N n) :
    ∃ beta : ∀ {m n : ℕ} (h : n ≤ m),
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J h)).obj (Cn m) ≅ Cn n,
    (∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
        (adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
          (adicFiniteFactor J (hnm.trans hmr)) (adicFiniteFactorComp J hnm hmr)).hom.app
            (Cn r) ≫ (beta (hnm.trans hmr)).hom =
        (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X)
          (adicFiniteFactor J hnm)).map (beta hmr).hom ≫ (beta hnm).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (adicFinitePullback.{u, v} X (adicFiniteCoeff J n)).map (beta h).hom ≫ (alpha n).hom =
        (adicFiniteComparison.{u, v} X (adicFiniteFactor J h)).inv.app (Cn m) ≫
          (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
            (adicFiniteFactor J h)).map (alpha m).hom ≫ (adicFiniteRho.{u, v} X J N h).hom) := by
  classical
  -- Bounded classical comparison suffices; no constructibility of the extensions is needed.
  let F (n : ℕ) := adicFinitePullback.{u, v} X (adicFiniteCoeff J n)
  let E {m n : ℕ} (h : n ≤ m) :=
    adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteFactor J h)
  let G {m n : ℕ} (h : n ≤ m) :=
    adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteFactor J h)
  let B (n : ℕ) := AlgebraicGeometry.ProEtale.coefficientCohomologyBounded
    (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J n))
  have hff (n : ℕ) (K L) (hK : B n K) (hL : B n L) :
      Function.Bijective ((F n).map : (K ⟶ L) → _) :=
    (AlgebraicGeometry.ProEtale.coefficientComparison_boundedClassical X
      (adicFiniteCoeff J n) (F n) (adicExactComparison X (adicFiniteCoeff J n))).1
      K L hK hL
  have hb (n : ℕ) : B n (Cn n) := (hCn n).2
  have he {m n : ℕ} (h : n ≤ m) : B n ((E h).obj (Cn m)) :=
    ⟨a, b, (hTor m).1, adicScalarExtension_bound
      (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteFactor J h)
      (Cn m) a b (hTor m)⟩
  have lift {m n : ℕ} (h : n ≤ m) : ∃ t : (E h).obj (Cn m) ≅ Cn n,
      (F n).map t.hom ≫ (alpha n).hom =
        (adicFiniteComparison.{u, v} X (adicFiniteFactor J h)).inv.app (Cn m) ≫
          (G h).map (alpha m).hom ≫ (adicFiniteRho.{u, v} X J N h).hom := by
    let e : (F n).obj ((E h).obj (Cn m)) ≅ (F n).obj (Cn n) :=
      (adicFiniteComparison.{u, v} X (adicFiniteFactor J h)).symm.app (Cn m) ≪≫
        (G h).mapIso (alpha m) ≪≫ adicFiniteRho.{u, v} X J N h ≪≫ (alpha n).symm
    obtain ⟨t, ht⟩ := liftIsoOnProperty (F n) (B n) (hff n)
      ((E h).obj (Cn m)) (Cn n) (he h) (hb n) e
    refine ⟨t, ?_⟩
    rw [ht]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.app_hom]
  choose beta hbeta using @lift
  refine ⟨@beta, ?_, fun m n h ↦ hbeta h⟩
  intro r m n hnm hmr
  have hd : B n ((E hnm).obj ((E hmr).obj (Cn r))) :=
    adicBounded_of_iso ((E hnm).mapIso (beta hmr)) (he hnm)
  apply (hff n _ _ hd (hb n)).injective
  apply (cancel_mono (alpha n).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hbeta (hnm.trans hmr)]
  rw [← Category.assoc, adicComparison_composition X
    (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
    (adicFiniteFactor J (hnm.trans hmr)) (adicFiniteFactorComp J hnm hmr) (Cn r)]
  simp only [Category.assoc]
  rw [← (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
    (adicFiniteFactor J (hnm.trans hmr))
    (adicFiniteFactorComp J hnm hmr)).hom.naturality_assoc (alpha r).hom]
  rw [← adicReduction_cocycle X J N r m n hnm hmr]
  change _ = (F n).map ((E hnm).map (beta hmr).hom) ≫
    (F n).map (beta hnm).hom ≫ (alpha n).hom
  rw [hbeta hnm]
  have hn : (F n).map ((E hnm).map (beta hmr).hom) ≫
        (adicFiniteComparison.{u, v} X (adicFiniteFactor J hnm)).inv.app (Cn m) =
      (adicFiniteComparison.{u, v} X (adicFiniteFactor J hnm)).inv.app
          ((E hmr).obj (Cn r)) ≫ (G hnm).map ((F m).map (beta hmr).hom) :=
    (adicFiniteComparison.{u, v} X (adicFiniteFactor J hnm)).inv.naturality
      (beta hmr).hom
  rw [reassoc_of% hn]
  conv_rhs => rw [← (G hnm).map_comp_assoc, hbeta hmr]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
