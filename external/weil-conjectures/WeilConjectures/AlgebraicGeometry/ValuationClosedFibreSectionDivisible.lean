/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ValuationClosedFibreSectionVanishing
import WeilConjectures.AlgebraicGeometry.PrincipalQuotientUnitKernel
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Dividing a section which vanishes on the closed fibre

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof.
(blueprint: new-valuation-closed-fibre-section-divisible)

Proof: If A is a field, its closed fibre inclusion is an isomorphism, so the unit
is an isomorphism and s = 0; choose pi = t = 0. Otherwise identify the quotient
fibre with the scheme-theoretic closed fibre. Uniqueness of adjoints compares the
units by isomorphisms, so they have the same kernel. Apply the closed-fibre
vanishing lemma to get a nonzero pi in the maximal ideal. The principal quotient
kernel theorem identifies multiplication by pi with the restriction kernel.
Represent s by O_X -> L, lift this morphism through the kernel, and evaluate the
lift at 1 to obtain t. Evaluating the kernel factorization gives pi t = s. The
integrality hypothesis is retained in the signature but is not used in this proof.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

private theorem pushforward_iso_equivalence {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (pushforward e.hom).IsEquivalence := by
  exact Functor.IsEquivalence.mk' (pushforward e.inv)
    ((pushforwardComp e.hom e.inv) ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId Y).symm
    ((pushforwardComp e.inv e.hom) ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Z)

private theorem section_comp_zero_iff {X : Scheme.{u}} (L N : X.Modules)
    (s : Γ(L, ⊤)) (a : L ⟶ N) :
    a.app ⊤ s = 0 ↔ homOfGlobalSection L s ≫ a = 0 := by
  constructor
  · intro hs
    ext U r
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app]
    rw [Hom.app_smul]
    have hn := ConcreteCategory.congr_hom
      (a.val.naturality (homOfLE (le_top : U ≤ ⊤)).op) s
    change a.app U (L.presheaf.map (homOfLE le_top).op s) =
      N.presheaf.map (homOfLE le_top).op (a.app ⊤ s) at hn
    rw [hn, hs, map_zero, smul_zero]
    rfl
  · intro hs
    have h := congrArg (fun b : unit X ⟶ N ↦ b.app ⊤ (1 : Γ(X, ⊤))) hs
    simpa [Hom.comp_app, homOfGlobalSection_app_one] using h

private theorem unit_section_zero_iso {X Y Z : Scheme.{u}}
    (i : Y ⟶ X) (j : Z ⟶ X) (e : Z ≅ Y) (he : e.hom ≫ i = j)
    (L : X.Modules) (s : Γ(L, ⊤)) :
    ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app L).app ⊤ s = 0 ↔
      ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app L).app ⊤ s = 0 := by
  classical
  let ai := Classical.choose (exists_tensorPullbackAdjunction i)
  let aj := Classical.choose (exists_tensorPullbackAdjunction j)
  let ae := Classical.choose (exists_tensorPullbackAdjunction e.hom)
  have := pushforward_iso_equivalence e
  let r := pushforwardComp e.hom i ≪≫ pushforwardCongr he
  let ac := (ai.comp ae).ofNatIsoRight r
  have h := aj.unit_leftAdjointUniq_hom_app ac L
  have hc : ac.unit.app L = ai.unit.app L ≫
      (pushforward i).map (ae.unit.app ((tensorPullback i).obj L)) ≫
      r.hom.app ((tensorPullback e.hom).obj ((tensorPullback i).obj L)) := by
    simp [ac, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app]
  rw [hc] at h
  rw [section_comp_zero_iff, section_comp_zero_iff]
  change homOfGlobalSection L s ≫ aj.unit.app L = 0 ↔
    homOfGlobalSection L s ≫ ai.unit.app L = 0
  have ht := congrArg (fun b ↦ homOfGlobalSection L s ≫ b) h
  let k := (pushforward j).map ((aj.leftAdjointUniq ac).hom.app L)
  let b := (pushforward i).map (ae.unit.app ((tensorPullback i).obj L)) ≫ r.hom.app _
  have ht' : (homOfGlobalSection L s ≫ aj.unit.app L) ≫ k =
      (homOfGlobalSection L s ≫ ai.unit.app L) ≫ b := by
    simpa only [Category.assoc] using ht
  constructor
  · intro hs
    apply (cancel_mono b).mp
    rw [zero_comp, ← ht', hs, zero_comp]
  · intro hs
    apply (cancel_mono k).mp
    rw [zero_comp, ht', hs, zero_comp]

private theorem field_unit_section_zero (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] (hA : IsField A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (L : X.Modules) (s : Γ(L, ⊤))
    (hs : ((Classical.choose (exists_tensorPullbackAdjunction
      (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).app ⊤ s = 0) : s = 0 := by
  classical
  let _ := hA.toField
  let p := IsLocalRing.closedPoint A
  have : IsIso (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      p.asIdeal.algEquivResidueFieldOfField.bijective
  have : IsIso ((Spec (.of A)).fromSpecResidueField p) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    infer_instance
  have : IsIso (f.fiberι p) := by
    dsimp [Scheme.Hom.fiberι]
    infer_instance
  have : (pushforward (f.fiberι p)).IsEquivalence :=
    pushforward_iso_equivalence (asIso (f.fiberι p))
  let a := Classical.choose (exists_tensorPullbackAdjunction (f.fiberι p))
  have : IsIso (a.unit.app L) := inferInstance
  have hz : homOfGlobalSection L s ≫ a.unit.app L = 0 :=
    (section_comp_zero_iff L _ s _).mp hs
  have hz' : homOfGlobalSection L s = 0 := by
    apply (cancel_mono (a.unit.app L)).mp
    simpa using hz
  have ht := congrArg (fun b : unit X ⟶ L ↦ b.app ⊤ (1 : Γ(X, ⊤))) hz'
  simpa [homOfGlobalSection_app_one] using ht

private theorem closed_fibre_unit_zero_iff (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (L : X.Modules) (s : Γ(L, ⊤)) :
    ((Classical.choose (exists_tensorPullbackAdjunction
      (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).app ⊤ s = 0 ↔
    ((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))).unit.app L).app ⊤ s = 0 := by
  classical
  let p := IsLocalRing.closedPoint A
  have : p.asIdeal.IsMaximal := by
    change (IsLocalRing.maximalIdeal A).IsMaximal
    infer_instance
  let q : CommRingCat.of (A ⧸ p.asIdeal) ≅ CommRingCat.of p.asIdeal.ResidueField :=
    (RingEquiv.ofBijective (algebraMap (A ⧸ p.asIdeal) p.asIdeal.ResidueField)
      p.asIdeal.bijective_algebraMap_quotient_residueField).toCommRingCatIso
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  let e : Spec ((Spec (.of A)).residueField p) ≅ Spec (.of (A ⧸ p.asIdeal)) :=
    asIso (Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv ≫ Spec.map q.hom)
  have he : e.hom ≫ g = (Spec (.of A)).fromSpecResidueField p := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    change Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv ≫
      Spec.map q.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal)) = _
    rw [← Spec.map_comp]
    congr 2
  let t : f.fiber p ⟶ Limits.pullback f g :=
    pullback.map f ((Spec (.of A)).fromSpecResidueField p) f g
      (𝟙 X) e.hom (𝟙 _) (by simp) (by simp [he])
  have : IsIso t := by dsimp [t]; infer_instance
  exact unit_section_zero_iso (pullback.fst f g) (f.fiberι p) (asIso t)
    (by simp [t, Scheme.Hom.fiberι]) L s

-- The integral-fibre hypothesis stays in the original interface but is not needed here.
set_option linter.unusedVariables false in
/-- A section vanishing on the closed fibre is divisible by a maximal-ideal element,
assuming the closed fibre is integral.
Source: Stacks Project, More on Morphisms, Tag 0EX8.
(blueprint: new-valuation-closed-fibre-section-divisible)

Proof: If A is a field, its closed fibre inclusion is an isomorphism, so the unit
is an isomorphism and s = 0; choose pi = t = 0. Otherwise identify the quotient
fibre with the scheme-theoretic closed fibre. Uniqueness of adjoints compares the
units by isomorphisms, so they have the same kernel. Apply the closed-fibre
vanishing lemma to get a nonzero pi in the maximal ideal. The principal quotient
kernel theorem identifies multiplication by pi with the restriction kernel.
Represent s by O_X -> L, lift this morphism through the kernel, and evaluate the
lift at 1 to obtain t. Evaluating the kernel factorization gives pi t = s. The
integrality hypothesis is retained in the signature but is not used in this proof.
-/
theorem closed_fibre_section_is_divisible
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))))
    (s : Γ(L, ⊤))
    (hs : (((Classical.choose (exists_tensorPullbackAdjunction
      (f.fiberι (IsLocalRing.closedPoint A)))).unit.app L).val.app (op ⊤) s = 0)) :
    ∃ π : A, π ∈ IsLocalRing.maximalIdeal A ∧ ∃ t : Γ(L, ⊤),
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π • t = s := by
  classical
  by_cases hA : IsField A
  · have hs0 := field_unit_section_zero A hA f L s hs
    refine ⟨0, Ideal.zero_mem _, 0, ?_⟩
    simp [hs0]
  · have : QuasiCompact f := inferInstance
    have : QuasiSeparated f := inferInstance
    have hs' := (closed_fibre_unit_zero_iff A f L s).mp hs
    have hv := exists_nonzero_maximalIdeal_section_eq_zero A hA (X := X) f L s
    have hx := hv hs'
    obtain ⟨π, hπ, hm, hsπ⟩ := hx
    obtain ⟨w, ⟨hk⟩⟩ := principal_quotient_unit_kernel A f L π hπ
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let η := (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app L
    have ha : homOfGlobalSection L s ≫ η = 0 :=
      (section_comp_zero_iff L _ s η).mp hsπ
    obtain ⟨t, ht⟩ := KernelFork.IsLimit.lift' hk (homOfGlobalSection L s) ha
    refine ⟨π, hm, t.app ⊤ (1 : Γ(X, ⊤)), ?_⟩
    have ht1 := congrArg (fun b : unit X ⟶ L ↦ b.app ⊤ (1 : Γ(X, ⊤))) ht
    simpa [Hom.comp_app, smulHom_app_apply, homOfGlobalSection_app_one] using ht1

end AlgebraicGeometry.Scheme.Modules
