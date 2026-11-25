/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Valuation.ValuationRing
import WeilConjectures.AlgebraicGeometry.FibreCartierLocal

/-!
# Zero locus over a valuation base

Source: More on Morphisms, Lemma 37.33.3 (Tag 0EX8), with Divisors Lemma 31.19.9
(Tag 062Y) (blueprint: lem-sc-valuation-zero-section-relative-cartier).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The zero scheme of a section whose restriction to the integral closed fibre is nonzero is
relative effective Cartier over a valuation base (Stacks, Tags 0EX8 and 062Y).
Module pullback is `tensorPullback` (def-pc-module-pullback); the restriction of `s` to the
fibre `X₀ = f.fiber x₀` is the unit of its canonical adjunction
(lem-pc-module-pullback-adjunction) applied to `s`.

Proof: `Z(s)` is locally principal (lem-pc-zero-scheme-properties (1)): on an affine open
`Spec B` where `M` is free on `e` and `s = a e`, `Z(s) ∩ U = Spec (B/(a))`, so its closed fibre
is `Z(s|_{X₀})`. The adjunction-unit comparison with ordinary module pullback shows that
the pulled-back section morphism is nonzero. Thus the fibre ideal is nonzero by
`Hom.zeroLocus_eq_bot_iff`.
It is locally principal, hence invertible on the integral fibre by
`IdealSheafData.IsLocallyPrincipal.isInvertible`.
For `x ∈ Z(s)` the closure `C` of `x` lies in `Z(s)`, `f(C)` is closed and nonempty
(lem-weil-pbc-proper-closed-image), hence contains the closed point of the local scheme
`Spec A`; so `x` specializes to some `y ∈ Z(s)` in the closed fibre. The local fibre-Cartier
criterion (lem-pc-recd-fibre-cartier-local; `f` flat, locally of finite presentation) gives an
open `U_y ∋ y`, hence `∋ x`, on which `Z(s)` is relative effective Cartier. These opens with
`X \ Z(s)` cover `X`, and the property is local, so `Z(s)` is a relative effective Cartier
divisor; in particular `Z(s) → Spec A` is flat (def-pc-relative-effective-cartier).
(blueprint: lem-sc-valuation-zero-section-relative-cartier) -/
theorem valuation_zero_section_relative_cartier
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (x₀ : Spec (.of A)) (hx₀ : IsClosed ({x₀} : Set (Spec (.of A))))
    [IsIntegral (f.fiber x₀)]
    (M : X.Modules) [M.IsInvertible] (s : Γ(M, ⊤))
    (hs₀ : ((Classical.choose (exists_tensorPullbackAdjunction (f.fiberι x₀))).unit.app M).val.app
      (op ⊤) s ≠ 0) :
    Scheme.IdealSheafData.IsRelativeEffectiveCartier
      (Scheme.Modules.Hom.zeroLocus (Scheme.Modules.homOfGlobalSection M s)) f := by
  classical
  let g := f.fiberι x₀
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    IsInvertible.sheafOfModules_isInvertible M
  have : (unit X).IsInvertible :=
    ⟨fun _ ↦ ⟨⊤, trivial, ⟨pullbackObjUnitIso _⟩⟩⟩
  have : SheafOfModules.IsInvertible.{u, u, u} (unit X) :=
    IsInvertible.sheafOfModules_isInvertible (unit X)
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback g).obj (unit X)) :=
    SheafOfModules.IsInvertible.pullback inferInstance
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback g).obj M) :=
    SheafOfModules.IsInvertible.pullback inferInstance
  let φ := homOfGlobalSection M s
  have hprincipal := φ.isLocallyPrincipal_zeroLocus
  have hfibre : (φ.zeroLocus.comap g).IsInvertible := by
    apply (hprincipal.comap g).isInvertible
    rw [Hom.comap_zeroLocus]
    intro hbot
    have hzero := (Hom.zeroLocus_eq_bot_iff ((pullback g).map φ)).mp hbot
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    let adj' := pullbackPushforwardAdjunction g
    let e := adj.leftAdjointUniq adj'
    have hn := adj'.unit_naturality φ
    rw [hzero, Functor.map_zero, comp_zero] at hn
    have hz := congrArg (fun q ↦ q.val.app (op ⊤) (1 : Γ(X, ⊤))) hn.symm
    have he := adj.unit_leftAdjointUniq_hom_app adj' M
    have hes := congrArg (fun q ↦ q.val.app (op ⊤) s) he
    have hstd : (adj'.unit.app M).val.app (op ⊤) s = 0 := by
      change (adj'.unit.app M).val.app (op ⊤)
        ((φ.val.app (op ⊤)) (1 : Γ(X, ⊤))) = 0 at hz
      have hφs : (φ.val.app (op ⊤)) (1 : Γ(X, ⊤)) = s := by
        simpa only [φ, Hom.app, ModuleCat.forget₂_map, AddCommGrpCat.ofHom_apply,
          presheaf_map_id_apply] using! homOfGlobalSection_app_one M s ⊤
      rwa [hφs] at hz
    apply hs₀
    apply (ConcreteCategory.bijective_of_isIso ((e.app M).hom.app ⊤)).injective
    change ((e.app M).hom.app ⊤) _ = ((e.app M).hom.app ⊤) 0
    rw [map_zero]
    exact hes.trans hstd
  have hx : x₀ = IsLocalRing.closedPoint A := by
    exact ((IsLocalRing.specializes_closedPoint x₀).mem_closed hx₀ rfl).symm
  subst x₀
  let J := φ.zeroLocus
  have hJ := hprincipal
  have key (x : X) : ∃ U : X.Opens, x ∈ U ∧
      (J.comap U.ι).IsRelativeEffectiveCartier (U.ι ≫ f) := by
    by_cases hx : x ∈ J.support
    · obtain ⟨y, hxy, hy⟩ := f.isClosedMap.specializingMap
        (IsLocalRing.specializes_closedPoint (f x))
      have hyJ : y ∈ J.support := hxy.mem_closed J.support.isClosed hx
      have hprincipal : ∃ V : X.Opens, y ∈ V ∧ (J.comap V.ι).IsLocallyPrincipal :=
        ⟨⊤, trivial, hJ.comap _⟩
      have hfib : ∃ V : X.Opens, y ∈ V ∧
          ((J.comap (f.fiberι (f y))).comap ((f.fiberι (f y) ⁻¹ᵁ V).ι)).IsInvertible := by
        refine ⟨⊤, trivial, ?_⟩
        rw [hy]
        exact hfibre.comap_of_isOpenImmersion _
      obtain ⟨U, hyU, hU⟩ := fibre_cartier_local f J y hyJ hprincipal hfib
      exact ⟨U, hxy.mem_open U.isOpen hyU, hU⟩
    · let U : X.Opens := ⟨(J.support : Set X)ᶜ, J.support.isClosed.isOpen_compl⟩
      have hJU : J.comap U.ι = ⊤ := by
        apply (support_eq_bot_iff _).mp
        rw [support_comap]
        ext z
        exact iff_false_intro z.property
      refine ⟨U, hx, ?_, ?_⟩
      · rw [hJU]
        intro z
        obtain ⟨V, hV, hzV, -⟩ :=
          exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
        refine ⟨⟨V, hV⟩, hzV, ?_⟩
        rw [ideal_top, Pi.top_apply, ← Ideal.span_singleton_one]
        exact Ideal.isRegularPrincipal_span_singleton (one_mem _)
      · have : IsEmpty (J.comap U.ι).subscheme := by rw [hJU]; infer_instance
        rw [Flat.iff_flat_stalkMap]
        exact fun z ↦ isEmptyElim z
  choose U hxU hU using key
  have hcov : ⨆ x, U x = ⊤ := eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  refine ⟨IsInvertible.of_iSup_opensRange_eq_top (fun x ↦ (U x).ι)
    (by simpa using hcov) (fun x ↦ (hU x).1), ?_⟩
  have hcov' : ⨆ x, J.subschemeι ⁻¹ᵁ U x = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat)
    (fun x ↦ J.subschemeι ⁻¹ᵁ U x) hcov'
  intro x
  let e : (J.comap (U x).ι).subscheme ≅ (J.subschemeι ⁻¹ᵁ U x).toScheme :=
    J.comapIso (U x).ι ≪≫ pullbackSymmetry _ _ ≪≫
      pullbackRestrictIsoRestrict J.subschemeι (U x)
  have he : e.inv ≫ (J.comap (U x).ι).subschemeι ≫ (U x).ι =
      (J.subschemeι ⁻¹ᵁ U x).ι ≫ J.subschemeι := by
    simp only [e, Iso.trans_inv, Category.assoc,
      comapIso_inv_subschemeι_assoc, pullbackSymmetry_inv_comp_fst_assoc]
    exact morphismRestrict_ι J.subschemeι (U x)
  have : Flat ((J.comap (U x).ι).subschemeι ≫ (U x).ι ≫ f) := (hU x).2
  rw [← Category.assoc, ← he, Category.assoc]
  simpa only [Category.assoc] using
    (inferInstance : Flat (e.inv ≫ (J.comap (U x).ι).subschemeι ≫ (U x).ι ≫ f))


end Modules
end Scheme
end AlgebraicGeometry
