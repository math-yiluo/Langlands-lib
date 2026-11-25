/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Support
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Closed support of a finite type module

Source: Stacks Project, Morphisms, Lemma 056J (part (1)), via Lemma 056I,
Properties Lemma 01PB and Algebra Lemma 00L2 (blueprint:
lem-weil-pbc-finite-type-module-support-closed).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.style.haveILetI false in
/-- Restriction preserves finite type: pull the local generating cover back along
`Over.forget U`; its local maps preserve colimits and the unit, hence carry each finite
family of generators to a finite family. Source: Stacks Project, Modules, Tag 01B5,
the locality of finite type used in the finite-pushforward argument
(blueprint: lem-weil-pbc-finite-type-module-support-closed). -/
private theorem isFiniteType_over (X : Scheme.{u}) (F : X.Modules)
    (hF : F.IsFiniteType) (U : X.Opens) : (F.over U).IsFiniteType := by
  classical
  haveI : F.IsFiniteType := hF
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let G := Over.forget U
  let J := Opens.grothendieckTopology X
  let K := J.over U
  let S := X.ringCatSheaf.over U
  let φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj X.ringCatSheaf := 𝟙 _
  let d : (F.over U).LocalGeneratorsData :=
    { I := Σ (V : Over U) (i : q.I), G.obj V ⟶ q.X i
      X := fun i ↦ i.1
      coversTop := fun V ↦ by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj V)))
        intro W g ⟨i, ⟨v⟩⟩
        exact ⟨⟨W, i, v⟩, ⟨𝟙 _⟩⟩
      generators := fun i ↦ by
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        have : G'.IsContinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          Functor.isContinuous_comp _ _ _ (J.over _) _
        have : G'.IsCocontinuous (K.over i.1) (J.over (q.X i.2.1)) :=
          isCocontinuous_comp _ _ _ (J.over _)
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (q.X i.2.1))).obj (X.ringCatSheaf.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          SheafOfModules.isLeftAdjoint_pushforward_of_isIso.{u} ψ
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) (Iso.refl _) }
  apply SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf.over U)
  refine ⟨d, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.1
  dsimp only [d]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, the stalk of a quasi-coherent module is the localization of its
sections, compatibly with germs.

Proof: use the germ map as a linear map over `Γ(X,U)`. Elements outside the prime have
unit germs and hence act invertibly on the stalk. Represent any germ over an open `V`,
shrink to a basic open `D(g)` inside `V`, and extend its section after multiplying by a
power of `g`. This gives the fraction representation. If two sections have equal germs,
shrink their equality to a basic open; the basic-open torsion lemma kills their difference
by a power of `g`. These are the three axioms of `IsLocalizedModule`. Its canonical
isomorphism sends `m/1` to the germ of `m`, so linearity gives the denominator identity.
No finite generation is needed, and for the zero module both sides are zero.
Source: Stacks Project, Morphisms, Lemma 056I, proof; Schemes, Lemma 01HV (7).
(blueprint: lem-weil-pbc-finite-type-module-support-closed) -/
private theorem quasicoherent_affine_stalk_germ_localization (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] :
    (∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ∃ e : LocalizedModule (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U.1) ≃+
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
        ∀ (m : Γ(F, U.1)) (s : (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl),
          X.presheaf.germ U.1 x hx s.1 • e (LocalizedModule.mk m s) =
            F.presheaf.germ U.1 x hx m) := by
  intro U x hx
  let A := Γ(X, U.1)
  let S := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    inferInstanceAs (Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
      (F.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ _ _)).presheaf x))
  let : Algebra A (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Module A (F.presheaf.stalk x) :=
    Module.compHom _ (X.presheaf.germ U.1 x hx).hom
  let f : Γ(F, U.1) →ₗ[A] F.presheaf.stalk x :=
    { toFun := F.presheaf.germ U.1 x hx
      map_add' := map_add _
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul (R := X.presheaf) F.val x U.1 hx r m }
  have hprime (g : A) (hxg : x ∈ X.basicOpen g) : g ∈ S := by
    change U.2.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g
    rw [← U.2.fromSpec_preimage_basicOpen]
    change U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g
    rwa [U.2.fromSpec_primeIdealOf]
  have hloc : IsLocalizedModule S f := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      have := U.2.isLocalization_stalk ⟨x, hx⟩
      have hu : IsUnit (X.presheaf.germ U.1 x hx s.1) :=
        IsLocalization.map_units (X.presheaf.stalk x) s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : F.presheaf.stalk x ↦
        X.presheaf.germ U.1 x hx s.1 • m)
      exact ⟨(fun a b h ↦ hu.smul_left_cancel.mp h), fun m ↦
        ⟨hu.unit⁻¹ • m, smul_inv_smul hu.unit m⟩⟩
    · intro y
      obtain ⟨V, hxV, m, rfl⟩ := F.presheaf.exists_germ_eq y
      obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hx
      obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen F U.2 g
        (F.presheaf.map (homOfLE hgV).op m)
      refine ⟨⟨t, ⟨g ^ n, S.pow_mem (hprime g hxg) n⟩⟩, ?_⟩
      have h := congrArg (F.presheaf.germ (X.basicOpen g) x hxg) ht
      erw [PresheafOfModules.germ_smul (R := X.presheaf) F.val] at h
      rw [_root_.map_pow] at h
      erw [X.presheaf.germ_res_apply, F.presheaf.germ_res_apply,
        F.presheaf.germ_res_apply] at h
      change X.presheaf.germ U.1 x hx (g ^ n) • F.presheaf.germ V x hxV m =
        F.presheaf.germ U.1 x hx t
      rw [_root_.map_pow]
      exact h.symm
    · intro m₁ m₂ hm
      obtain ⟨V, hxV, i₁, i₂, heq⟩ := F.presheaf.germ_eq x hx hx m₁ m₂ hm
      obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hx
      have hz : F.presheaf.map (homOfLE (X.basicOpen_le g)).op (m₁ - m₂) = 0 := by
        have h := congrArg (F.presheaf.map (homOfLE hgV).op) heq
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at h
        rw [map_sub, sub_eq_zero]
        convert h using 1
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F U.2 g (m₁ - m₂) hz
      refine ⟨⟨g ^ n, S.pow_mem (hprime g hxg) n⟩, ?_⟩
      exact sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)
  have := hloc
  refine ⟨(IsLocalizedModule.iso S f).toAddEquiv, ?_⟩
  intro m s
  change s.1 • IsLocalizedModule.iso S f (LocalizedModule.mk m s) = f m
  rw [← (IsLocalizedModule.iso S f).map_smul, LocalizedModule.smul'_mk,
    ← Submonoid.smul_def, LocalizedModule.mk_cancel, IsLocalizedModule.iso_mk_one]

/-- Let `F` be a quasi-coherent `𝒪_X`-module of finite type and `U` an affine open with
`A = Γ(X, U)`, `M = Γ(F, U)`, the point `x ∈ U` corresponding to the prime `p_x` of `A`.
Then (1) `F_x ≅ M_{p_x}`, the isomorphism sending `m / s` to `s_x⁻¹ • m_x`
(stated as `s_x • e (m / s) = m_x`, which determines `e` since `s_x` is a unit);
(2) `x ∈ Supp F` iff `Ann_A(M) ⊆ p_x`; (3) `Supp F ∩ U = V(Ann_A(M))`;
(4) `Supp F = {x | F_x ≠ 0}` is closed in `X`.

Proof: on the affine chart `U ≅ Spec A` the restriction `F|_U` is quasi-coherent of finite
type, hence `F|_U ≅ M~` with `M` finitely generated (Properties 01PB and the tilde/Γ
adjunction). The stalk of `F` at `x` is the stalk of `F|_U` (cofinal neighbourhoods), and the
stalk of `M~` at `p_x` is `M_{p_x}` (Schemes 01HV (7)), giving (1). By Algebra 00L2 a finite
module has `M_p ≠ 0` iff `Ann_A(M) ⊆ p`, giving (2) and (3). The sets `V(Ann_A(M))` are closed
in each affine chart and the affine opens cover `X`, giving (4).
Source: Stacks Project, Morphisms, Lemma 056J (1), via Lemma 056I, Properties Lemma 01PB and
Algebra Lemma 00L2.
(blueprint: lem-weil-pbc-finite-type-module-support-closed) -/
theorem finite_type_module_support_closed (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    (∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ∃ e : LocalizedModule (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U.1) ≃+
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
        ∀ (m : Γ(F, U.1)) (s : (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl),
          X.presheaf.germ U.1 x hx s.1 • e (LocalizedModule.mk m s) =
            F.presheaf.germ U.1 x hx m) ∧
    (∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ¬ Subsingleton (F.presheaf.stalk x) ↔
        Module.annihilator Γ(X, U.1) Γ(F, U.1) ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) ∧
    (∀ (U : X.affineOpens),
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) =
        U.2.fromSpec '' PrimeSpectrum.zeroLocus
          (Module.annihilator Γ(X, U.1) Γ(F, U.1) : Set Γ(X, U.1))) ∧
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  classical
  have hstalk := quasicoherent_affine_stalk_germ_localization X F
  have hmem : ∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1),
      ¬ Subsingleton (F.presheaf.stalk x) ↔
        Module.annihilator Γ(X, U.1) Γ(F, U.1) ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro U x hx
    have : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
      (((quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1 U.1 U.2).1.mp
        (isFiniteType_over X F inferInstance U.1)
    obtain ⟨e, -⟩ := hstalk U x hx
    have he : Subsingleton (LocalizedModule
        (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U.1)) ↔
        Subsingleton (F.presheaf.stalk x) := e.toEquiv.subsingleton_congr
    exact (not_congr he).symm.trans
      (not_subsingleton_iff_nontrivial.trans Module.mem_support_iff_of_finite)
  have hset : ∀ (U : X.affineOpens),
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∩ (U.1 : Set X) =
        U.2.fromSpec '' PrimeSpectrum.zeroLocus
          (Module.annihilator Γ(X, U.1) Γ(F, U.1) : Set Γ(X, U.1)) := by
    intro U
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨U.2.primeIdealOf ⟨x, hxU⟩, ?_, U.2.fromSpec_primeIdealOf _⟩
      exact (hmem U x hxU).mp hx
    · rintro ⟨p, hp, rfl⟩
      have hxU : U.2.fromSpec p ∈ U.1 := U.2.range_fromSpec.le ⟨p, rfl⟩
      refine ⟨(hmem U _ hxU).mpr ?_, hxU⟩
      have hp' : U.2.primeIdealOf ⟨U.2.fromSpec p, hxU⟩ = p :=
        U.2.fromSpec.isOpenEmbedding.injective (U.2.fromSpec_primeIdealOf _)
      rwa [hp']
  refine ⟨hstalk, hmem, hset, ?_⟩
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (show x ∈ (⊤ : X.Opens) from trivial)
  let V := PrimeSpectrum.zeroLocus (Module.annihilator Γ(X, U) Γ(F, U) : Set Γ(X, U))
  refine ⟨hU.fromSpec '' Vᶜ, ?_,
    hU.fromSpec.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl,
    ?_⟩
  · rintro y ⟨p, hp, rfl⟩ hy
    have hyU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
    have hpy := (hmem ⟨U, hU⟩ _ hyU).mp hy
    have hp' : hU.primeIdealOf ⟨hU.fromSpec p, hyU⟩ = p :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
    apply hp
    change Module.annihilator Γ(X, U) Γ(F, U) ≤ p.asIdeal
    rwa [hp'] at hpy
  · refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, hU.fromSpec_primeIdealOf _⟩
    intro hp
    exact hx ((hmem ⟨U, hU⟩ x hxU).mpr hp)

end AlgebraicGeometry.Scheme.Modules
