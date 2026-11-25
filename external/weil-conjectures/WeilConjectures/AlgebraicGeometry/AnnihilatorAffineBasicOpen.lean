/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal

/-! # Compatibility of affine annihilators on basic opens

Source: Stacks Project, Morphisms, Lemma 05JU and Algebra, Lemma 07T8.
(blueprint: lem-weil-pbc-annihilator-affine-basic-open)
-/

@[expose] public section

universe u v w u₁ v₁

open CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction to a slice site preserves finite type for a sheaf of modules over
an arbitrary sheaf of rings. Pull a local finite generating cover back along `Over.forget U`;
its local maps preserve colimits and the unit, hence preserve finite generating families.
Source: Stacks Project, Modules, Tag 01B5, locality of finite type.
(blueprint: lem-weil-pbc-annihilator-affine-basic-open) -/
private theorem isFiniteType_over_site
    {C : Type u₁} [Category.{v₁} C] [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (V : C) (W : Over V), HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ (V : C) (W : Over V),
      ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) [F.IsFiniteType] (U : C) :
    (F.over U).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let G := Over.forget U
  let K := J.over U
  let S := R.over U
  let φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R := 𝟙 _
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
              (J.over (q.X i.2.1))).obj (R.over (q.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        have : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
          SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
        exact (q.generators i.2.1).map (SheafOfModules.pushforward.{u} ψ) (Iso.refl _) }
  apply SheafOfModules.IsFiniteType.mk (R := R.over U)
  refine ⟨d, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := d) (fun i ↦ ?_)
  have := hq.isFiniteType i.2.1
  dsimp only [d]
  infer_instance

private theorem annihilator_localized
    (R : Type u) [CommRing R] (S : Submonoid R) (A : Type v) [CommRing A]
    [Algebra R A] [IsLocalization S A]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type w) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] :
    Ideal.map (algebraMap R A) (Module.annihilator R M) = Module.annihilator A N := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    apply Module.mem_annihilator.mpr
    intro y
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj S g y
    apply IsLocalizedModule.smul_injective g t
    change t • ((algebraMap R A r) • y) = t • (0 : N)
    change t • y = g m at ht
    rw [smul_zero, smul_comm, ht]
    rw [IsScalarTower.algebraMap_smul A r, ← g.map_smul,
      Module.mem_annihilator.mp hr m, map_zero]
  · intro z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S z
    have hzero (m : M) : g (r • m) = 0 := by
      rw [g.map_smul, ← IsScalarTower.algebraMap_smul A, ← hrs, mul_smul,
        Module.mem_annihilator.mp hz]
    obtain ⟨n, e, he⟩ := Module.Finite.exists_fin (R := R) (M := M)
    choose c hc using fun j : Fin n ↦ (IsLocalizedModule.eq_zero_iff S g).mp (hzero (e j))
    let t : S := ∏ j, c j
    have hgen (j : Fin n) : (t.1 * r) • e j = 0 := by
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ j)
      change ((∏ j, c j : S).1 * r) • e j = 0
      rw [hd, Submonoid.coe_mul, mul_smul, mul_smul]
      have hcj := hc j
      change (c j).1 • (r • e j) = 0 at hcj
      rw [smul_comm (c j).1 d.1, hcj, smul_zero]
    have hann : t.1 * r ∈ Module.annihilator R M := by
      apply Module.mem_annihilator.mpr
      intro m
      have hspan : Submodule.span R (Set.range e) ≤
          LinearMap.ker (LinearMap.lsmul R M (t.1 * r)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact hgen j
      exact hspan (he ▸ Submodule.mem_top : m ∈ Submodule.span R (Set.range e))
    apply (IsLocalization.mem_map_algebraMap_iff S A).mpr
    refine ⟨⟨⟨t.1 * r, hann⟩, t * s⟩, ?_⟩
    simp only [Submonoid.coe_mul, map_mul]
    calc
      z * (algebraMap R A t.1 * algebraMap R A s.1) =
          algebraMap R A t.1 * (z * algebraMap R A s.1) := by ring
      _ = algebraMap R A t.1 * algebraMap R A r := by rw [hrs]

set_option backward.isDefEq.respectTransparency false in
/-- Affine annihilator ideals of a finite type quasi-coherent module are compatible with
restriction to basic opens.
Source: Stacks Project, Morphisms, Lemma 05JU (last paragraph), and Algebra, Lemma 07T8.
(blueprint: lem-weil-pbc-annihilator-affine-basic-open)

Proof: fix an affine open U, put A = O_X(U), M = F(U), and fix f in A. Finite type and
quasi-coherence imply that M is finite. The restriction ring O_X(D(f)) is a localization
A_f, and the canonical quasi-coherent section base-change map identifies F(D(f)) with
M tensor_A A_f, with its A_f action and with restriction corresponding to m tensor 1.
The tensor identification gives an IsLocalizedModule structure on restriction. For the
forward ideal inclusion, a scalar in Ann_A(M) kills every localized section: multiply
such a section by an invertible denominator to bring it into the image of M, and use
linearity and injectivity of multiplication by that denominator. For the reverse
inclusion, write a localized annihilator z as a fraction r/s. Then restriction sends
r times every generator of M to zero. The localization equality criterion gives a
denominator c_j killing r times the j-th generator. The product t of the finitely many
c_j kills r times all generators, hence all of M by linearity. Thus tr belongs to
Ann_A(M), and z = (tr)/(ts) belongs to its extended ideal. This proves exactly the
claimed equality along the actual restriction homomorphism. The empty product is 1,
so the proof also covers the zero module. The equality remains
valid for f = 0 and for M = 0: localization at 0 is the zero ring, and the annihilator
of the zero module is the unit ideal. -/
theorem annihilator_affine_basicOpen
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      (Module.annihilator Γ(X, U.1) Γ(F, U.1)) =
      Module.annihilator Γ(X, (X.affineBasicOpen f).1) Γ(F, (X.affineBasicOpen f).1) := by
  let : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  let : Module Γ(X, U.1) Γ(F, X.basicOpen f) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    { smul_assoc := fun r a m ↦ by
        change (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r * a) • m =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • (a • m)
        exact mul_smul _ _ _ }
  have : IsLocalization (Submonoid.powers f) Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  have : (F.over U.1).IsFiniteType :=
    isFiniteType_over_site (Opens.grothendieckTopology X) X.ringCatSheaf F U.1
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    ((quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1 U.1 U.2 |>.1 |>.mp
      inferInstance
  have hbc := quasiCoherent_affine_section_baseChange X F (X.affineBasicOpen f) U
    (X.basicOpen_le f)
  dsimp only [Scheme.affineBasicOpen] at hbc
  obtain ⟨c, hc, hs, ht⟩ := hbc
  let g : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(F, X.basicOpen f) :=
    { toFun := F.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' := map_add _
      map_smul' := by
        intro r m
        change F.val.map (homOfLE (X.basicOpen_le f)).op (r • m) =
          X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op r •
            F.val.map (homOfLE (X.basicOpen_le f)).op m
        exact F.val.map_smul _ r m }
  let d : (Γ(X, X.basicOpen f) ⊗[Γ(X, U.1)] Γ(F, U.1)) →ₗ[
      Γ(X, X.basicOpen f)] Γ(F, X.basicOpen f) :=
    { toFun := fun t ↦ c ((TensorProduct.comm _ _ _) t)
      map_add' := by intro a b; simp
      map_smul' := by
        intro r t
        simpa using hs r ((TensorProduct.comm _ _ _) t) }
  have hd : Function.Bijective d :=
    hc.comp (TensorProduct.comm _ _ _).bijective
  have hg : IsBaseChange Γ(X, X.basicOpen f) g :=
    .of_equiv (LinearEquiv.ofBijective d hd) (fun m ↦ by
      change c ((TensorProduct.comm _ _ _) (1 ⊗ₜ m)) = g m
      simpa [g] using ht m 1)
  have : IsLocalizedModule (Submonoid.powers f) g :=
    (isLocalizedModule_iff_isBaseChange _ Γ(X, X.basicOpen f) g).mpr hg
  exact annihilator_localized Γ(X, U.1) (Submonoid.powers f)
    Γ(X, X.basicOpen f) Γ(F, U.1) Γ(F, X.basicOpen f) g

end AlgebraicGeometry.Scheme.Modules
