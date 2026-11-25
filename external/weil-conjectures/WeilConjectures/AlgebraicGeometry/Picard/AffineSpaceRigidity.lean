/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeSections
public import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
public import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
public import WeilConjectures.RingTheory.TensorLocalizationAway
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rigidity of invertible modules over an open of the affine line

Let `k` be an algebraically closed field, `X` an integral `k`-scheme whose local rings are unique
factorization domains, and `U = D(f) = Spec k[t]_f` a basic open of the affine line with
`k`-points `p` and `q`. For every invertible module `ℒ` on `X ×_k U` the restrictions
`ℒ|_{X × p}` and `ℒ|_{X × q}` are isomorphic (Stacks 0BEH).

Stacks 0BEH is stated for a normal variety `X` and an open `U` of affine `n`-space; the case of a
basic open of the affine line suffices for its applications (two `k`-points of an open of `𝔸ⁿ`
lie on a line, and an open of a line contains a basic open through both points), and the
hypothesis that the local rings of `X` are factorial holds for the smooth varieties occurring in
the proof that group schemes are quasi-projective (Stacks 0BF7).

## Strategy

Write `π : X ×_k U ⟶ X` for the projection.

* `AlgebraicGeometry.exists_isFreeGenerator_preimage_fst`: `ℒ` is trivial over `π⁻¹ V` for the
  members `V` of an affine open cover of `X`. Indeed for an affine open `W = Spec A` of `X` we
  have `π⁻¹ W = Spec (A ⊗_k k[t]_f)`, and for a point `x ∈ W` with prime `𝔭 ⊆ A` the ring
  `A_𝔭 ⊗_k k[t]_f = A_𝔭[t]_f` is a UFD, so the invertible module `Γ(ℒ, π⁻¹ W)` becomes free after
  inverting an element of `A \ 𝔭` (its Picard group being trivial).
* `AlgebraicGeometry.exists_appLE_lift_eq_mul`: a unit of `A ⊗_k k[t]_f` is `a ⊗ r` with `a` a
  unit of `A` and `r` a unit of `k[t]_f`, so its pullbacks along the two sections `X ⟶ X ×_k U`
  at `p` and `q` differ by the constant `r(p) / r(q)`.
* The pullbacks of the local generators of `ℒ` along the two sections, rescaled by these
  constants, have the same transition functions, hence glue to an isomorphism
  (`AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_isFreeGenerator`).

## Main results

- `AlgebraicGeometry.nonempty_iso_pullback_lift_of_isAlgClosed`: Stacks 0BEH.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A section `σ = (𝟙, g) : X ⟶ X ×_S T` of the first projection maps an open `W` into its
preimage `π⁻¹ W`. -/
lemma le_preimage_lift_preimage_fst {X T S : Scheme.{u}} {sX : X ⟶ S} {sT : T ⟶ S} (g : X ⟶ T)
    (hg : 𝟙 X ≫ sX = g ≫ sT) (W : X.Opens) :
    W ≤ pullback.lift (𝟙 X) g hg ⁻¹ᵁ pullback.fst sX sT ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, pullback.lift_fst, Scheme.Hom.id_preimage]

/-- Elementwise form of `Scheme.Hom.appLE_comp_appLE`. -/
lemma Scheme.Hom.appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : Γ(Z, U)) : f.appLE V W e₂ (g.appLE U V e₁ a) = (f ≫ g).appLE U W e a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- `appLE` of equal morphisms agree. -/
lemma Scheme.Hom.appLE_apply_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) :
    f.appLE U V e a = g.appLE U V e' a := by
  subst h
  rfl

/-- Pulling back a function from `X` along `X ⟶ X ×_S T ⟶ X` along a section of the first
projection gives back the function. -/
lemma appLE_lift_app_fst {X T S : Scheme.{u}} {sX : X ⟶ S} {sT : T ⟶ S} (g : X ⟶ T)
    (hg : 𝟙 X ≫ sX = g ≫ sT) (W : X.Opens) (a : Γ(X, W)) :
    (pullback.lift (𝟙 X) g hg).appLE _ W (le_preimage_lift_preimage_fst g hg W)
      ((pullback.fst sX sT).app W a) = a := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_appLE_apply _ _ _ _ (by simp)]
  refine (Scheme.Hom.appLE_apply_of_eq (pullback.lift_fst (𝟙 X) g hg) _ le_rfl a).trans ?_
  simp [Scheme.Hom.appLE]
  rfl

/-- Pulling back a function from `T` along `X ⟶ X ×_S T ⟶ T`. -/
lemma appLE_lift_appLE_snd {X T S : Scheme.{u}} {sX : X ⟶ S} {sT : T ⟶ S} (g : X ⟶ T)
    (hg : 𝟙 X ≫ sX = g ≫ sT) (W : X.Opens) (t : Γ(T, ⊤)) :
    (pullback.lift (𝟙 X) g hg).appLE _ W (le_preimage_lift_preimage_fst g hg W)
      ((pullback.snd sX sT).appLE ⊤ _ le_top t) = g.appLE ⊤ W le_top t := by
  rw [Scheme.Hom.appLE_appLE_apply _ _ _ _ (by simp)]
  exact Scheme.Hom.appLE_apply_of_eq (pullback.lift_snd (𝟙 X) g hg) _ le_top t

/-- `appLE` of a composite over the top open, elementwise. -/
lemma Scheme.Hom.comp_appLE_top_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : X.Opens) (t : Γ(Z, ⊤)) :
    (f ≫ g).appLE ⊤ W le_top t = f.appLE ⊤ W le_top (g.appTop t) := by
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- **Local triviality over the base.** Let `X` be an integral `k`-scheme whose local rings are
unique factorization domains and `f ≠ 0`. Every invertible module `ℒ` on `X ×_k Spec k[t]_f` is
trivial over `π⁻¹ V` for an affine open neighbourhood `V` of any given point of `X`, where `π` is
the first projection. -/
theorem exists_isFreeGenerator_preimage_fst {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (sX : X ⟶ Spec (.of k))
    {f : k[X]} (hf : f ≠ 0)
    (L : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))))).Modules)
    [L.IsInvertible] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      ∃ e : Γ(L, pullback.fst sX (Spec.map (CommRingCat.ofHom
        (algebraMap k (Localization.Away f)))) ⁻¹ᵁ V), Scheme.Modules.IsFreeGenerator e := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : IsAffineHom (pullback.fst sX (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away f))))) := MorphismProperty.pullback_fst _ _ inferInstance
  let : Algebra k Γ(X, W) :=
    ((sX.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  obtain ⟨e, he1, -⟩ := exists_ringEquiv_tensor_app_preimage_fst (R := Localization.Away f) sX hW
  let : Algebra Γ(X, W) Γ(pullback sX (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away f)))), pullback.fst sX (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away f)))) ⁻¹ᵁ W) :=
    ((pullback.fst sX _).app W).hom.toAlgebra
  let e' := AlgEquiv.ofRingEquiv (R := Γ(X, W)) (f := e) fun a ↦ he1 a
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW⟩
  have := hW.isLocalization_stalk ⟨x, hxW⟩
  have := hX x
  let : Algebra k (X.presheaf.stalk x) :=
    ((algebraMap Γ(X, W) (X.presheaf.stalk x)).comp (algebraMap k Γ(X, W))).toAlgebra
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨_, _⟩ := TensorProduct.uniqueFactorizationMonoid_localization_atPrime
    (D := X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal hf e'
  obtain ⟨_, ⟨a, ha, rfl⟩, g, hg⟩ :=
    Scheme.Modules.exists_mem_isFreeGenerator_basicOpen L (hW.preimage (pullback.fst sX _))
      (Algebra.algebraMapSubmonoid _ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl)
  refine ⟨X.basicOpen a, hW.basicOpen a, (X.mem_basicOpen a x hxW).mpr
    (IsLocalization.map_units (X.presheaf.stalk x)
      (M := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl) ⟨a, ha⟩), ?_⟩
  rw [Scheme.preimage_basicOpen]
  exact ⟨g, hg⟩

/-- **Units over `π⁻¹ W` are constant along the fibres up to a unit of the base.** Let `k` be
algebraically closed, `X` an integral `k`-scheme, `f ≠ 0`, and `p`, `q` two `k`-points of
`Spec k[t]_f`. For an affine open `W ⊆ X` and a unit `u` of `Γ(X ×_k Spec k[t]_f, π⁻¹ W)`, the
pullbacks of `u` along the sections `X ⟶ X ×_k Spec k[t]_f` at `p` and `q` differ by a constant
`c ∈ k`: as `u = a ⊗ r` with `a ∈ Γ(X, W)ˣ` and `r ∈ k[t]_fˣ`, one has `c = r(p) / r(q)`. -/
theorem exists_appLE_lift_eq_mul [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) {f : k[X]} (hf : f ≠ 0)
    (p q : Spec (.of k) ⟶ Spec (.of (Localization.Away f)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) = 𝟙 _)
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) = 𝟙 _)
    {W : X.Opens} (hW : IsAffineOpen W)
    (u : Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f)))),
      pullback.fst sX (Spec.map (CommRingCat.ofHom
        (algebraMap k (Localization.Away f)))) ⁻¹ᵁ W)ˣ) :
    ∃ c : Γ(Spec (.of k), ⊤),
      (pullback.lift (𝟙 X) (sX ≫ p) (by simp [hp])).appLE _ W
          (le_preimage_lift_preimage_fst _ _ W) u.1 =
        sX.appLE ⊤ W le_top c * (pullback.lift (𝟙 X) (sX ≫ q) (by simp [hq])).appLE _ W
          (le_preimage_lift_preimage_fst _ _ W) u.1 := by
  by_cases hne : Nonempty W
  swap
  · have : Subsingleton Γ(X, W) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty (eq_bot_iff.mpr fun x hx ↦ hne ⟨⟨x, hx⟩⟩))
    exact ⟨0, Subsingleton.elim _ _⟩
  have := IsIntegral.component_integral (X := X) W
  let := ((sX.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  obtain ⟨e, he1, he2⟩ := exists_ringEquiv_tensor_app_preimage_fst (R := Localization.Away f) sX hW
  obtain ⟨a, r, har⟩ := TensorProduct.exists_units_eq_tmul Γ(X, W) hf (Units.map e.symm u)
  have hu : u.1 = _ := (e.symm_apply_eq.mp har).trans (by
    rw [← mul_one (a : Γ(X, W)), ← one_mul (r : Localization.Away f),
      ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, he1, he2])
  let t (s : (Localization.Away f)ˣ) := (Scheme.ΓSpecIso (.of (Localization.Away f))).inv s.1
  refine ⟨p.appTop (t r) * q.appTop (t r⁻¹), ?_⟩
  have hQ : sX.appLE ⊤ W le_top (q.appTop (t r⁻¹)) * sX.appLE ⊤ W le_top (q.appTop (t r)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
      map_one, map_one]
  simp only [hu, map_mul]
  rw [appLE_lift_app_fst, appLE_lift_app_fst, appLE_lift_appLE_snd,
    appLE_lift_appLE_snd, Scheme.Hom.comp_appLE_top_apply, Scheme.Hom.comp_appLE_top_apply]
  linear_combination (-((a : Γ(X, W)) * sX.appLE ⊤ W le_top (p.appTop (t r)))) * hQ

/-- Elementwise form of `Scheme.Hom.appLE_map`. -/
lemma Scheme.Hom.appLE_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (a : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e a) = f.appLE U V' (h.trans e) a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- Elementwise form of `Scheme.Hom.map_appLE`. -/
lemma Scheme.Hom.map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE h).op a) =
      f.appLE U' V (e.trans (f.preimage_mono h)) a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- A section `σ` of `π` maps an open `W` into `π⁻¹ W`. -/
lemma le_preimage_preimage_of_comp_eq_id {X Y : Scheme.{u}} {π : Y ⟶ X} {σ : X ⟶ Y}
    (hσ : σ ≫ π = 𝟙 X) (W : X.Opens) : W ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, hσ, Scheme.Hom.id_preimage]

namespace Scheme.Modules

/-- A relation `m|_V = ρ • m'|_V` between sections over `U` and `U'` restricts to `W ⊆ V`. -/
lemma presheaf_map_homOfLE_eq_smul_of_le {X : Scheme.{u}} {M : X.Modules} {U U' V W : X.Opens}
    (h : V ≤ U) (h' : V ≤ U') (hW : W ≤ V) {m : Γ(M, U)} {m' : Γ(M, U')} {ρ : Γ(X, V)}
    (H : M.presheaf.map (homOfLE h).op m = ρ • M.presheaf.map (homOfLE h').op m') :
    M.presheaf.map (homOfLE (hW.trans h)).op m =
      X.presheaf.map (homOfLE hW).op ρ • M.presheaf.map (homOfLE (hW.trans h')).op m' := by
  rw [← presheaf_map_homOfLE_map_homOfLE h hW, H, map_smul, presheaf_map_homOfLE_map_homOfLE]

/-- **Cocycle relation.** If `m₁ = a • m₃`, `m₂ = b • m₃` and `m₁ = d • m₂` on suitable opens,
then `a = d * b` on any smaller open `T` on which `m₃` is a free generator. -/
lemma presheaf_map_eq_mul_of_smul_eq {X : Scheme.{u}} {M : X.Modules}
    {U₁ U₂ U₃ A B D T : X.Opens} {m₁ : Γ(M, U₁)} {m₂ : Γ(M, U₂)} {m₃ : Γ(M, U₃)}
    (hA₁ : A ≤ U₁) (hA₃ : A ≤ U₃) (hB₂ : B ≤ U₂) (hB₃ : B ≤ U₃) (hD₁ : D ≤ U₁) (hD₂ : D ≤ U₂)
    {a : Γ(X, A)} {b : Γ(X, B)} {d : Γ(X, D)}
    (ha : M.presheaf.map (homOfLE hA₁).op m₁ = a • M.presheaf.map (homOfLE hA₃).op m₃)
    (hb : M.presheaf.map (homOfLE hB₂).op m₂ = b • M.presheaf.map (homOfLE hB₃).op m₃)
    (hd : M.presheaf.map (homOfLE hD₁).op m₁ = d • M.presheaf.map (homOfLE hD₂).op m₂)
    (hTA : T ≤ A) (hTB : T ≤ B) (hTD : T ≤ D)
    (hm₃ : IsFreeGenerator (M.presheaf.map (homOfLE (hTA.trans hA₃)).op m₃)) :
    X.presheaf.map (homOfLE hTA).op a =
      X.presheaf.map (homOfLE hTD).op d * X.presheaf.map (homOfLE hTB).op b := by
  refine hm₃.smul_left_injective ?_
  dsimp only
  rw [← presheaf_map_homOfLE_eq_smul_of_le hA₁ hA₃ hTA ha, mul_smul,
    ← presheaf_map_homOfLE_eq_smul_of_le hB₂ hB₃ hTB hb,
    ← presheaf_map_homOfLE_eq_smul_of_le hD₁ hD₂ hTD hd]

/-- A relation `m|_{U''} = ρ • m'|_{U''}` pulls back along `g` to the relation
`g^* m = g^♯ ρ • g^* m'` on any open `V ⊆ g⁻¹ U''`. -/
lemma pullbackSection_map_eq_appLE_smul {X Y : Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    {U U' U'' : Y.Opens} (h : U'' ≤ U) (h' : U'' ≤ U') {m : Γ(M, U)} {m' : Γ(M, U')}
    {ρ : Γ(Y, U'')}
    (H : M.presheaf.map (homOfLE h).op m = ρ • M.presheaf.map (homOfLE h').op m')
    {V : X.Opens} (hV : V ≤ g ⁻¹ᵁ U'') :
    ((pullback g).obj M).presheaf.map (homOfLE (hV.trans (g.preimage_mono h))).op
        (pullbackSection g m) =
      g.appLE U'' V hV ρ • ((pullback g).obj M).presheaf.map
        (homOfLE (hV.trans (g.preimage_mono h'))).op (pullbackSection g m') := by
  have H' := congrArg (pullbackSection g) H
  rw [pullbackSection_map, pullbackSection_smul, pullbackSection_map] at H'
  have H'' := congrArg (((pullback g).obj M).presheaf.map (homOfLE hV).op) H'
  rw [map_smul, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at H''
  exact H''

end Scheme.Modules

open Scheme.Modules in
/-- **Gluing rigidified pullbacks.** Let `X` be an integral scheme over `S` with `Γ(S, ⊤)` a
field, `π : Y ⟶ X` with two sections `σp`, `σq`, and `M` an `𝒪_Y`-module which is trivial over
`π⁻¹ V` for the members `V` of an open cover of `X`. If for every affine open `W ⊆ X` the
pullbacks along `σp` and `σq` of every unit over `π⁻¹ W` differ by a constant of `Γ(S, ⊤)`, then
`σp^* M ≅ σq^* M`. -/
theorem nonempty_iso_pullback_of_appLE_eq_mul {X Y S : Scheme.{u}} [IsIntegral X] (π : Y ⟶ X)
    {σp σq : X ⟶ Y} (hp : σp ≫ π = 𝟙 X) (hq : σq ≫ π = 𝟙 X) (sX : X ⟶ S)
    (hS : IsField Γ(S, ⊤)) (M : Y.Modules)
    (hM : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ e : Γ(M, π ⁻¹ᵁ V), IsFreeGenerator e)
    (hu : ∀ W : X.Opens, IsAffineOpen W → ∀ u : Γ(Y, π ⁻¹ᵁ W)ˣ, ∃ c : Γ(S, ⊤),
      σp.appLE _ W (le_preimage_preimage_of_comp_eq_id hp W) u.1 =
        sX.appLE ⊤ W le_top c * σq.appLE _ W (le_preimage_preimage_of_comp_eq_id hq W) u.1) :
    Nonempty ((Scheme.Modules.pullback σp).obj M ≅ (Scheme.Modules.pullback σq).obj M) := by
  have hle := le_preimage_preimage_of_comp_eq_id hp
  have hle' := le_preimage_preimage_of_comp_eq_id hq
  choose V hxV E hE using hM
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  have hW (x : X) : ∃ W : X.Opens, IsAffineOpen W ∧ (W : Set X).Nonempty ∧ W ≤ V x ⊓ V x₀ := by
    obtain ⟨z, hz, hz₀⟩ := nonempty_preirreducible_inter (V x).isOpen (V x₀).isOpen
      ⟨x, hxV x⟩ ⟨x₀, hxV x₀⟩
    obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := z)
      (U := V x ⊓ V x₀) ⟨hz, hz₀⟩
    exact ⟨W, hW, ⟨z, hzW⟩, hWV⟩
  choose W hWa hWne hWV using hW
  choose u hu' using fun x ↦ ((hE x₀).map (π.preimage_mono ((hWV x).trans inf_le_right)))
    |>.exists_unit_smul_eq ((hE x).map (π.preimage_mono ((hWV x).trans inf_le_left)))
  choose c hc using fun x ↦ hu (W x) (hWa x) (u x)
  have hcu (x : X) : IsUnit (c x) := by
    have h1 : IsUnit (sX.appLE ⊤ (W x) le_top (c x)) :=
      isUnit_of_mul_isUnit_left (hc x ▸ (u x).isUnit.map _)
    have := (hWne x).to_subtype
    have h0 : c x ≠ 0 := by
      rintro h0
      rw [h0, map_zero] at h1
      exact not_isUnit_zero h1
    obtain ⟨d, hd⟩ := hS.mul_inv_cancel h0
    exact IsUnit.of_mul_eq_one _ hd
  choose w hw using fun i j ↦ ((hE j).map (π.preimage_mono (inf_le_right : V i ⊓ V j ≤ _)))
    |>.exists_unit_smul_eq ((hE i).map (π.preimage_mono (inf_le_left : V i ⊓ V j ≤ _)))
  have key (i j : X) (O : X.Opens) (hO : O ≤ V i ⊓ V j) :
      sX.appLE ⊤ O le_top (c i) * σq.appLE _ O (hO.trans (hle' _)) (w i j).1 =
        σp.appLE _ O (hO.trans (hle _)) (w i j).1 * sX.appLE ⊤ O le_top (c j) := by
    by_cases hne : (O : Set X).Nonempty
    swap
    · have : Subsingleton Γ(X, O) := CommRingCat.subsingleton_of_isTerminal
        (X.sheaf.isTerminalOfEqEmpty (eq_bot_iff.mpr fun x hx ↦ hne ⟨x, hx⟩))
      exact Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter O.isOpen (W i).isOpen hne (hWne i)
    have hT : ((O ⊓ W i ⊓ W j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (O ⊓ W i).isOpen (W j).isOpen ⟨z, hz⟩ (hWne j)
    have hTO : O ⊓ W i ⊓ W j ≤ O := inf_le_left.trans inf_le_left
    have hTi : O ⊓ W i ⊓ W j ≤ W i := inf_le_left.trans inf_le_right
    have hTj : O ⊓ W i ⊓ W j ≤ W j := inf_le_right
    refine map_injective_of_isIntegral X (homOfLE hTO) (H := ⟨⟨hT.some, hT.some_mem⟩⟩) ?_
    simp only [map_mul, Scheme.Hom.appLE_map_apply]
    have hcoc := presheaf_map_eq_mul_of_smul_eq (ha := hu' i) (hb := hu' j) (hd := hw i j)
      (hTA := π.preimage_mono hTi) (hTB := π.preimage_mono hTj)
      (hTD := π.preimage_mono (hTO.trans hO)) (hm₃ := (hE x₀).map _)
    have hP := congrArg (σp.appLE _ _ (hle (O ⊓ W i ⊓ W j))) hcoc
    have hQ := congrArg (σq.appLE _ _ (hle' (O ⊓ W i ⊓ W j))) hcoc
    have hci := congrArg (X.presheaf.map (homOfLE hTi).op) (hc i)
    have hcj := congrArg (X.presheaf.map (homOfLE hTj).op) (hc j)
    simp only [map_mul, Scheme.Hom.map_appLE_apply, Scheme.Hom.appLE_map_apply] at hP hQ hci hcj
    refine ((u j).isUnit.map (σq.appLE _ _ (hTj.trans (hle' _))).hom).mul_right_cancel ?_
    linear_combination (-sX.appLE ⊤ _ le_top (c i)) * hQ - hci + hP +
      σp.appLE _ _ (hTO.trans (hO.trans (hle _))) (w i j).1 * hcj
  let e (i : X) : Γ((Scheme.Modules.pullback σp).obj M, V i) :=
    ((Scheme.Modules.pullback σp).obj M).presheaf.map (homOfLE (hle (V i))).op
      (pullbackSection σp (E i))
  let g (i : X) : Γ((Scheme.Modules.pullback σq).obj M, V i) :=
    sX.appLE ⊤ (V i) le_top (c i) • ((Scheme.Modules.pullback σq).obj M).presheaf.map
      (homOfLE (hle' (V i))).op (pullbackSection σq (E i))
  refine nonempty_iso_of_isFreeGenerator (e := e) (f := g)
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)
    (fun i ↦ ((hE i).pullback_unit_app σp).map _) (fun i j O hi hj a b hab ↦ ?_)
    fun i ↦ (((hE i).pullback_unit_app σq).map _).units_smul
      ((hcu i).map (sX.appLE ⊤ (V i) le_top).hom).unit
  have hO := le_inf hi hj
  simp only [e, g, Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE,
    Scheme.Hom.appLE_map_apply] at hab ⊢
  rw [pullbackSection_map_eq_appLE_smul σp (π.preimage_mono inf_le_left)
    (π.preimage_mono inf_le_right) (hw i j) (hO.trans (hle _))] at hab
  rw [pullbackSection_map_eq_appLE_smul σq (π.preimage_mono inf_le_left)
    (π.preimage_mono inf_le_right) (hw i j) (hO.trans (hle' _))]
  have hab' : a * σp.appLE _ O (hO.trans (hle _)) (w i j).1 = b := by
    refine (((hE j).pullback_unit_app σp).map (hj.trans (hle _))).smul_left_injective ?_
    dsimp only
    rw [mul_smul]
    exact hab
  rw [← hab']
  simp only [smul_smul]
  congr 1
  linear_combination a * key i j O hO

/-- **Rigidity of invertible modules over an open of the affine line** (Stacks 0BEH, for a basic
open `D(f)` of the affine line). Let `k` be an algebraically closed field, `X` an integral
`k`-scheme whose local rings are unique factorization domains, and `p`, `q` two `k`-points of
`D(f) = Spec k[t]_f`. For every invertible module `ℒ` on `X ×_k D(f)`, the pullbacks of `ℒ` along
the sections `X ⟶ X ×_k D(f)` at `p` and at `q` are isomorphic. -/
@[stacks 0BEH]
theorem nonempty_iso_pullback_lift_of_isAlgClosed [IsAlgClosed k] (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (sX : X ⟶ Spec (.of k))
    (f : k[X]) (p q : Spec (.of k) ⟶ Spec (.of (Localization.Away f)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) = 𝟙 _)
    (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))) = 𝟙 _)
    (M : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away f))))).Modules)
    [M.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 X) (sX ≫ p) (by simp [hp]))).obj M ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 X) (sX ≫ q) (by simp [hq]))).obj M) := by
  have hf : f ≠ 0 := by
    have h0 := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f
    rintro rfl
    rw [map_zero, isUnit_zero_iff] at h0
    have := subsingleton_of_zero_eq_one h0
    obtain ⟨pt⟩ : Nonempty (Spec (.of k)) := inferInstance
    exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr this).false (p pt)
  refine nonempty_iso_pullback_of_appLE_eq_mul (pullback.fst _ _) (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) sX
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k))
    M (fun x ↦ ?_)
    fun W hW u ↦ exists_appLE_lift_eq_mul sX hf p q hp hq hW u
  obtain ⟨V, -, hx, e, he⟩ := exists_isFreeGenerator_preimage_fst hX sX hf M x
  exact ⟨V, hx, e, he⟩

end AlgebraicGeometry
