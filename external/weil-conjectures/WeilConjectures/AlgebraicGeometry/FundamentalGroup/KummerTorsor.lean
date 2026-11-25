/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Kummer torsors

Let `X` be a scheme on which `n` is invertible, `ζ` a global `n`-th root of unity and `f` a
global unit. The scheme of `n`-th roots of `f`,
`X ×_{Spec Γ(X)} Spec Γ(X)[T]/(Tⁿ - f)`, with `a ∈ ℤ/n` acting by `T ↦ ζ^a T`, is the *Kummer
cover* of `f` (`AlgebraicGeometry.Scheme.kummerCover`). When the image of `ζ` at a geometric
point is a primitive `n`-th root of unity it is a `ℤ/n`-torsor
(`AlgebraicGeometry.Scheme.EtaleTorsor.kummer`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (n : ℕ) (f : Γ(Y, ⊤))

/-- The Kummer algebra `Γ(X)[T]/(Tⁿ - f)`. -/
abbrev KummerAlgebra : Type u := AdjoinRoot (X ^ n - C f : Γ(Y, ⊤)[X])

/-- The scheme `X ×_{Spec Γ(X)} Spec Γ(X)[T]/(Tⁿ - f)` of `n`-th roots of `f`. -/
noncomputable abbrev kummerCover : Scheme.{u} :=
  pullback Y.toSpecΓ (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))))

/-- The projection of the Kummer cover to `X`. -/
noncomputable abbrev kummerCoverπ : Y.kummerCover n f ⟶ Y :=
  pullback.fst _ _

variable {Y n f} (ζ : Γ(Y, ⊤)) (hζ : ζ ^ n = 1)

include hζ in
lemma kummer_eval_eq_zero (m : ℕ) :
    (X ^ n - C f : Γ(Y, ⊤)[X]).eval₂ (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))
      (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) (ζ ^ m) * AdjoinRoot.root _) = 0 := by
  have hr := AdjoinRoot.eval₂_root (X ^ n - C f : Γ(Y, ⊤)[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at hr ⊢
  rw [mul_pow, ← map_pow, ← pow_mul, mul_comm m n, pow_mul, hζ, one_pow, map_one, one_mul]
  exact hr

/-- The automorphism `T ↦ ζ ^ m T` of the Kummer algebra. -/
noncomputable def kummerAlgHom (m : ℕ) : KummerAlgebra Y n f →ₐ[Γ(Y, ⊤)] KummerAlgebra Y n f :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ (kummer_eval_eq_zero ζ hζ m)

lemma kummerAlgHom_root (m : ℕ) :
    kummerAlgHom ζ hζ m (AdjoinRoot.root _) =
      algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) (ζ ^ m) * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma kummerAlgHom_zero : kummerAlgHom ζ hζ (f := f) 0 = AlgHom.id _ _ :=
  AdjoinRoot.algHom_ext (by simp [kummerAlgHom_root])

lemma kummerAlgHom_add (a b : ℕ) :
    kummerAlgHom ζ hζ (f := f) (a + b) = (kummerAlgHom ζ hζ a).comp (kummerAlgHom ζ hζ b) :=
  AdjoinRoot.algHom_ext (by
    simp only [AlgHom.comp_apply, kummerAlgHom_root, map_mul, AlgHom.commutes, pow_add, map_mul]
    ring)

lemma kummerAlgHom_pow (k m : ℕ) (hζk : (ζ ^ k) ^ n = 1) :
    kummerAlgHom (ζ ^ k) hζk (f := f) m = kummerAlgHom ζ hζ (k * m) :=
  AdjoinRoot.algHom_ext (by simp only [kummerAlgHom_root, ← pow_mul])

lemma kummerAlgHom_mod (m : ℕ) : kummerAlgHom ζ hζ (f := f) (m % n) = kummerAlgHom ζ hζ m :=
  AdjoinRoot.algHom_ext (by
    simp only [kummerAlgHom_root]
    conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hζ, one_pow, mul_one])

/-- **Roots of `f` form a `μₙ`-torsor.** Two ring maps `α, β` from the Kummer algebra to a field
`Ω`, agreeing on `Γ(Y)`, differ by a unique `T ↦ ζ ^ m T`, `m ∈ ℤ / n`, provided `f` is a unit
and the image of `ζ` in `Ω` is a primitive `n`-th root of unity. -/
lemma existsUnique_comp_kummerAlgHom [NeZero n] (hf : IsUnit f) {Ω : Type u} [Field Ω]
    (α β : KummerAlgebra Y n f →+* Ω)
    (hαβ : α.comp (algebraMap Γ(Y, ⊤) _) = β.comp (algebraMap Γ(Y, ⊤) _))
    (hζΩ : IsPrimitiveRoot (α (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) ζ)) n) :
    ∃! m : ZMod n, α.comp (kummerAlgHom ζ hζ m.val).toRingHom = β := by
  set σ := α.comp (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))
  set w := α (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) ζ)
  have hroot (γ : KummerAlgebra Y n f →+* Ω) :
      γ (AdjoinRoot.root _) ^ n = γ (algebraMap _ _ f) := by
    have hr := AdjoinRoot.eval₂_root (X ^ n - C f : Γ(Y, ⊤)[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hr
    rw [← map_pow, hr]
    rfl
  have hfΩ : α (algebraMap _ _ f) ≠ 0 := (hf.map (α.comp (algebraMap _ _))).ne_zero
  set a := α (AdjoinRoot.root _)
  set b := β (AdjoinRoot.root _)
  have hβf : β (algebraMap _ _ f) = α (algebraMap _ _ f) :=
    (RingHom.congr_fun hαβ f).symm
  have ha : a ^ n = α (algebraMap _ _ f) := hroot α
  have hb : b ^ n = α (algebraMap _ _ f) := (hroot β).trans hβf
  have ha0 : a ≠ 0 := fun h ↦ hfΩ (by rw [← ha, h, zero_pow (NeZero.ne n)])
  -- `T ↦ ζ ^ m T` followed by `α` is `β` iff `w ^ m * a = b`
  have hiff (m : ℕ) : α.comp (kummerAlgHom ζ hζ m).toRingHom = β ↔ w ^ m * a = b := by
    constructor
    · intro h
      have := congrArg (fun γ : KummerAlgebra Y n f →+* Ω ↦ γ (AdjoinRoot.root _)) h
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        kummerAlgHom_root, map_mul, map_pow] at this
      exact this
    · intro h
      refine AdjoinRoot.ringHom_ext (RingHom.ext fun r ↦ ?_) ?_
      · change α (kummerAlgHom ζ hζ m (algebraMap _ _ r)) = β (algebraMap _ _ r)
        rw [AlgHom.commutes]
        exact RingHom.congr_fun hαβ r
      · change α (kummerAlgHom ζ hζ m (AdjoinRoot.root _)) = β (AdjoinRoot.root _)
        rw [kummerAlgHom_root, map_mul, map_pow, map_pow]
        exact h
  -- `b / a` is an `n`-th root of unity, hence a power of `w`
  have hu : (b / a) ^ n = 1 := by rw [div_pow, ha, hb, div_self hfΩ]
  obtain ⟨i, hin, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hu
  have hwi : w ^ i * a = b := by rw [hi, div_mul_cancel₀ _ ha0]
  have hmod (k : ℕ) : w ^ (k % n) = w ^ k := by
    conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hζΩ.pow_eq_one, one_pow, mul_one]
  refine ⟨(i : ZMod n), ?_, fun m hm ↦ ?_⟩
  · beta_reduce
    rw [hiff, ZMod.val_natCast, hmod]
    exact hwi
  · beta_reduce at hm
    rw [hiff] at hm
    have hpow : w ^ m.val = w ^ i := mul_right_cancel₀ ha0 (hm.trans hwi.symm)
    rw [← ZMod.natCast_zmod_val m, hζΩ.pow_inj (ZMod.val_lt m) hin hpow]

/-- The map `Γ(Y)[T']/(T'ⁿ - f ^ a) → Γ(Y)[T]/(Tⁿ - f)`, `T' ↦ T ^ a`. -/
noncomputable def kummerPowAlgHom (a : ℕ) :
    KummerAlgebra Y n (f ^ a) →ₐ[Γ(Y, ⊤)] KummerAlgebra Y n f :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (AdjoinRoot.root _ ^ a) (by
    have hr := AdjoinRoot.eval₂_root (X ^ n - C f : Γ(Y, ⊤)[X])
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hr ⊢
    rw [← pow_mul, mul_comm, pow_mul, hr, map_pow]
    rfl)

lemma kummerPowAlgHom_root (a : ℕ) :
    kummerPowAlgHom (n := n) (f := f) a (AdjoinRoot.root _) = AdjoinRoot.root _ ^ a :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma kummerAlgHom_comp_kummerPowAlgHom (a m : ℕ) (hζ' : ζ ^ n = 1) :
    (kummerAlgHom ζ hζ (f := f) m).comp (kummerPowAlgHom a) =
      (kummerPowAlgHom a).comp (kummerAlgHom ζ hζ' (f := f ^ a) (a * m)) :=
  AdjoinRoot.algHom_ext (by
    simp only [AlgHom.comp_apply, kummerPowAlgHom_root, kummerAlgHom_root, map_pow, map_mul,
      AlgHom.commutes, mul_pow, ← pow_mul]
    ring)

section Torsor

variable (n f)

/-- The structure morphism of the Kummer algebra. -/
noncomputable abbrev kummerStructureMap :
    Γ(Y, ⊤) ⟶ CommRingCat.of (KummerAlgebra Y n f) :=
  CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f))

variable {n f}

/-- The action of `m` on the Kummer cover, `T ↦ ζ ^ m T` on the second factor. -/
noncomputable def kummerVadd (m : ℕ) : Y.kummerCover n f ⟶ Y.kummerCover n f :=
  pullback.map _ _ _ _ (𝟙 Y)
    (Spec.map (CommRingCat.ofHom (kummerAlgHom ζ hζ (f := f) m).toRingHom)) (𝟙 _) (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext r
      exact ((kummerAlgHom ζ hζ m).commutes r).symm)

lemma kummerVadd_comp_π (m : ℕ) : kummerVadd ζ hζ (f := f) m ≫ Y.kummerCoverπ n f =
    Y.kummerCoverπ n f := by
  simp [kummerVadd, kummerCoverπ]

lemma kummerVadd_add (a b : ℕ) :
    kummerVadd ζ hζ (f := f) (a + b) = kummerVadd ζ hζ a ≫ kummerVadd ζ hζ b := by
  apply pullback.hom_ext
  · simp [kummerVadd]
  · simp only [kummerVadd, pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, kummerAlgHom_add]
    rfl

lemma kummerVadd_zero : kummerVadd ζ hζ (f := f) 0 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [kummerVadd]
  · simp only [kummerVadd, pullback.lift_snd, Category.id_comp, kummerAlgHom_zero]
    exact (congrArg (pullback.snd _ _ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

lemma kummerVadd_pow (k m : ℕ) (hζk : (ζ ^ k) ^ n = 1) :
    kummerVadd (ζ ^ k) hζk (f := f) m = kummerVadd ζ hζ (k * m) := by
  simp only [kummerVadd, kummerAlgHom_pow ζ hζ k m hζk]

/-- The map `T ↦ T ^ a` from the Kummer cover of `f` to that of `f ^ a`. -/
noncomputable def kummerPowMap (a : ℕ) : Y.kummerCover n f ⟶ Y.kummerCover n (f ^ a) :=
  pullback.map _ _ _ _ (𝟙 Y)
    (Spec.map (CommRingCat.ofHom (kummerPowAlgHom (n := n) (f := f) a).toRingHom)) (𝟙 _)
    (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext r
      exact ((kummerPowAlgHom a).commutes r).symm)

lemma kummerPowMap_comp_π (a : ℕ) :
    kummerPowMap (n := n) (f := f) a ≫ Y.kummerCoverπ n (f ^ a) = Y.kummerCoverπ n f := by
  simp [kummerPowMap, kummerCoverπ]

lemma kummerVadd_comp_kummerPowMap (a m : ℕ) :
    kummerVadd ζ hζ (f := f) m ≫ kummerPowMap a =
      kummerPowMap a ≫ kummerVadd ζ hζ (f := f ^ a) (a * m) := by
  apply pullback.hom_ext
  · simp [kummerVadd, kummerPowMap]
  · simp only [kummerVadd, kummerPowMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp]
    have e₁ : CommRingCat.ofHom (kummerPowAlgHom (n := n) (f := f) a).toRingHom ≫
        CommRingCat.ofHom (kummerAlgHom ζ hζ (f := f) m).toRingHom =
        CommRingCat.ofHom ((kummerAlgHom ζ hζ m).comp (kummerPowAlgHom a)).toRingHom := rfl
    have e₂ : CommRingCat.ofHom (kummerAlgHom ζ hζ (f := f ^ a) (a * m)).toRingHom ≫
        CommRingCat.ofHom (kummerPowAlgHom (n := n) (f := f) a).toRingHom =
        CommRingCat.ofHom ((kummerPowAlgHom a).comp (kummerAlgHom ζ hζ (a * m))).toRingHom := rfl
    rw [e₁, e₂, kummerAlgHom_comp_kummerPowAlgHom ζ hζ a m hζ]

lemma kummerVadd_mod (m : ℕ) : kummerVadd ζ hζ (f := f) (m % n) = kummerVadd ζ hζ m := by
  simp only [kummerVadd, kummerAlgHom_mod]

end Torsor

section Torsor

variable {ζ hζ} [NeZero n] (hn : IsUnit (n : Γ(Y, ⊤))) (hf : IsUnit f)

include hn hf in
lemma etale_kummerStructureMap : Etale (Spec.map (kummerStructureMap (Y := Y) n f)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C (NeZero.ne n) hn hf)

lemma isFinite_kummerStructureMap : IsFinite (Spec.map (kummerStructureMap (Y := Y) n f)) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr (monic_X_pow_sub_C f (NeZero.ne n)).finite_adjoinRoot

lemma surjective_kummerStructureMap : Surjective (Spec.map (kummerStructureMap (Y := Y) n f)) := by
  have hdeg : (X ^ n - C f : Γ(Y, ⊤)[X]).degree ≠ 0 := by
    nontriviality Γ(Y, ⊤)
    rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne n))]
    exact_mod_cast NeZero.ne n
  exact ((flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr
    (AdjoinRoot.faithfullyFlat_of_monic (monic_X_pow_sub_C f (NeZero.ne n)) hdeg))).2

include hn hf in
/-- The Kummer cover as a finite étale `Y`-scheme. -/
noncomputable def kummerFiniteEtale : Y.FiniteEtale :=
  have := etale_kummerStructureMap hn hf
  have := isFinite_kummerStructureMap (Y := Y) (n := n) (f := f)
  ⟨MorphismProperty.Over.mk ⊤ (Y.kummerCoverπ n f) (by
      change Etale (pullback.fst _ _); infer_instance),
    by change IsFinite (pullback.fst _ _); infer_instance⟩

variable (ζ hζ) in
/-- The action of `m ∈ ℕ` on the Kummer cover, as an endomorphism of finite étale schemes. -/
noncomputable def kummerVaddHom (m : ℕ) : kummerFiniteEtale hn hf ⟶ kummerFiniteEtale hn hf :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (kummerVadd ζ hζ m) (kummerVadd_comp_π ζ hζ m))

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The ring map `Γ(Y) → Ω` of a geometric point. -/
noncomputable abbrev pointRingHom : Γ(Y, ⊤) ⟶ CommRingCat.of Ω := Spec.preimage (s ≫ Y.toSpecΓ)

/-- The ring map `Γ(Y)[T]/(Tⁿ - f) → Ω` of a point of the Kummer cover. -/
noncomputable abbrev kummerPointRingHom (x : (FiniteEtale.fiber s).obj (kummerFiniteEtale hn hf)) :
    CommRingCat.of (KummerAlgebra Y n f) ⟶ CommRingCat.of Ω :=
  Spec.preimage (x.left ≫ pullback.snd _ _)

lemma kummerStructureMap_comp_kummerPointRingHom
    (x : (FiniteEtale.fiber s).obj (kummerFiniteEtale hn hf)) :
    kummerStructureMap n f ≫ kummerPointRingHom hn hf s x = pointRingHom s := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc, ← pullback.condition,
    ← Category.assoc]
  congr 1
  exact FiniteEtale.fiber_left_comp s x

lemma fiber_map_kummerVaddHom_eq_iff (m : ℕ)
    (x y : (FiniteEtale.fiber s).obj (kummerFiniteEtale hn hf)) :
    (FiniteEtale.fiber s).map (kummerVaddHom ζ hζ hn hf m) x = y ↔
      (kummerPointRingHom hn hf s x).hom.comp (kummerAlgHom ζ hζ m).toRingHom =
        (kummerPointRingHom hn hf s y).hom := by
  constructor
  · intro h
    have h' := congrArg (fun z ↦ z.left ≫ pullback.snd _ _) h
    simp only [FiniteEtale.fiber_map_left] at h'
    change (x.left ≫ kummerVadd ζ hζ m) ≫ pullback.snd _ _ = y.left ≫ pullback.snd _ _ at h'
    rw [Category.assoc, kummerVadd, pullback.lift_snd, ← Category.assoc,
      ← Spec.map_preimage (x.left ≫ pullback.snd _ _), ← Spec.map_comp,
      ← Spec.map_preimage (y.left ≫ pullback.snd _ _)] at h'
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  · intro h
    apply FiniteEtale.fiber_ext s
    change x.left ≫ kummerVadd ζ hζ m = y.left
    apply pullback.hom_ext
    · rw [Category.assoc]
      change x.left ≫ (kummerVadd ζ hζ m ≫ Y.kummerCoverπ n f) = y.left ≫ Y.kummerCoverπ n f
      rw [kummerVadd_comp_π]
      exact (FiniteEtale.fiber_left_comp s x).trans (FiniteEtale.fiber_left_comp s y).symm
    · rw [Category.assoc, kummerVadd, pullback.lift_snd, ← Category.assoc,
        ← Spec.map_preimage (x.left ≫ pullback.snd _ _), ← Spec.map_comp,
        ← Spec.map_preimage (y.left ≫ pullback.snd _ _)]
      congr 1
      exact CommRingCat.hom_ext h

variable (ζ hζ) [ConnectedSpace Y]

/-- **The Kummer torsor.** The scheme of `n`-th roots of a unit `f`, with `m ∈ ℤ / n` acting by
`T ↦ ζ ^ m T`, is a `ℤ / n`-torsor as soon as the image of `ζ` at a geometric point `s` is a
primitive `n`-th root of unity. -/
noncomputable def EtaleTorsor.kummer (hζs : IsPrimitiveRoot ((pointRingHom s).hom ζ) n) :
    EtaleTorsor (ULift.{u + 1} (ZMod n)) Y where
  P := Y.kummerCover n f
  π := Y.kummerCoverπ n f
  isFinite := (kummerFiniteEtale hn hf).property
  etale := (kummerFiniteEtale hn hf).obj.prop
  surjective := by
    have := surjective_kummerStructureMap (Y := Y) (n := n) (f := f)
    change Surjective (pullback.fst _ _)
    infer_instance
  vadd m := kummerVadd ζ hζ m.down.val
  vadd_π m := kummerVadd_comp_π ζ hζ _
  zero_vadd := by
    change kummerVadd ζ hζ (0 : ZMod n).val = _
    rw [ZMod.val_zero, kummerVadd_zero]
  add_vadd a b := by
    change kummerVadd ζ hζ (a.down + b.down).val = _
    rw [ZMod.val_add, kummerVadd_mod, kummerVadd_add]
  isIso_sigmaDesc := by
    refine FiniteEtale.isIso_sigmaDesc_of_existsUnique s (kummerFiniteEtale hn hf)
      (fun m : ULift.{u + 1} (ZMod n) ↦ kummerVaddHom ζ hζ hn hf m.down.val) fun x y ↦ ?_
    have hx := kummerStructureMap_comp_kummerPointRingHom hn hf s x
    have hy := kummerStructureMap_comp_kummerPointRingHom hn hf s y
    have hαβ : (kummerPointRingHom hn hf s x).hom.comp (algebraMap Γ(Y, ⊤) _) =
        (kummerPointRingHom hn hf s y).hom.comp (algebraMap Γ(Y, ⊤) _) :=
      (congrArg CommRingCat.Hom.hom hx).trans (congrArg CommRingCat.Hom.hom hy).symm
    have hζΩ : IsPrimitiveRoot
        ((kummerPointRingHom hn hf s x).hom (algebraMap Γ(Y, ⊤) (KummerAlgebra Y n f) ζ)) n := by
      have := congrArg (fun g : Γ(Y, ⊤) ⟶ CommRingCat.of Ω ↦ g.hom ζ) hx
      beta_reduce at this
      rw [← this] at hζs
      exact hζs
    obtain ⟨m, hm, huniq⟩ := existsUnique_comp_kummerAlgHom ζ hζ hf _ _ hαβ hζΩ
    refine ⟨⟨m⟩, (fiber_map_kummerVaddHom_eq_iff hn hf s _ x y).2 hm, fun m' h ↦ ?_⟩
    exact ULift.ext (huniq m'.down ((fiber_map_kummerVaddHom_eq_iff hn hf s _ x y).1 h))

section Monodromy

open FiniteEtale PreGaloisCategory

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- If an isomorphism of total spaces over `Y` carries the action of `k * m` on `t` to the action
of `m` on `t'`, then `k • f_{t'} = f_t`. -/
lemma _root_.AlgebraicGeometry.Scheme.EtaleTorsor.mul_monodromy_of_iso
    (t t' : EtaleTorsor (ULift.{u + 1} (ZMod n)) Y) (φ : t.P ≅ t'.P) (hφ : φ.hom ≫ t'.π = t.π)
    (k : ZMod n)
    (hv : ∀ m : ZMod n, t.vadd ⟨k * m⟩ ≫ φ.hom = φ.hom ≫ t'.vadd ⟨m⟩) (g : G) :
    k * (t'.monodromy s G g).toAdd.down = (t.monodromy s G g).toAdd.down := by
  let Φ : t.toFiniteEtale ⟶ t'.toFiniteEtale :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk φ.hom hφ)
  have hinj : Function.Injective ((fiber s).map Φ) := fun a b h ↦ FiniteEtale.fiber_ext s (by
    have := congrArg (fun z ↦ z.left) h
    change a.left ≫ φ.hom = b.left ≫ φ.hom at this
    exact (cancel_mono φ.hom).1 this)
  let x := (t.nonempty_fiber s).some
  set m' := (t'.monodromy s G g).toAdd.down
  have key : t.monodromy s G g = Multiplicative.ofAdd (ULift.up (k * m')) := by
    refine (t.monodromy_eq_iff s G g x _).2 (hinj ?_)
    rw [IsNaturalSMul.naturality, ← t'.fiber_map_vaddHom_monodromy s G g ((fiber s).map Φ x)]
    apply FiniteEtale.fiber_ext s
    change (x.left ≫ t.vadd ⟨k * m'⟩) ≫ φ.hom = (x.left ≫ φ.hom) ≫ t'.vadd ⟨m'⟩
    rw [Category.assoc, Category.assoc, hv m']
  rw [key]
  rfl

/-- If a morphism of total spaces over `Y` carries the action of `m` on `t` to the action of
`k * m` on `t'`, then `f_{t'} = k • f_t`. -/
lemma _root_.AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_eq_mul_of_hom
    (t t' : EtaleTorsor (ULift.{u + 1} (ZMod n)) Y) (φ : t.P ⟶ t'.P) (hφ : φ ≫ t'.π = t.π)
    (k : ZMod n) (hv : ∀ m : ZMod n, t.vadd ⟨m⟩ ≫ φ = φ ≫ t'.vadd ⟨k * m⟩) (g : G) :
    (t'.monodromy s G g).toAdd.down = k * (t.monodromy s G g).toAdd.down := by
  let Φ : t.toFiniteEtale ⟶ t'.toFiniteEtale :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk φ hφ)
  let x := (t.nonempty_fiber s).some
  set m := (t.monodromy s G g).toAdd.down
  have key : t'.monodromy s G g = Multiplicative.ofAdd (ULift.up (k * m)) := by
    refine (t'.monodromy_eq_iff s G g ((fiber s).map Φ x) _).2 ?_
    rw [← IsNaturalSMul.naturality, ← t.fiber_map_vaddHom_monodromy s G g x]
    apply FiniteEtale.fiber_ext s
    change (x.left ≫ φ) ≫ t'.vadd ⟨k * m⟩ = (x.left ≫ t.vadd ⟨m⟩) ≫ φ
    rw [Category.assoc, Category.assoc, hv m]
  rw [key]
  rfl

/-- **Kummer torsors are multiplicative**: `f_{f ^ a} = a • f_f`, via `T ↦ T ^ a`. -/
lemma EtaleTorsor.monodromy_kummer_pow (a : ℕ) (hζs : IsPrimitiveRoot ((pointRingHom s).hom ζ) n)
    (g : G) :
    ((EtaleTorsor.kummer ζ hζ hn (hf.pow a) s hζs).monodromy s G g).toAdd.down =
      (a : ZMod n) * ((EtaleTorsor.kummer ζ hζ hn hf s hζs).monodromy s G g).toAdd.down := by
  refine EtaleTorsor.monodromy_eq_mul_of_hom s G _ _ (kummerPowMap a) (kummerPowMap_comp_π a)
    (a : ZMod n) (fun m ↦ ?_) g
  change kummerVadd ζ hζ m.val ≫ kummerPowMap a =
    kummerPowMap a ≫ kummerVadd ζ hζ ((a : ZMod n) * m).val
  rw [kummerVadd_comp_kummerPowMap, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod,
    kummerVadd_mod]

/-- Replacing `ζ` by `ζ ^ k` divides the monodromy of the Kummer torsor by `k`:
`k • f_{ζ ^ k} = f_ζ`. -/
lemma EtaleTorsor.mul_monodromy_kummer_pow (k : ℕ) (hζk : (ζ ^ k) ^ n = 1)
    (hζs : IsPrimitiveRoot ((pointRingHom s).hom ζ) n)
    (hζks : IsPrimitiveRoot ((pointRingHom s).hom (ζ ^ k)) n) (g : G) :
    (k : ZMod n) * ((EtaleTorsor.kummer (ζ ^ k) hζk hn hf s hζks).monodromy s G g).toAdd.down =
      ((EtaleTorsor.kummer ζ hζ hn hf s hζs).monodromy s G g).toAdd.down := by
  refine EtaleTorsor.mul_monodromy_of_iso s G _ _ (Iso.refl (Y.kummerCover n f))
    (Category.id_comp _) (k : ZMod n) (fun m ↦ ?_) g
  change kummerVadd ζ hζ ((k : ZMod n) * m).val ≫ 𝟙 _ = 𝟙 _ ≫ kummerVadd (ζ ^ k) hζk m.val
  rw [Category.comp_id, Category.id_comp, kummerVadd_pow ζ hζ k _ hζk,
    ← kummerVadd_mod ζ hζ (k * m.val), ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod,
    kummerVadd_mod]

end Monodromy

end Torsor

end AlgebraicGeometry.Scheme
