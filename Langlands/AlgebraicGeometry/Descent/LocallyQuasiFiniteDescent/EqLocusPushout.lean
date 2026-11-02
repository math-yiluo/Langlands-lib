import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.RingHom.Flat

/-! # Flat base change of an equalizer of two ring maps -/

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

set_option backward.isDefEq.respectTransparency false in
/-- Let `r : R → A` be flat and `a : A → C` a ring map. Suppose `D` is the pushout
`C ⊗[R] A` with coprojections `i₁` and `s`, that `E` is the pushout `D ⊗[R] A` with
coprojections `e₁` and `e₂`, and that `i₂ : C → D` and `q₁ q₂ : D → E` are ring maps
with `q_j ∘ i₁ = e₁ ∘ i_j`, `q_j ∘ s = e₂`, `i₂ ∘ a = s` and `q₁ ∘ i₂ = q₂ ∘ i₂`. If `i₂` is
injective, then `C` is the base change along `r` of the equalizer `B = {c | i₁ c = i₂ c}`. -/
theorem isPushout_eqLocus_of_flat {R A C D E : Type u} [CommRing R] [CommRing A]
    [CommRing C] [CommRing D] [CommRing E]
    (r : R →+* A) (hr : r.Flat) (a : A →+* C) (i₁ i₂ : C →+* D) (s : A →+* D)
    (h₁ : IsPushout (CommRingCat.ofHom (a.comp r)) (CommRingCat.ofHom r)
      (CommRingCat.ofHom i₁) (CommRingCat.ofHom s))
    (e₁ : D →+* E) (e₂ : A →+* E)
    (hE : IsPushout (CommRingCat.ofHom (s.comp r)) (CommRingCat.ofHom r)
      (CommRingCat.ofHom e₁) (CommRingCat.ofHom e₂))
    (q₁ q₂ : D →+* E) (hq₁ : q₁.comp i₁ = e₁.comp i₁) (hq₂ : q₂.comp i₁ = e₁.comp i₂)
    (hs₁ : q₁.comp s = e₂) (hs₂ : q₂.comp s = e₂)
    (ha : i₂.comp a = s) (hcoc : q₁.comp i₂ = q₂.comp i₂) (hinj : Function.Injective i₂)
    (hmem : ∀ x : R, a (r x) ∈ i₁.eqLocus i₂) :
    IsPushout (CommRingCat.ofHom ((a.comp r).codRestrict _ hmem)) (CommRingCat.ofHom r)
      (CommRingCat.ofHom (i₁.eqLocus i₂).subtype) (CommRingCat.ofHom a) := by
  classical
  let B := i₁.eqLocus i₂
  have hw₁ : ∀ x, i₁ (a (r x)) = s (r x) := fun x => by
    simpa using congrArg (fun f => f.hom x) h₁.w
  have hwE : ∀ x, e₁ (s (r x)) = e₂ (r x) := fun x => by
    simpa using congrArg (fun f => f.hom x) hE.w
  have ha' : ∀ x, i₂ (a x) = s x := fun x => congrArg (fun f => f x) ha
  -- Algebra structures for the first pushout.
  let : Algebra R A := r.toAlgebra
  have : Module.Flat R A := hr
  let : Algebra A C := a.toAlgebra
  let : Algebra R C := (a.comp r).toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra C D := i₁.toAlgebra
  let : Algebra A D := s.toAlgebra
  let : Algebra R D := (s.comp r).toAlgebra
  have : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq (fun x => (hw₁ x).symm)
  have : Algebra.IsPushout R C A D := CommRingCat.isPushout_iff_isPushout.mp h₁
  let ψ : C ⊗[R] A ≃ₐ[C] D := Algebra.IsPushout.equiv R C A D
  have hψ : ∀ (c : C) (x : A), ψ (c ⊗ₜ x) = i₁ c * s x := fun c x =>
    Algebra.IsPushout.equiv_tmul R C A D c x
  -- Algebra structures for the second pushout.
  let : Algebra D E := e₁.toAlgebra
  let : Algebra A E := e₂.toAlgebra
  let : Algebra R E := (e₂.comp r).toAlgebra
  have : IsScalarTower R A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R D E := IsScalarTower.of_algebraMap_eq (fun x => (hwE x).symm)
  have : Algebra.IsPushout R D A E := CommRingCat.isPushout_iff_isPushout.mp hE
  let χ : D ⊗[R] A ≃ₐ[D] E := Algebra.IsPushout.equiv R D A E
  have hχ : ∀ (d : D) (x : A), χ (d ⊗ₜ x) = e₁ d * e₂ x := fun d x =>
    Algebra.IsPushout.equiv_tmul R D A E d x
  -- The relevant `R`-linear maps.
  let I₁ : C →ₗ[R] D := (IsScalarTower.toAlgHom R C D).toLinearMap
  let I₂ : C →ₗ[R] D :=
    { toFun := i₂
      map_add' := i₂.map_add
      map_smul' := fun x c => by
        change i₂ (a (r x) * c) = s (r x) * i₂ c
        rw [map_mul, ha'] }
  let : Algebra R B := ((a.comp r).codRestrict _ hmem).toAlgebra
  let ι : B →ₗ[R] C :=
    { toFun := fun b => (b : C)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hex0 : Function.Exact ι (I₁ - I₂) := by
    intro c
    constructor
    · intro h
      refine ⟨⟨c, ?_⟩, rfl⟩
      exact sub_eq_zero.mp h
    · rintro ⟨b, rfl⟩
      exact sub_eq_zero.mpr b.2
  have hex := Module.Flat.rTensor_exact A hex0
  have hιinj : Function.Injective (ι.rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι Subtype.val_injective
  -- The multiplication map `B ⊗[R] A → C`.
  let : Algebra B C := B.subtype.toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let m : B ⊗[R] A →ₐ[B] C :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId B C) (IsScalarTower.toAlgHom R A C)
  have hm : ∀ (b : B) (x : A), m (b ⊗ₜ x) = (b : C) * a x := fun _ _ => rfl
  have key₁ : ∀ z : B ⊗[R] A, i₂ (m z) = ψ (ι.rTensor A z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      rw [hm, LinearMap.rTensor_tmul, hψ, map_mul, ha']
      congr 1
      exact b.2.symm
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  have key₂ : ∀ y : C ⊗[R] A,
      χ (((I₁ - I₂).rTensor A) y) = q₁ (ψ y) - q₂ (ψ y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul c x =>
      rw [LinearMap.rTensor_tmul, hψ, hχ, map_mul, map_mul]
      have h1 : q₁ (i₁ c) = e₁ (i₁ c) := congrArg (fun f => f c) hq₁
      have h2 : q₂ (i₁ c) = e₁ (i₂ c) := congrArg (fun f => f c) hq₂
      have h3 : q₁ (s x) = e₂ x := congrArg (fun f => f x) hs₁
      have h4 : q₂ (s x) = e₂ x := congrArg (fun f => f x) hs₂
      rw [h1, h2, h3, h4, ← sub_mul, ← map_sub]
      rfl
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add, map_add]; abel
  have hminj : Function.Injective m := by
    intro z z' h
    apply hιinj
    apply ψ.injective
    rw [← key₁, ← key₁, h]
  have hmsurj : Function.Surjective m := by
    intro c
    let y : C ⊗[R] A := ψ.symm (i₂ c)
    have hy : ψ y = i₂ c := ψ.apply_symm_apply _
    have hzero : ((I₁ - I₂).rTensor A) y = 0 := by
      apply χ.injective
      rw [key₂, hy, map_zero]
      exact sub_eq_zero.mpr (congrArg (fun f => f c) hcoc)
    obtain ⟨z, hz⟩ := (hex y).mp hzero
    refine ⟨z, hinj ?_⟩
    rw [key₁, hz, hy]
  have hbc : IsBaseChange B (IsScalarTower.toAlgHom R A C).toLinearMap := by
    refine IsBaseChange.of_equiv (LinearEquiv.ofBijective m.toLinearMap ⟨hminj, hmsurj⟩) ?_
    intro x
    change m (1 ⊗ₜ x) = a x
    rw [hm]
    simp
  have : Algebra.IsPushout R B A C := ⟨hbc⟩
  exact CommRingCat.isPushout_iff_isPushout.mpr inferInstance

/-- `CommRingCat` form of `isPushout_eqLocus_of_flat`: the equalizer `B` of `i₁` and `i₂`
is a subring of `C` through which `R → C` factors, and `C` is the base change of `B`
along `r`. -/
theorem exists_isPushout_eqLocus {R A C D E : CommRingCat.{u}} (r : R ⟶ A) (hr : r.hom.Flat)
    (a : A ⟶ C) (i₁ i₂ : C ⟶ D) (s : A ⟶ D) (h₁ : IsPushout (r ≫ a) r i₁ s)
    (e₁ : D ⟶ E) (e₂ : A ⟶ E) (hE : IsPushout (r ≫ s) r e₁ e₂) (q₁ q₂ : D ⟶ E)
    (hq₁ : i₁ ≫ q₁ = i₁ ≫ e₁) (hq₂ : i₁ ≫ q₂ = i₂ ≫ e₁) (hs₁ : s ≫ q₁ = e₂)
    (hs₂ : s ≫ q₂ = e₂) (ha : a ≫ i₂ = s) (hcoc : i₂ ≫ q₁ = i₂ ≫ q₂)
    (hinj : Function.Injective i₂.hom) :
    ∃ (B : CommRingCat.{u}) (rB : R ⟶ B) (ι : B ⟶ C),
      IsPushout rB r ι a ∧ ι ≫ i₁ = ι ≫ i₂ := by
  have hmem : ∀ x : R, a.hom (r.hom x) ∈ i₁.hom.eqLocus i₂.hom := by
    intro x
    change i₁.hom (a.hom (r.hom x)) = i₂.hom (a.hom (r.hom x))
    have h1 : i₁.hom (a.hom (r.hom x)) = s.hom (r.hom x) :=
      congrArg (fun f => f.hom x) h₁.w
    have h2 : i₂.hom (a.hom (r.hom x)) = s.hom (r.hom x) :=
      congrArg (fun f => f.hom (r.hom x)) ha
    rw [h1, h2]
  refine ⟨CommRingCat.of (i₁.hom.eqLocus i₂.hom),
    CommRingCat.ofHom ((a.hom.comp r.hom).codRestrict _ hmem),
    CommRingCat.ofHom (i₁.hom.eqLocus i₂.hom).subtype, ?_, ?_⟩
  · exact isPushout_eqLocus_of_flat r.hom hr a.hom i₁.hom i₂.hom s.hom h₁ e₁.hom e₂.hom hE
      q₁.hom q₂.hom (congrArg CommRingCat.Hom.hom hq₁) (congrArg CommRingCat.Hom.hom hq₂)
      (congrArg CommRingCat.Hom.hom hs₁) (congrArg CommRingCat.Hom.hom hs₂)
      (congrArg CommRingCat.Hom.hom ha) (congrArg CommRingCat.Hom.hom hcoc) hinj hmem
  · ext b
    exact b.2

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
