import Langlands.Algebra.UnitCocycleLocalUnitsProof
import Langlands.Algebra.SemilocalUnitProduct
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Trivialising unit cocycles over a semilocal base -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra.Semilocal

section Core

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The `R`-submodule of `S` of elements `m` with `u * (m ⊗ 1) = 1 ⊗ m`. -/
def cocycleSubmodule (u : S ⊗[R] S) : Submodule R S where
  carrier := {m | u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m}
  add_mem' {m n} hm hn := by
    simp only [Set.mem_ofPred_eq] at hm hn ⊢
    rw [TensorProduct.add_tmul, mul_add, hm, hn, TensorProduct.tmul_add]
  zero_mem' := by simp
  smul_mem' r m hm := by
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [← TensorProduct.smul_tmul', mul_smul_comm, hm, TensorProduct.tmul_smul]

theorem mem_cocycleSubmodule {u : S ⊗[R] S} {m : S} :
    m ∈ cocycleSubmodule u ↔ u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m :=
  Iff.rfl

/-- Over a faithfully flat algebra `S` of a ring `R` with finitely many maximal ideals, every
unit cocycle `u` in `S ⊗[R] S` is a coboundary: `u * (m ⊗ 1) = 1 ⊗ m` for a unit `m` of `S`. -/
theorem exists_isUnit_of_unitCocycle [Module.FaithfullyFlat R S] [Finite (MaximalSpectrum R)]
    (u v : S ⊗[R] S) (huv : u * v = 1)
    (hcoc : Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) u =
      (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) u) :
    ∃ m : S, IsUnit m ∧ u * (m ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] m := by
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have heff := (Algebra.IsEffective.of_faithfullyFlat R S).eqLocus_includeLeft_includeRight
  have hprod : ∀ m ∈ cocycleSubmodule u, ∀ m' ∈ cocycleSubmodule v,
      ∃ r : R, algebraMap R S r = m * m' := by
    intro m hm m' hm'
    rw [mem_cocycleSubmodule] at hm hm'
    have h2 : (m * m') ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (m * m') :=
      calc (m * m') ⊗ₜ[R] (1 : S) = (u * v) * ((m ⊗ₜ[R] (1 : S)) * (m' ⊗ₜ[R] (1 : S))) := by
            rw [huv, one_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        _ = (u * (m ⊗ₜ[R] (1 : S))) * (v * (m' ⊗ₜ[R] (1 : S))) := by ring
        _ = (1 : S) ⊗ₜ[R] (m * m') := by
            rw [hm, hm', Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hmem : m * m' ∈ Set.range (algebraMap R S) := by
      rw [← heff]
      exact h2
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr⟩
  have hspan := Langlands.Algebra.unitCocycleLocalUnits R S u v huv hcoc
  have hspan' : Ideal.span {r : R | ∃ m ∈ cocycleSubmodule u, ∃ m' ∈ cocycleSubmodule v,
      algebraMap R S r = m * m'} = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Ideal.span_mono ?_
    rintro r ⟨m, m', hm, hm', hr⟩
    exact ⟨m, hm, m', hm', hr⟩
  obtain ⟨m, hm, m', -, r, hr, hrm⟩ :=
    exists_isUnit_of_span_eq_top hinj _ _ hprod hspan'
  refine ⟨m, ?_, hm⟩
  obtain ⟨w, hw⟩ := hr.map (algebraMap R S)
  refine IsUnit.of_mul_eq_one (m' * ↑w⁻¹) ?_
  rw [← mul_assoc, ← hrm, ← hw, Units.mul_inv]

end Core

section Weil

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
  {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

section Generic

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S]
  [IsScalarTower k R S]

/-- For a `k`-algebra map `β : B → R` and an `R`-algebra `T`, the multiplication map
`B ⊗[k] T → T`, `b ⊗ t ↦ β(b) t`. -/
def mulMap (β : B →ₐ[k] R) (T : Type u) [CommRing T] [Algebra k T] [Algebra R T]
    [IsScalarTower k R T] : B ⊗[k] T →ₐ[k] T :=
  Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom k R T).comp β) (AlgHom.id k T)

theorem mulMap_tmul (β : B →ₐ[k] R) (T : Type u) [CommRing T] [Algebra k T] [Algebra R T]
    [IsScalarTower k R T] (b : B) (t : T) :
    mulMap β T (b ⊗ₜ[k] t) = algebraMap R T (β b) * t :=
  rfl

/-- `mulMap` commutes with `R`-algebra homomorphisms. -/
theorem mulMap_naturality (β : B →ₐ[k] R) {T T' : Type u} [CommRing T] [Algebra k T]
    [Algebra R T] [IsScalarTower k R T] [CommRing T'] [Algebra k T'] [Algebra R T']
    [IsScalarTower k R T'] (f : T →ₐ[R] T') (x : B ⊗[k] T) :
    f (mulMap β T x) =
      mulMap β T' (Algebra.TensorProduct.map (AlgHom.id k B) (f.restrictScalars k) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b t => simp [mulMap_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A family of `(B ⊗[k] T)ˣ`-valued cocycles indexed by pairs of `k`-algebra maps `L → T`
that agree on `K`, natural in `T` and multiplicative under concatenation, is a coboundary of
a single unit of `B ⊗[k] L`, given a faithfully flat cover `S` of a ring `R` with finitely many
maximal ideals, together with maps `β : B → R`, `j : L → S`, `θ : S → B ⊗[k] L` satisfying
the compatibilities below. -/
theorem exists_unit_coboundary_of_cover [Module.FaithfullyFlat R S]
    [Finite (MaximalSpectrum R)]
    (β : B →ₐ[k] R) (j : L →ₐ[k] S) (θ : S →ₐ[k] B ⊗[k] L)
    (hj : ∀ x : K, ∃ r : R, algebraMap R S r = j (algebraMap K L x))
    (hθj : ∀ l : L, θ (j l) = 1 ⊗ₜ[k] l)
    (hθβ : ∀ b : B, θ (algebraMap R S (β b)) = b ⊗ₜ[k] 1)
    (hθR : ∀ r : R, ∃ y : B ⊗[k] K, θ (algebraMap R S r) =
      Algebra.TensorProduct.map (AlgHom.id k B) (IsScalarTower.toAlgHom k K L) y)
    (c : ∀ (T : Type u) [CommRing T] [Algebra k T], (L →ₐ[k] T) → (L →ₐ[k] T) → (B ⊗[k] T)ˣ)
    (hnat : ∀ (T : Type u) [CommRing T] [Algebra k T] (T' : Type u) [CommRing T'] [Algebra k T']
      (φ : T →ₐ[k] T') (a b : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      c T' (φ.comp a) (φ.comp b) =
        Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T')
          (c T a b))
    (hcoc : ∀ (T : Type u) [CommRing T] [Algebra k T] (a b d : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      b.comp (IsScalarTower.toAlgHom k K L) = d.comp (IsScalarTower.toAlgHom k K L) →
      c T a d = c T a b * c T b d) :
    ∃ f : (B ⊗[k] L)ˣ, ∀ (T : Type u) [CommRing T] [Algebra k T] (a b : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      c T a b * Units.map (Algebra.TensorProduct.map (AlgHom.id k B) a : B ⊗[k] L →* B ⊗[k] T) f =
        Units.map (Algebra.TensorProduct.map (AlgHom.id k B) b : B ⊗[k] L →* B ⊗[k] T) f := by
  classical
  let ι := IsScalarTower.toAlgHom k K L
  let pr1 : L →ₐ[k] S ⊗[R] S :=
    ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).restrictScalars k).comp j
  let pr2 : L →ₐ[k] S ⊗[R] S :=
    ((Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).restrictScalars k).comp j
  have hpr : pr1.comp ι = pr2.comp ι := by
    ext x
    obtain ⟨r, hr⟩ := hj x
    simp only [pr1, pr2, ι, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
      IsScalarTower.toAlgHom_apply, ← hr, AlgHom.commutes]
  -- the unit cocycle on the cover
  let u0 : (S ⊗[R] S)ˣ := Units.map (mulMap β (S ⊗[R] S)).toRingHom.toMonoidHom (c _ pr1 pr2)
  have hu0 : ∀ (T : Type u) [CommRing T] [Algebra k T] [Algebra R T] [IsScalarTower k R T]
      (f : S ⊗[R] S →ₐ[R] T),
      f u0 = mulMap β T
        ↑(c T ((f.restrictScalars k).comp pr1) ((f.restrictScalars k).comp pr2)) := by
    intro T _ _ _ _ f
    rw [hnat (S ⊗[R] S) T (f.restrictScalars k) pr1 pr2 hpr, Units.coe_map, Units.coe_map]
    exact mulMap_naturality β f _
  let f13 : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S) :=
    Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight
  let f23 : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S) := Algebra.TensorProduct.includeRight
  let f12 : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S) :=
    Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeLeft
  have h1 : (f13.restrictScalars k).comp pr1 = (f12.restrictScalars k).comp pr1 := by
    ext l
    simp [f13, f12, pr1]
  have h2 : (f23.restrictScalars k).comp pr1 = (f12.restrictScalars k).comp pr2 := by
    ext l
    simp [f23, f12, pr1, pr2]
  have h3 : (f23.restrictScalars k).comp pr2 = (f13.restrictScalars k).comp pr2 := by
    ext l
    simp [f23, f13, pr2]
  have hι12 : ((f12.restrictScalars k).comp pr1).comp ι =
      ((f12.restrictScalars k).comp pr2).comp ι :=
    congrArg (fun g => (f12.restrictScalars k).comp g) hpr
  have hι23 : ((f12.restrictScalars k).comp pr2).comp ι =
      ((f13.restrictScalars k).comp pr2).comp ι := by
    rw [← h2, ← h3]
    exact congrArg (fun g => (f23.restrictScalars k).comp g) hpr
  have hcoc0 : Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) (u0 : S ⊗[R] S) =
      (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) u0 *
        Algebra.TensorProduct.map (AlgHom.id R S)
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) u0 := by
    change f13 (u0 : S ⊗[R] S) = f23 (u0 : S ⊗[R] S) * f12 (u0 : S ⊗[R] S)
    rw [hu0 _ f13, hu0 _ f23, hu0 _ f12, h1, h3, h2,
      hcoc _ _ ((f12.restrictScalars k).comp pr2) _ hι12 hι23, Units.val_mul, map_mul, mul_comm]
  obtain ⟨m, hmu, hm⟩ :=
    exists_isUnit_of_unitCocycle (u0 : S ⊗[R] S) (↑u0⁻¹ : S ⊗[R] S) u0.mul_inv hcoc0
  refine ⟨(hmu.map θ).unit, ?_⟩
  intro T _ _ a b hab
  have hab' : ∀ r : R, Algebra.TensorProduct.map (AlgHom.id k B) a (θ (algebraMap R S r)) =
      Algebra.TensorProduct.map (AlgHom.id k B) b (θ (algebraMap R S r)) := by
    intro r
    obtain ⟨y, hy⟩ := hθR r
    rw [hy, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
      ← Algebra.TensorProduct.map_comp, hab]
  let A' : S →ₐ[k] B ⊗[k] T := (Algebra.TensorProduct.map (AlgHom.id k B) a).comp θ
  let B' : S →ₐ[k] B ⊗[k] T := (Algebra.TensorProduct.map (AlgHom.id k B) b).comp θ
  let _ : Algebra R (B ⊗[k] T) := (A'.toRingHom.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower k R (B ⊗[k] T) := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k (B ⊗[k] T) x = A' (algebraMap R S (algebraMap k R x))
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes])
  let A'' : S →ₐ[R] B ⊗[k] T := { A'.toRingHom with commutes' := fun _ => rfl }
  let B'' : S →ₐ[R] B ⊗[k] T := { B'.toRingHom with commutes' := fun r => (hab' r).symm }
  let ψ : S ⊗[R] S →ₐ[R] B ⊗[k] T :=
    Algebra.TensorProduct.lift A'' B'' (fun _ _ => Commute.all _ _)
  have hψ1 : (ψ.restrictScalars k).comp pr1 =
      (Algebra.TensorProduct.includeRight : T →ₐ[k] B ⊗[k] T).comp a := by
    ext l
    simp [ψ, pr1, A'', A', hθj]
  have hψ2 : (ψ.restrictScalars k).comp pr2 =
      (Algebra.TensorProduct.includeRight : T →ₐ[k] B ⊗[k] T).comp b := by
    ext l
    simp [ψ, pr2, B'', B', hθj]
  have hmul : ∀ x : B ⊗[k] T, mulMap β (B ⊗[k] T)
      (Algebra.TensorProduct.map (AlgHom.id k B) Algebra.TensorProduct.includeRight x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b' t =>
      rw [Algebra.TensorProduct.map_tmul, mulMap_tmul]
      change A' (algebraMap R S (β b')) * _ = _
      simp [A', hθβ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have key : ψ (u0 : S ⊗[R] S) = (c T a b : B ⊗[k] T) := by
    rw [hu0 (B ⊗[k] T) ψ, hψ1, hψ2,
      hnat T (B ⊗[k] T) Algebra.TensorProduct.includeRight a b hab, Units.coe_map]
    exact hmul _
  have h := congrArg ψ hm
  rw [map_mul, key] at h
  ext
  simp only [Units.val_mul, Units.coe_map, IsUnit.unit_spec]
  simpa [ψ, A'', B'', A', B'] using h

end Generic

variable (k B K L) in
/-- The inclusion `L → (K ⊗[k] B) ⊗[K] L`. -/
def coverIncl : L →ₐ[k] (K ⊗[k] B) ⊗[K] L :=
  (Algebra.TensorProduct.includeRight : L →ₐ[K] (K ⊗[k] B) ⊗[K] L).restrictScalars k

theorem coverIncl_apply (l : L) : coverIncl k B K L l = (1 : K ⊗[k] B) ⊗ₜ[K] l :=
  rfl

variable (k B K L) in
/-- The comparison map `(K ⊗[k] B) ⊗[K] L → B ⊗[k] L`, `(κ ⊗ b) ⊗ l ↦ b ⊗ κ l`. -/
def coverMap : (K ⊗[k] B) ⊗[K] L →ₐ[k] B ⊗[k] L :=
  (Algebra.TensorProduct.comm k L B).toAlgHom.comp
    ((Algebra.TensorProduct.lift
      (Algebra.TensorProduct.map (Algebra.ofId K L) (AlgHom.id k B))
      (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[k] B)
      (fun _ _ => Commute.all _ _)).restrictScalars k)

theorem coverMap_tmul (κ : K) (b : B) (l : L) :
    coverMap k B K L ((κ ⊗ₜ[k] b) ⊗ₜ[K] l) = b ⊗ₜ[k] (algebraMap K L κ * l) := by
  simp [coverMap]

theorem coverMap_coverIncl (l : L) : coverMap k B K L (coverIncl k B K L l) = 1 ⊗ₜ[k] l := by
  rw [coverIncl_apply, Algebra.TensorProduct.one_def, coverMap_tmul, map_one, one_mul]

theorem coverMap_algebraMap (κ : K) (b : B) :
    coverMap k B K L (algebraMap (K ⊗[k] B) ((K ⊗[k] B) ⊗[K] L) (κ ⊗ₜ[k] b)) =
      b ⊗ₜ[k] algebraMap K L κ := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    coverMap_tmul, mul_one]

/-- A family of `(B ⊗[k] T)ˣ`-valued cocycles indexed by pairs of `k`-algebra maps `L → T`
that agree on `K`, natural in `T` and multiplicative under concatenation, is a coboundary of
a single unit of `B ⊗[k] L`, provided `B` is finite over `k`. -/
theorem exists_unit_coboundary [Module.Finite k B]
    (c : ∀ (T : Type u) [CommRing T] [Algebra k T], (L →ₐ[k] T) → (L →ₐ[k] T) → (B ⊗[k] T)ˣ)
    (hnat : ∀ (T : Type u) [CommRing T] [Algebra k T] (T' : Type u) [CommRing T'] [Algebra k T']
      (φ : T →ₐ[k] T') (a b : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      c T' (φ.comp a) (φ.comp b) =
        Units.map (Algebra.TensorProduct.map (AlgHom.id k B) φ : B ⊗[k] T →* B ⊗[k] T')
          (c T a b))
    (hcoc : ∀ (T : Type u) [CommRing T] [Algebra k T] (a b d : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      b.comp (IsScalarTower.toAlgHom k K L) = d.comp (IsScalarTower.toAlgHom k K L) →
      c T a d = c T a b * c T b d) :
    ∃ f : (B ⊗[k] L)ˣ, ∀ (T : Type u) [CommRing T] [Algebra k T] (a b : L →ₐ[k] T),
      a.comp (IsScalarTower.toAlgHom k K L) = b.comp (IsScalarTower.toAlgHom k K L) →
      c T a b * Units.map (Algebra.TensorProduct.map (AlgHom.id k B) a : B ⊗[k] L →* B ⊗[k] T) f =
        Units.map (Algebra.TensorProduct.map (AlgHom.id k B) b : B ⊗[k] L →* B ⊗[k] T) f := by
  have : IsArtinianRing (K ⊗[k] B) := IsArtinianRing.of_finite K _
  refine exists_unit_coboundary_of_cover (K := K) (R := K ⊗[k] B) (S := (K ⊗[k] B) ⊗[K] L)
    Algebra.TensorProduct.includeRight (coverIncl k B K L) (coverMap k B K L) ?_
    coverMap_coverIncl ?_ ?_ c hnat hcoc
  · intro x
    refine ⟨algebraMap K (K ⊗[k] B) x, ?_⟩
    rw [coverIncl_apply, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes x).symm
  · intro b
    rw [Algebra.TensorProduct.includeRight_apply, coverMap_algebraMap, map_one]
  · intro r
    induction r using TensorProduct.inductionOn with
    | tmul κ b =>
      refine ⟨b ⊗ₜ[k] κ, ?_⟩
      rw [coverMap_algebraMap, Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hy
      exact ⟨y1 + y2, by rw [map_add, map_add, h1, h2, map_add]⟩

end Weil

end Langlands.Algebra.Semilocal
