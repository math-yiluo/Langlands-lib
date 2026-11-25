import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.PermutationLattice
import Langlands.GaloisCohomology.Global.Units.SUnits
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Units
import Langlands.Global.Arithmetic.SUnitIndex
import Langlands.Global.AdelicFunctoriality.Finite
import Langlands.ClassFieldTheory.Global.FullLogLatticeRepresentations

/-!
# The `S`-units as a Galois lattice

Let `L / K` be a finite Galois extension of number fields with group `Γ`, `S` a finite set of finite
places of `K` and `S_L` the places of `L` above `S`. For an additive function `d` on finite
`𝔽_ℓ[Γ]`-modules, extended to finitely generated `ℤ[Γ]`-modules by `g(A) = d(A/ℓ) - d(A[ℓ])`
(`Local.AdditiveFunction.g`), this file computes
`g(𝒪_{L,S}ˣ) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)` (`g_sUnitsOf`).

The proof is Tate's. For the units: `𝒪_Lˣ/torsion ⊕ ℤ` is the augmented logarithmic lattice of the
library's class field theory (`fullLogIntegralSplit`), a `Γ`-stable full lattice in `ℝ^{∞_L}`, as is
`ℤ^{∞_L}`; two such lattices are related by an injective `Γ`-map with finite cokernel
(`Langlands.Cohomology.Herbrand.exists_injective_finite_coker_of_isZLattice`), on which `g` does not change
(`g_units`). For the `S`-units: the valuations at the places of `S_L` give the exact sequence
`1 → 𝒪_Lˣ → 𝒪_{L,S}ˣ → ℤ^{S_L}` with finite cokernel (`SUnitIndex`), equivariant for the action of
`Γ` on the places by transport of structure (`finitePlaceAction` of
`Langlands.Galois.RestrictedRamification.Unramified`, through `finitePlaceEquiv`).
-/

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain CategoryTheory Langlands.GaloisCohomology.Local
open Langlands.ClassFieldTheory.Global Langlands.Global.AdelicFunctoriality Langlands.Galois
open Langlands.Global.Arithmetic.SUnitIndex

universe u

noncomputable section

section Finiteness

variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) [NeZero n]

/-- `A/n` is finite for a finitely generated abelian group `A`. -/
theorem finite_modN_of_moduleFinite : Finite (ModN A n) := by
  apply Module.finite_of_fg_torsion
  intro y
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (n : ℤ) • (Submodule.Quotient.mk a : ModN A n) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, rfl⟩

/-- `A[n]` is finite for a finitely generated abelian group `A`. -/
theorem finite_torsN_of_moduleFinite : Finite (TorsN A n) := by
  have : Module.Finite ℤ (TorsN A n) :=
    Module.Finite.of_injective (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).subtype
      Subtype.val_injective
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  apply Subtype.ext
  change (n : ℤ) • (x : A) = 0
  rw [natCast_zsmul]
  exact (mem_ker_lsmul_iff n (x : A)).1 x.2

end Finiteness

namespace Local.AdditiveFunction

variable {l : ℕ} [NeZero l] {Γ : Type*} [Group Γ] (d : AdditiveFunction.{u} l Γ)

/-- `g` only depends on the `Γ`-module up to isomorphism. -/
theorem g_congr {A B : Type u} [AddCommGroup A] [AddCommGroup B] [DistribMulAction Γ A]
    [DistribMulAction Γ B] [Module.Finite ℤ A] (e : A ≃+ B)
    (he : ∀ (γ : Γ) (a : A), e (γ • a) = γ • e a) : d.g A = d.g B := by
  have := finite_modN_of_moduleFinite (A := A) l
  have := finite_torsN_of_moduleFinite (A := A) l
  have : Finite (A ⧸ (e.symm.toAddMonoidHom).range) :=
    Finite.of_surjective (fun _ : Unit => (0 : A ⧸ (e.symm.toAddMonoidHom).range)) fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H a => exact ⟨(), ((QuotientAddGroup.eq_zero_iff a).2
          (AddMonoidHom.mem_range.2 ⟨e a, e.symm_apply_apply a⟩)).symm⟩
  exact d.g_eq_of_finite_cokernel' e.symm.toAddMonoidHom (fun γ b => by
    apply e.injective
    change e (e.symm (γ • b)) = e (γ • e.symm b)
    rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]) e.symm.injective

/-- `g` does not see a finite kernel. -/
theorem g_eq_of_surjective_of_finite_ker {B C : Type u} [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ B] [DistribMulAction Γ C] [Module.Finite ℤ C] (p : B →+ C)
    (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b) (hp : Function.Surjective p) [Finite p.ker] :
    d.g B = d.g C := by
  have hK : ∀ (γ : Γ) (b : B), b ∈ p.ker → γ • b ∈ p.ker := fun γ b hb => by
    rw [AddMonoidHom.mem_ker] at hb ⊢
    rw [hpγ, hb, smul_zero]
  let _ := subgroupDistribMulAction p.ker hK
  have := finite_modN_of_moduleFinite (A := C) l
  have := finite_torsN_of_moduleFinite (A := C) l
  rw [d.g_add p.ker.subtype p (fun _ _ => rfl) hpγ p.ker.subtype_injective
      (fun y => by simp) hp, d.g_eq_zero_of_finite p.ker, zero_add]

/-- **Additivity with a finite cokernel.** For `0 → A → B → C` exact with `C/B` finite, `A` and `C`
finitely generated: `g(B) = g(A) + g(C)`. -/
theorem g_eq_add_of_exact_of_finite_cokernel {A B C : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C] (f : A →+ B) (p : B →+ C)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hpγ : ∀ (γ : Γ) (b : B), p (γ • b) = γ • p b)
    (hf : Function.Injective f) (hfp : Function.Exact f p) [Finite (C ⧸ p.range)] :
    d.g B = d.g A + d.g C := by
  have hR : ∀ (γ : Γ) (c : C), c ∈ p.range → γ • c ∈ p.range := by
    rintro γ _ ⟨b, rfl⟩
    exact ⟨γ • b, hpγ γ b⟩
  let _ := subgroupDistribMulAction p.range hR
  have : Module.Finite ℤ p.range :=
    Module.Finite.of_injective p.range.subtype.toIntLinearMap Subtype.val_injective
  have := finite_modN_of_moduleFinite (A := A) l
  have := finite_torsN_of_moduleFinite (A := A) l
  have := finite_modN_of_moduleFinite (A := p.range) l
  have := finite_torsN_of_moduleFinite (A := p.range) l
  have : Finite (C ⧸ p.range.subtype.range) := by
    rw [AddSubgroup.range_subtype]
    infer_instance
  rw [d.g_add f p.rangeRestrict hfγ (fun γ b => Subtype.ext (hpγ γ b)) hf
      (fun y => by
        rw [← hfp y]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
      p.rangeRestrict_surjective,
    d.g_eq_of_finite_cokernel p.range.subtype (fun _ _ => rfl) p.range.subtype_injective]

end Local.AdditiveFunction

/-- A group of linear automorphisms as a distributive action. -/
abbrev distribMulActionOfAut {Γ A : Type*} [Group Γ] [AddCommGroup A]
    (φ : Γ →* (A ≃ₗ[ℤ] A)) : DistribMulAction Γ A where
  smul γ a := φ γ a
  one_smul a := by
    change φ 1 a = a
    rw [map_one]
    rfl
  mul_smul γ δ a := by
    change φ (γ * δ) a = φ γ (φ δ a)
    rw [map_mul]
    rfl
  smul_zero γ := map_zero (φ γ)
  smul_add γ := map_add (φ γ)

section Units

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {ℓ : ℕ} [NeZero ℓ] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L))

attribute [local instance] unitsModuloTorsionAction Units.mulDistribMulActionRight

local instance : AddCommGroup (Additive ((𝓞 L)ˣ ⧸ NumberField.Units.torsion L)) :=
  inferInstance

omit [NumberField K] in
/-- **The units.** `g(𝒪_Lˣ) = d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)`. -/
theorem g_units :
    d.g (Additive (𝓞 L)ˣ) =
      d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) -
        d.one := by
  -- units modulo torsion
  let p : Additive (𝓞 L)ˣ →+ Additive ((𝓞 L)ˣ ⧸ NumberField.Units.torsion L) :=
    (QuotientGroup.mk' (NumberField.Units.torsion L)).toAdditive
  have hp : Function.Surjective p := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion L) y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  have : Finite p.ker := by
    have hker : ∀ x : Additive (𝓞 L)ˣ, x ∈ p.ker ↔ x.toMul ∈ NumberField.Units.torsion L :=
      fun x => by
        rw [AddMonoidHom.mem_ker]
        change (QuotientGroup.mk x.toMul : (𝓞 L)ˣ ⧸ NumberField.Units.torsion L) = 1 ↔ _
        rw [QuotientGroup.eq_one_iff]
    exact Finite.of_injective (β := NumberField.Units.torsion L)
      (fun x => ⟨(x : Additive (𝓞 L)ˣ).toMul, (hker x).1 x.2⟩) fun x y h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Additive.toMul.injective h)
  have : Module.Finite ℤ (Additive ((𝓞 L)ˣ ⧸ NumberField.Units.torsion L)) :=
    Module.Finite.of_surjective (AddMonoidHom.toIntLinearMap p) hp
  have h1 := d.g_eq_of_surjective_of_finite_ker p (fun _ _ => rfl) hp
  -- the logarithmic lattice
  let _ : DistribMulAction (L ≃ₐ[K] L) (fullLogUnitLattice L) :=
    distribMulActionOfAut (fullLogUnitLatticeAut K L)
  have h2 := d.g_congr (fullLogEmbeddingEquiv L).toAddEquiv
    (fun γ x => fullLogEmbeddingEquiv_equivariant K L γ x)
  -- the augmented lattice
  let _ : DistribMulAction (L ≃ₐ[K] L) (augmentedFullLogUnitLattice L) :=
    distribMulActionOfAut (augmentedFullLogUnitLatticeAut K L)
  let _ := trivialIntAction.{u} (L ≃ₐ[K] L)
  have : Module.Finite ℤ (fullLogUnitLattice L) :=
    Module.Finite.of_injective (fullLogEmbeddingEquiv L).symm.toLinearMap
      (fullLogEmbeddingEquiv L).symm.injective
  have := finite_modN_of_moduleFinite (A := fullLogUnitLattice L) ℓ
  have := finite_torsN_of_moduleFinite (A := fullLogUnitLattice L) ℓ
  have := finite_modN_uliftInt.{u} ℓ
  have := finite_torsN_uliftInt.{u} ℓ
  let f : fullLogUnitLattice L →+ augmentedFullLogUnitLattice L :=
    ((fullLogIntegralSplit L).symm.toLinearMap.comp (LinearMap.inl ℤ _ ℤ)).toAddMonoidHom
  let h : augmentedFullLogUnitLattice L →+ ULift.{u} ℤ :=
    { toFun := fun x => ULift.up (fullLogIntegralSplit L x).2
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add]; rfl }
  have h3 := d.g_add f h (fun γ x => by
      change (fullLogIntegralSplit L).symm (fullLogUnitLatticeAut K L γ x, 0) =
        augmentedFullLogUnitLatticeAut K L γ ((fullLogIntegralSplit L).symm (x, 0))
      apply (fullLogIntegralSplit L).injective
      rw [LinearEquiv.apply_symm_apply, fullLogIntegralSplit_equivariant,
        LinearEquiv.apply_symm_apply])
    (fun γ x => by
      change ULift.up (fullLogIntegralSplit L (augmentedFullLogUnitLatticeAut K L γ x)).2 =
        ULift.up (fullLogIntegralSplit L x).2
      rw [fullLogIntegralSplit_equivariant])
    (fun x y hxy => by
      have := congrArg (fun z => (fullLogIntegralSplit L z).1) hxy
      simpa [f] using this)
    (fun y => by
      constructor
      · intro hy
        refine ⟨(fullLogIntegralSplit L y).1, ?_⟩
        apply (fullLogIntegralSplit L).injective
        have hy' : (fullLogIntegralSplit L y).2 = 0 := congrArg ULift.down hy
        change fullLogIntegralSplit L ((fullLogIntegralSplit L).symm ((fullLogIntegralSplit L y).1, 0)) = _
        rw [LinearEquiv.apply_symm_apply, ← hy']
      · rintro ⟨x, rfl⟩
        change ULift.up (fullLogIntegralSplit L ((fullLogIntegralSplit L).symm (x, 0))).2 = 0
        rw [LinearEquiv.apply_symm_apply]
        rfl)
    (fun t => ⟨(fullLogIntegralSplit L).symm (0, t.down), by
      change ULift.up (fullLogIntegralSplit L ((fullLogIntegralSplit L).symm (0, t.down))).2 = t
      rw [LinearEquiv.apply_symm_apply]⟩)
  have h4 := d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ => rfl) AddEquiv.ulift
  -- comparison with the coordinate lattice
  let A := augmentedFullLogUnitLatticeRepresentation.{u, u} K L
  let B := infinitePlaceCoordinateLatticeRepresentation.{u, u} K L
  obtain ⟨φ, hφ, hfin⟩ := Langlands.Cohomology.Herbrand.exists_injective_finite_coker_of_isZLattice
    (A := A) (B := B) (fun γ => (fullLogPermutation K L γ).toLinearMap)
    (augmentedFullLogUnitLattice L) (infinitePlaceCoordinateLattice L)
    (AddEquiv.refl _) (AddEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)
  let _ : DistribMulAction (L ≃ₐ[K] L) (infinitePlaceCoordinateLattice L) :=
    distribMulActionOfAut (infinitePlaceCoordinateLatticeAut K L)
  have : Module.Finite ℤ (infinitePlaceCoordinateLattice L) :=
    Module.Finite.of_injective (infinitePlaceCoordinateIntegerEquiv L).toLinearMap
      (infinitePlaceCoordinateIntegerEquiv L).injective
  have := finite_modN_of_moduleFinite (A := infinitePlaceCoordinateLattice L) ℓ
  have := finite_torsN_of_moduleFinite (A := infinitePlaceCoordinateLattice L) ℓ
  let φ' : augmentedFullLogUnitLattice L →+ infinitePlaceCoordinateLattice L :=
    φ.hom.toLinearMap.toAddMonoidHom
  have : Finite (infinitePlaceCoordinateLattice L ⧸ φ'.range) := hfin
  have h5 := d.g_eq_of_finite_cokernel' φ' (fun γ x => Rep.hom_comm_apply φ γ x) hφ
  -- the coordinate lattice is the permutation lattice
  let _ := funPermAction (L ≃ₐ[K] L) (InfinitePlace L) ℤ
  have h6 := d.g_congr (infinitePlaceCoordinateIntegerEquiv L).toAddEquiv (fun γ x => by
    funext w
    apply Int.cast_injective (α := ℝ)
    change ((infinitePlaceCoordinateIntegerEquiv L (infinitePlaceCoordinateLatticeAut K L γ x) w : ℤ) :
      ℝ) = ((infinitePlaceCoordinateIntegerEquiv L x (γ⁻¹ • w) : ℤ) : ℝ)
    rw [infinitePlaceCoordinateIntegerEquiv_cast, infinitePlaceCoordinateIntegerEquiv_cast,
      infinitePlaceCoordinateLatticeAut_apply, fullLogPermutation_apply])
  have h7 := d.g_funPermAction (InfinitePlace L)
  rw [h1, h2]
  linarith

end Units

section SUnits

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The Galois action on the `S`-units of `L`, written additively. -/
abbrev sUnitsOfAction : DistribMulAction (L ≃ₐ[K] L) (Additive (sUnitsOf S L)) where
  smul σ x := Additive.ofMul (sUnitsAction S L σ x.toMul)
  one_smul x := by
    change Additive.ofMul (sUnitsAction S L 1 x.toMul) = x
    rw [map_one]
    rfl
  mul_smul σ τ x := by
    change Additive.ofMul (sUnitsAction S L (σ * τ) x.toMul) =
      Additive.ofMul (sUnitsAction S L σ (sUnitsAction S L τ x.toMul))
    rw [map_mul]
    rfl
  smul_zero σ := congrArg Additive.ofMul (map_one (sUnitsAction S L σ))
  smul_add σ x y := congrArg Additive.ofMul (map_mul (sUnitsAction S L σ) x.toMul y.toMul)

omit [NumberField L] in
theorem coe_toMul_sUnitsOfAction_smul (σ : L ≃ₐ[K] L) (x : Additive (sUnitsOf S L)) :
    (letI := sUnitsOfAction (K := K) (L := L) S;
      (((σ • x).toMul : Lˣ) : L)) = σ ((x.toMul : Lˣ) : L) :=
  rfl

variable [Finite S] {ℓ : ℕ} [NeZero ℓ] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L))

attribute [local instance] Units.mulDistribMulActionRight

/-- **The `S`-units.** `g(𝒪_{L,S}ˣ) = d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)`. -/
theorem g_sUnitsOf :
    letI := sUnitsOfAction (K := K) (L := L) S
    haveI : Finite (finitePlacesAbove L S) :=
      (finite_finitePlacesAbove (L := L) (Set.toFinite S)).to_subtype
    d.g (Additive (sUnitsOf S L)) =
      d.toFun (finitePlacesAbove L S → ZMod ℓ)
          (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (finitePlacesAbove L S)) +
        d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) -
          d.one := by
  classical
  let := sUnitsOfAction (K := K) (L := L) S
  have hfin := finite_finitePlacesAbove (L := L) (Set.toFinite S)
  have : Finite (finitePlacesAbove L S) := hfin.to_subtype
  let T : Finset (HeightOneSpectrum (𝓞 L)) := hfin.toFinset
  have hT : ∀ w, w ∈ T ↔ w ∈ finitePlacesAbove L S := fun w => Set.Finite.mem_toFinset hfin
  have hsub : sUnits L T = sUnitsOf S L := by
    ext x
    rw [mem_sUnitsOf_iff_mem_unit]
    change x ∈ ((T : Set (HeightOneSpectrum (𝓞 L)))).unit L ↔ _
    rw [show ((T : Set (HeightOneSpectrum (𝓞 L)))) = finitePlacesAbove L S from
        Set.Finite.coe_toFinset hfin]
  let e₁ : sUnits L T ≃* sUnitsOf S L := MulEquiv.subgroupCongr hsub
  have he₁ : ∀ y : sUnits L T, ((e₁ y : Lˣ)) = (y : Lˣ) := fun _ => rfl
  let ι : Additive (𝓞 L)ˣ →+ Additive (sUnitsOf S L) :=
    (e₁.toMonoidHom.comp (unitsToSUnits L T)).toAdditive
  let jT : finitePlacesAbove L S → T := fun w => ⟨w.1, (hT w.1).2 w.2⟩
  have hjT : Function.Surjective jT := fun t => ⟨⟨t.1, (hT t.1).1 t.2⟩, rfl⟩
  let v : Additive (sUnitsOf S L) →+ (finitePlacesAbove L S → ℤ) :=
    { toFun := fun x w => Multiplicative.toAdd (valuationVector L T (e₁.symm x.toMul) (jT w))
      map_zero' := by
        funext w
        simp
      map_add' := fun x y => by
        funext w
        simp }
  have hv : ∀ x w, v x w = Multiplicative.toAdd (w.1.valuationOfNeZero ((x.toMul : sUnitsOf S L) : Lˣ)) :=
    fun _ _ => rfl
  -- exactness
  have hexact : Function.Exact ι v := by
    intro y
    constructor
    · intro hy
      have hmem : e₁.symm y.toMul ∈ (valuationVector L T).ker := by
        rw [MonoidHom.mem_ker]
        funext t
        obtain ⟨w, rfl⟩ := hjT t
        exact congrArg Multiplicative.ofAdd (congrFun hy w)
      rw [← range_unitsToSUnits] at hmem
      obtain ⟨u, hu⟩ := hmem
      refine ⟨Additive.ofMul u, ?_⟩
      change Additive.ofMul (e₁ (unitsToSUnits L T u)) = y
      rw [hu, MulEquiv.apply_symm_apply]
      rfl
    · rintro ⟨u, rfl⟩
      funext w
      change Multiplicative.toAdd (valuationVector L T (e₁.symm (e₁ (unitsToSUnits L T u))) (jT w)) = 0
      rw [MulEquiv.symm_apply_apply]
      have h1 : unitsToSUnits L T u ∈ (valuationVector L T).ker := by
        rw [← range_unitsToSUnits]
        exact ⟨u, rfl⟩
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  have hι : Function.Injective ι := fun a b h =>
    Additive.toMul.injective (unitsToSUnits_injective L T (e₁.injective (congrArg Additive.toMul h)))
  -- the cokernel is finite
  let φ : Additive (T → Multiplicative ℤ) ≃+ (finitePlacesAbove L S → ℤ) :=
    { toFun := fun f w => Multiplicative.toAdd (f.toMul (jT w))
      invFun := fun c => Additive.ofMul fun t => Multiplicative.ofAdd (c ⟨t.1, (hT t.1).1 t.2⟩)
      left_inv := fun f => by
        apply Additive.toMul.injective
        funext t
        rfl
      right_inv := fun c => by
        funext w
        rfl
      map_add' := fun f g => by
        funext w
        rfl }
  have hrange : v.range = (Subgroup.toAddSubgroup (valuationVector L T).range).map
      (φ : Additive (T → Multiplicative ℤ) →+ (finitePlacesAbove L S → ℤ)) := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Additive.ofMul (valuationVector L T (e₁.symm x.toMul)), ⟨e₁.symm x.toMul, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx⟩, rfl⟩
      refine ⟨Additive.ofMul (e₁ x), ?_⟩
      funext w
      change Multiplicative.toAdd (valuationVector L T (e₁.symm (e₁ x)) (jT w)) = _
      rw [MulEquiv.symm_apply_apply, hx]
      rfl
  have hidx : v.range.index ≠ 0 := by
    rw [hrange, AddSubgroup.index_map_equiv, Subgroup.index_toAddSubgroup]
    exact index_range_valuationVector_ne_zero L T
  have : v.range.FiniteIndex := ⟨hidx⟩
  -- equivariance
  let _ := funPermAction (L ≃ₐ[K] L) (finitePlacesAbove L S) ℤ
  have hιγ : ∀ (γ : L ≃ₐ[K] L) (a : Additive (𝓞 L)ˣ), ι (γ • a) = γ • ι a := fun γ a => by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  have hvγ : ∀ (γ : L ≃ₐ[K] L) (x : Additive (sUnitsOf S L)), v (γ • x) = γ • v x := fun γ x => by
    funext w
    change v (γ • x) w = v x (γ⁻¹ • w)
    rw [hv, hv]
    congr 1
    apply WithZero.coe_injective
    rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq,
      coe_toMul_sUnitsOfAction_smul]
    have h := valuation_smul_finitePlace γ (γ⁻¹ • (w : HeightOneSpectrum (𝓞 L)))
      (((x.toMul : sUnitsOf S L) : Lˣ) : L)
    rw [smul_inv_smul] at h
    exact h
  have key := d.g_eq_add_of_exact_of_finite_cokernel ι v hιγ hvγ hι hexact
  rw [key, g_units, d.g_funPermAction (finitePlacesAbove L S)]
  ring

end SUnits

end

end Langlands.GaloisCohomology
