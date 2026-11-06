import Langlands.GroupScheme.Torus.CharacterPullbackAnnihilator
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual quotient characters from finite-index coroot comparison -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- Characters annihilating a specified subset of coroots, with their full
integral pairings retained. -/
def corootAnnihilator (P : RootDatum J X Y) (s : Set J) : Submodule ℤ X :=
  ⨅ i : s, (P.toLinearMap.flip (P.coroot i)).ker

@[simp]
theorem mem_corootAnnihilator (P : RootDatum J X Y) (s : Set J) (x : X) :
    x ∈ corootAnnihilator P s ↔ ∀ i ∈ s, P.toLinearMap x (P.coroot i) = 0 := by
  simp only [corootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.flip_apply, Subtype.forall]

end Langlands.RootDatum

namespace Langlands.GroupScheme.characterLattice

variable {k : Type u} [Field k]
    {S T Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {J : Type v} {K : Type w}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (R : RootDatum K (characterLattice S) (cocharacterLattice S))
    (s : Set J) (f : T ⟶ Q) (φ : S ⟶ T)

/-- Exactness of the actual cocharacter sequence and finite coroot index in
the subgroup torus turn a coroot-span comparison into a saturated kernel span. -/
theorem cocharacterKernel_saturated_coroot_span
    [Finite (cocharacterLattice S ⧸ R.corootSpan ℤ)]
    (hexact : ∀ ν : cocharacterLattice T,
      ν ≫ f = 0 ↔ ∃ η : cocharacterLattice S, η ≫ φ = ν)
    (hmap : (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' s)) :
    (∀ i ∈ s, P.coroot i ≫ f = 0) ∧
      (∀ ν : cocharacterLattice T, ν ≫ f = 0 →
        ∃ m : ℤ, m ≠ 0 ∧ m • ν ∈ Submodule.span ℤ (P.coroot '' s)) := by
  constructor
  · intro i hi
    have hc : P.coroot i ∈ Submodule.span ℤ (P.coroot '' s) :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    rw [← hmap] at hc
    obtain ⟨η, _, hη⟩ := hc
    exact (hexact _).mpr ⟨η, hη⟩
  · intro ν hν
    obtain ⟨η, hη⟩ := (hexact ν).mp hν
    obtain ⟨m, hm, hmη⟩ :=
      (isOfFinAddOrder_of_finite ((R.corootSpan ℤ).mkQ η)).exists_nsmul_eq_zero
    have hmultiple : (m : ℤ) • η ∈ R.corootSpan ℤ := by
      apply (Submodule.Quotient.mk_eq_zero (R.corootSpan ℤ)).mp
      change (R.corootSpan ℤ).mkQ ((m : ℤ) • η) = 0
      rw [map_zsmul, natCast_zsmul]
      exact hmη
    refine ⟨m, Int.natCast_ne_zero.mpr hm.ne', ?_⟩
    rw [← hmap]
    refine ⟨(m : ℤ) • η, hmultiple, ?_⟩
    rw [map_smul]
    exact congrArg (fun z => (m : ℤ) • z) hη

/-- Actual quotient character pullback has precisely the specified coroot
annihilator as its image, under actual exactness and finite-index comparison. -/
theorem mem_range_precompose_iff_corootComparison
    [(latticePairing Q).IsPerfPair]
    [Finite (cocharacterLattice S ⧸ R.corootSpan ℤ)]
    (hP : P.toLinearMap = latticePairing T)
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    (hexact : ∀ ν : cocharacterLattice T,
      ν ≫ f = 0 ↔ ∃ η : cocharacterLattice S, η ≫ φ = ν)
    (hmap : (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' s))
    (χ : characterLattice T) :
    χ ∈ (precompose f).toIntLinearMap.range ↔
      χ ∈ Langlands.RootDatum.corootAnnihilator P s := by
  let : (latticePairing T).IsPerfPair := hP ▸ inferInstance
  obtain ⟨hkill, hspan⟩ := cocharacterKernel_saturated_coroot_span P R s f φ hexact hmap
  let c : s → cocharacterLattice T := fun i => P.coroot i
  have hc : Set.range c = P.coroot '' s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [mem_range_precompose_iff_of_saturated_span f hf c
    (fun i => hkill i i.property)
    (fun ν hν => by simpa only [hc] using hspan ν hν) χ]
  rw [Langlands.RootDatum.mem_corootAnnihilator]
  simp only [c, ← hP, Subtype.forall]

/-- The actual character lattice of a quotient is identified with a chosen
coroot annihilator using finite index, rather than integral coroot generation. -/
def corootAnnihilatorEquivOfComparison
    [(latticePairing Q).IsPerfPair]
    [Finite (cocharacterLattice S ⧸ R.corootSpan ℤ)]
    (hP : P.toLinearMap = latticePairing T)
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    (hexact : ∀ ν : cocharacterLattice T,
      ν ≫ f = 0 ↔ ∃ η : cocharacterLattice S, η ≫ φ = ν)
    (hmap : (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' s)) :
    characterLattice Q ≃ₗ[ℤ] Langlands.RootDatum.corootAnnihilator P s :=
  LinearEquiv.ofBijective
    ((precompose f).toIntLinearMap.codRestrict
      (Langlands.RootDatum.corootAnnihilator P s)
      (fun χ => (mem_range_precompose_iff_corootComparison P R s f φ
        hP hf hexact hmap _).mp ⟨χ, rfl⟩))
    ⟨fun χ ψ h => precompose_injective_of_cocharacter_surjective f hf
      (congrArg Subtype.val h),
      fun χ => by
        obtain ⟨ψ, hψ⟩ := (mem_range_precompose_iff_corootComparison P R s f φ
          hP hf hexact hmap _).mpr χ.property
        exact ⟨ψ, Subtype.ext hψ⟩⟩

@[simp]
theorem corootAnnihilatorEquivOfComparison_val
    [(latticePairing Q).IsPerfPair]
    [Finite (cocharacterLattice S ⧸ R.corootSpan ℤ)]
    (hP : P.toLinearMap = latticePairing T)
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f))
    (hexact : ∀ ν : cocharacterLattice T,
      ν ≫ f = 0 ↔ ∃ η : cocharacterLattice S, η ≫ φ = ν)
    (hmap : (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' s))
    (χ : characterLattice Q) :
    (corootAnnihilatorEquivOfComparison P R s f φ hP hf hexact hmap χ).val = f ≫ χ :=
  rfl

end Langlands.GroupScheme.characterLattice
