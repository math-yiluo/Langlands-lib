/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover

/-!
# Lifts of the geometric Frobenius to the étale fundamental group

Let `p : X₀ ⟶ Spec k₀` be a connected scheme over a finite field which is geometrically
connected, `s : Spec Ω ⟶ X₀` a geometric point and `G = π₁(X₀, s)`. Then some element of `G`
acts on the geometric fibre of every constant cover `X₀ ×_{k₀} Spec A` as the geometric
Frobenius (`AlgebraicGeometry.Scheme.FiniteEtale.exists_smul_eq_geometricFrobenius`): the map
`π₁(X₀, s) → Gal(k / k₀)` hits the geometric Frobenius. Consequently the degree map of the Weil
group is surjective (`AlgebraicGeometry.Scheme.FiniteEtale.weilGroupDeg_surjective`).

## Proof

Identify the fibre of `X₀ ×_{k₀} Spec A` with the `k₀`-embeddings `A → Ω`, where `Ω` is a
`k₀`-algebra through `s` (`AlgebraicGeometry.Scheme.FiniteEtale.fiberConstantCoverEquiv`). For a
finite subfield `R` of `Ω` the constant cover `X₀ ×_{k₀} Spec R` is connected, by geometric
connectedness, so `G` acts transitively on its fibre and some `g` moves the inclusion
`R ⊆ Ω` to its image under the geometric Frobenius. Every point of the fibre of a constant cover
whose embedding lands in `R` is the image of this inclusion under a morphism of constant covers,
and the actions of `G` and of the Frobenius commute with those, so `g` acts as the Frobenius on
all of them; this applies to `R` itself since `R / k₀` is normal. The sets of such `g` are closed
and directed, and `G` is compact.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- If `T` intertwines two permutations, it intertwines all their integral powers. -/
lemma _root_.Equiv.Perm.zpow_apply_eq_of_comm {α β : Type*} (T : α → β) (a : Equiv.Perm α)
    (b : Equiv.Perm β) (h : ∀ y, T (a y) = b (T y)) (n : ℤ) (y : α) :
    T ((a ^ n) y) = (b ^ n) (T y) := by
  have hinv (y : α) : T (a⁻¹ y) = b⁻¹ (T y) := by
    rw [Equiv.Perm.eq_inv_iff_eq, ← h]
    simp
  induction n using Int.induction_on generalizing y with
  | zero => simp
  | succ n ih => rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, ih, h,
      Equiv.Perm.mul_apply]
  | pred n ih => rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, ih, hinv,
      Equiv.Perm.mul_apply]

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

/-- The arithmetic Frobenius commutes with morphisms of constant covers, since `k₀`-algebra maps
commute with the `q`-power map. -/
lemma arithmeticFrobenius_hom_comp_constantCoverHom {A B : FiniteEtaleAlgebra K}
    (f : A.1 →ₐ[K] B.1) :
    (arithmeticFrobenius p B).hom ≫ constantCoverHom p f =
      constantCoverHom p f ≫ (arithmeticFrobenius p A).hom := by
  change constantCoverHom p B.frobenius.toAlgHom ≫ constantCoverHom p f =
    constantCoverHom p f ≫ constantCoverHom p A.frobenius.toAlgHom
  rw [← constantCoverHom_comp, ← constantCoverHom_comp]
  congr 1
  ext x
  simp [FiniteEtaleAlgebra.frobenius_apply, map_pow]

/-- The geometric Frobenius commutes with the maps on geometric fibres induced by morphisms of
constant covers. -/
lemma fiber_map_constantCoverHom_geometricFrobenius {A B : FiniteEtaleAlgebra K}
    (f : A.1 →ₐ[K] B.1) (y : (fiber s).obj (constantCover p B)) :
    (fiber s).map (constantCoverHom p f) (geometricFrobenius p s B y) =
      geometricFrobenius p s A ((fiber s).map (constantCoverHom p f) y) := by
  have hinj : Function.Injective ((fiber s).map (arithmeticFrobenius p A).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← arithmeticFrobenius_hom_comp_constantCoverHom, Functor.map_comp,
    ConcreteCategory.comp_apply, fiber_map_arithmeticFrobenius_geometricFrobenius]

variable (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)]

/-- If `g` acts as the geometric Frobenius on a point `y` of the fibre of a constant cover, it
does so on the image of `y` under any morphism of constant covers. -/
lemma smul_fiber_map_eq_geometricFrobenius [IsNaturalSMul (fiber s) G]
    {A B : FiniteEtaleAlgebra K} (f : A.1 →ₐ[K] B.1) (g : G)
    (y : (fiber s).obj (constantCover p B)) (h : g • y = geometricFrobenius p s B y) :
    g • (fiber s).map (constantCoverHom p f) y =
      geometricFrobenius p s A ((fiber s).map (constantCoverHom p f) y) := by
  rw [← IsNaturalSMul.naturality, h, fiber_map_constantCoverHom_geometricFrobenius]

/-- If `g` acts as an integral power of the geometric Frobenius on a point `y` of the fibre of
a constant cover, it does so on the image of `y` under any morphism of constant covers. -/
lemma smul_fiber_map_eq_geometricFrobenius_zpow [IsNaturalSMul (fiber s) G]
    {A B : FiniteEtaleAlgebra K} (f : A.1 →ₐ[K] B.1) (g : G) (n : ℤ)
    (y : (fiber s).obj (constantCover p B)) (h : g • y = (geometricFrobenius p s B ^ n) y) :
    g • (fiber s).map (constantCoverHom p f) y =
      (geometricFrobenius p s A ^ n) ((fiber s).map (constantCoverHom p f) y) := by
  rw [← IsNaturalSMul.naturality, h]
  exact Equiv.Perm.zpow_apply_eq_of_comm _ _ _
    (fun y ↦ fiber_map_constantCoverHom_geometricFrobenius p s f y) n y

section Subfield

variable [Algebra K Ω]

/-- A finite-dimensional intermediate field `K ⊆ R ⊆ Ω` as a finite étale `K`-algebra. -/
noncomputable def finiteEtaleAlgebraOfIntermediateField (R : IntermediateField K Ω)
    [FiniteDimensional K R] : FiniteEtaleAlgebra K :=
  have : Algebra.Etale K R :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K R
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  ⟨CommAlgCat.of K R, inferInstanceAs (Module.Finite K R),
    inferInstanceAs (Algebra.Etale K R)⟩

variable {p s} (hκ : baseRingHom p s = algebraMap K Ω)
include hκ

/-- The inclusion `R ⊆ Ω` of a finite intermediate field, as a point of the geometric fibre of
the constant cover `X₀ ×_{k₀} Spec R`. -/
noncomputable def inclusionPoint (R : IntermediateField K Ω) [FiniteDimensional K R] :
    (fiber s).obj (constantCover p (finiteEtaleAlgebraOfIntermediateField R)) :=
  (fiberConstantCoverEquiv p s _).symm ⟨R.val.toRingHom, by
    rw [hκ]
    ext x
    exact R.val.commutes x⟩

lemma fiberConstantCoverEquiv_inclusionPoint (R : IntermediateField K Ω) [FiniteDimensional K R] :
    (fiberConstantCoverEquiv p s _ (inclusionPoint hκ R)).1 = R.val.toRingHom := by
  rw [inclusionPoint, Equiv.apply_symm_apply]

/-- A point of the geometric fibre of a constant cover whose embedding `A → Ω` lands in a
finite intermediate field `R` is the image of the inclusion point of `R` under a morphism of
constant covers. -/
lemma exists_eq_fiber_map_inclusionPoint (R : IntermediateField K Ω) [FiniteDimensional K R]
    {A : FiniteEtaleAlgebra K} (y : (fiber s).obj (constantCover p A))
    (hy : ∀ a, (fiberConstantCoverEquiv p s A y).1 a ∈ R) :
    ∃ f : A.1 →ₐ[K] (finiteEtaleAlgebraOfIntermediateField R).1,
      y = (fiber s).map (constantCoverHom p f) (inclusionPoint hκ R) := by
  set φ := fiberConstantCoverEquiv p s A y
  let f : A.1 →ₐ[K] R :=
    { toRingHom := φ.1.codRestrict R.toSubalgebra.toSubsemiring hy
      commutes' := fun c ↦ Subtype.ext (by
        change φ.1 (algebraMap K A.1 c) = algebraMap K Ω c
        rw [← hκ]
        exact RingHom.congr_fun φ.2 c) }
  refine ⟨f, (fiberConstantCoverEquiv p s A).injective (Subtype.ext ?_)⟩
  rw [fiberConstantCoverEquiv_fiber_map, fiberConstantCoverEquiv_inclusionPoint]
  rfl

/-- Every `K`-embedding of a finite intermediate field `R` into `Ω` lands in `R`, since `R / K`
is normal. -/
lemma fiberConstantCoverEquiv_mem (R : IntermediateField K Ω) [FiniteDimensional K R]
    (y : (fiber s).obj (constantCover p (finiteEtaleAlgebraOfIntermediateField R))) (a : R) :
    (fiberConstantCoverEquiv p s _ y).1 a ∈ R := by
  set φ := fiberConstantCoverEquiv p s _ y
  have : Finite R := Module.finite_of_finite K
  let ψ : R →ₐ[K] Ω :=
    { toRingHom := φ.1
      commutes' := fun c ↦ by
        rw [← hκ]
        exact RingHom.congr_fun φ.2 c }
  have h : ψ a ∈ ψ.fieldRange := ⟨a, rfl⟩
  rwa [AlgHom.fieldRange_of_normal ψ] at h

/-- If `g` moves the inclusion point of a finite intermediate field `R` by the geometric
Frobenius, then it acts as the geometric Frobenius on every point of the fibre of a constant
cover whose embedding lands in `R`. -/
lemma smul_eq_geometricFrobenius_of_mem [IsNaturalSMul (fiber s) G] (R : IntermediateField K Ω)
    [FiniteDimensional K R]
    (g : G) (hg : g • inclusionPoint hκ R = geometricFrobenius p s _ (inclusionPoint hκ R))
    {A : FiniteEtaleAlgebra K} (y : (fiber s).obj (constantCover p A))
    (hy : ∀ a, (fiberConstantCoverEquiv p s A y).1 a ∈ R) :
    g • y = geometricFrobenius p s A y := by
  obtain ⟨f, rfl⟩ := exists_eq_fiber_map_inclusionPoint hκ R y hy
  exact smul_fiber_map_eq_geometricFrobenius p s G f g _ hg

/-- If `g` moves the inclusion point of a finite intermediate field `R` by an integral power
of the geometric Frobenius, then it acts by this power on every point of the fibre of a constant
cover whose embedding lands in `R`. -/
lemma smul_eq_geometricFrobenius_zpow_of_mem [IsNaturalSMul (fiber s) G]
    (R : IntermediateField K Ω) [FiniteDimensional K R] (g : G) (n : ℤ)
    (hg : g • inclusionPoint hκ R = (geometricFrobenius p s _ ^ n) (inclusionPoint hκ R))
    {A : FiniteEtaleAlgebra K} (y : (fiber s).obj (constantCover p A))
    (hy : ∀ a, (fiberConstantCoverEquiv p s A y).1 a ∈ R) :
    g • y = (geometricFrobenius p s A ^ n) y := by
  obtain ⟨f, rfl⟩ := exists_eq_fiber_map_inclusionPoint hκ R y hy
  exact smul_fiber_map_eq_geometricFrobenius_zpow p s G f g n _ hg

/-- The images of all the `K`-embeddings of a finite étale `K`-algebra `A` into `Ω` lie in a
finite intermediate field. -/
lemma exists_forall_mem_intermediateField (A : FiniteEtaleAlgebra K) :
    ∃ R : IntermediateField K Ω, FiniteDimensional K R ∧
      ∀ (y : (fiber s).obj (constantCover p A)) (a : A.1),
        (fiberConstantCoverEquiv p s A y).1 a ∈ R := by
  have : Finite A.1 := A.finite
  let S : Set Ω := ⋃ z : (fiber s).obj (constantCover p A),
    Set.range (fiberConstantCoverEquiv p s A z).1
  have : Finite S := Set.finite_iUnion fun z ↦ Set.finite_range _
  have hSint : ∀ x ∈ S, _root_.IsIntegral K x := by
    intro x hx
    obtain ⟨z, a, rfl⟩ := Set.mem_iUnion.1 hx
    let φ := fiberConstantCoverEquiv p s A z
    let ψ : A.1 →ₐ[K] Ω :=
      { toRingHom := φ.1
        commutes' := fun c ↦ by
          rw [← hκ]
          exact RingHom.congr_fun φ.2 c }
    exact (Algebra.IsIntegral.isIntegral a).map ψ
  exact ⟨IntermediateField.adjoin K S, IntermediateField.finiteDimensional_adjoin hSint,
    fun y a ↦ IntermediateField.subset_adjoin K S (Set.mem_iUnion.2 ⟨y, a, rfl⟩)⟩

end Subfield

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace X₀]
  [IsFundamentalGroup (fiber s) G]

open scoped FintypeCatDiscrete in
/-- **Lifts of the geometric Frobenius.** For a connected, geometrically connected scheme `X₀`
over a finite field, some element of the fundamental group `π₁(X₀, s)` acts on the geometric
fibre of every constant cover as the geometric Frobenius. -/
theorem exists_smul_eq_geometricFrobenius [GeometricallyConnected p] :
    ∃ g : G, ∀ (A : FiniteEtaleAlgebra K) (y : (fiber s).obj (constantCover p A)),
      g • y = geometricFrobenius p s A y := by
  let : Algebra K Ω := (baseRingHom p s).toAlgebra
  have hκ : baseRingHom p s = algebraMap K Ω := rfl
  let ι := {R : IntermediateField K Ω // FiniteDimensional K R}
  let t (R : ι) : Set G :=
    have := R.2
    {g | g • inclusionPoint hκ R.1 = geometricFrobenius p s _ (inclusionPoint hκ R.1)}
  have hclosed (R : ι) : IsClosed (t R) := by
    have := R.2
    exact isClosed_eq (continuous_id.smul continuous_const) continuous_const
  have hne (R : ι) : (t R).Nonempty := by
    have := R.2
    let A := finiteEtaleAlgebraOfIntermediateField R.1
    have : ConnectedSpace (constantCover p A).obj.left :=
      GeometricallyConnected.geometrically_connectedSpace (f := p) (K := R.1) A.specHom
        (pullback.fst p A.specHom) (pullback.snd p A.specHom) (IsPullback.of_hasPullback _ _)
    have : IsConnected (constantCover p A) := isConnected_of_connectedSpace _
    exact MulAction.exists_smul_eq G _ _
  have hdir : Directed (· ⊇ ·) t := by
    intro R₁ R₂
    have := R₁.2
    have := R₂.2
    refine ⟨⟨R₁.1 ⊔ R₂.1, inferInstance⟩, fun g hg ↦ ?_, fun g hg ↦ ?_⟩
    · exact smul_eq_geometricFrobenius_of_mem G hκ _ g hg _ fun a ↦
        (le_sup_left : R₁.1 ≤ R₁.1 ⊔ R₂.1) (by
          rw [fiberConstantCoverEquiv_inclusionPoint]
          exact a.2)
    · exact smul_eq_geometricFrobenius_of_mem G hκ _ g hg _ fun a ↦
        (le_sup_right : R₂.1 ≤ R₁.1 ⊔ R₂.1) (by
          rw [fiberConstantCoverEquiv_inclusionPoint]
          exact a.2)
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    hdir hne (fun R ↦ (hclosed R).isCompact) hclosed
  refine ⟨g, fun A y ↦ ?_⟩
  obtain ⟨R, _, hR⟩ := exists_forall_mem_intermediateField hκ A
  exact smul_eq_geometricFrobenius_of_mem G hκ R g (Set.mem_iInter.1 hg ⟨R, inferInstance⟩) y
    (hR y)

/-- **The degree map of the Weil group is surjective** for a connected, geometrically connected
scheme over a finite field: a lift of the geometric Frobenius has degree one. -/
theorem exists_mem_weilGroup_snd_eq_one [GeometricallyConnected p] :
    ∃ g : G, (g, Multiplicative.ofAdd 1) ∈ weilGroup p s G := by
  obtain ⟨g, hg⟩ := exists_smul_eq_geometricFrobenius p s G
  refine ⟨g, (mem_weilGroup_iff p s G).2 fun A y ↦ ?_⟩
  simpa using hg A y

end AlgebraicGeometry.Scheme.FiniteEtale
