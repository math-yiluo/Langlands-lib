import Langlands.Cohomology.HerbrandQuotient
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Herbrand quotients of full lattices in a real representation

Two `G`-stable full lattices in the same finite-dimensional real representation of a finite
cyclic group `G` have the same Herbrand quotient (Milne, *Class Field Theory*, VII Lemma 3.5).

The proof finds an integer matrix `X` with `det X ≠ 0` intertwining the two integral actions:
the identity of `V`, written in bases of the two lattices, is a real solution of the
intertwining equations, and a polynomial non-vanishing argument over the `ℤ`-span of its
entries produces an integral solution with nonzero determinant. The resulting map of
representations is injective with finite cokernel, which preserves the Herbrand quotient.
-/

namespace Langlands.Cohomology.Herbrand

open CategoryTheory

universe u

section Descent

variable {G κ : Type*} [Fintype κ] [DecidableEq κ]

/-- If a system of intertwining equations `Q g * X = X * P g` with integer coefficients has a
real solution with nonzero determinant, then it has an integer solution with nonzero
determinant. -/
theorem exists_intMatrix_det_ne_zero (P Q : G → Matrix κ κ ℤ) (C : Matrix κ κ ℝ)
    (hC : C.det ≠ 0)
    (h : ∀ g, (Q g).map (Int.castRingHom ℝ) * C = C * (P g).map (Int.castRingHom ℝ)) :
    ∃ X : Matrix κ κ ℤ, X.det ≠ 0 ∧ ∀ g, Q g * X = X * P g := by
  classical
  -- A `ℤ`-basis `c` of the `ℤ`-span of the entries of `C`.
  let S : Submodule ℤ ℝ := Submodule.span ℤ (Set.range fun p : κ × κ => C p.1 p.2)
  have hS : ∀ i j, C i j ∈ S := fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
  have : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  let c := Module.Free.chooseBasis ℤ S
  -- `C = ∑ s, c s • Y s` with integer matrices `Y s`.
  let Y : Module.Free.ChooseBasisIndex ℤ S → Matrix κ κ ℤ := fun s i j =>
    c.repr ⟨C i j, hS i j⟩ s
  have hY : ∀ i j, C i j = ∑ s, (c s : ℝ) * (Y s i j : ℝ) := by
    intro i j
    have := congrArg Subtype.val (c.sum_repr ⟨C i j, hS i j⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul, zsmul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hind : ∀ r : Module.Free.ChooseBasisIndex ℤ S → ℤ,
      ∑ s, (c s : ℝ) * (r s : ℝ) = 0 → ∀ s, r s = 0 := by
    intro r hr
    apply Fintype.linearIndependent_iff.1 c.linearIndependent r
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, zsmul_eq_mul, Submodule.coe_zero]
    rw [← hr]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hCY : C = ∑ s, (c s : ℝ) • (Y s).map (Int.castRingHom ℝ) := by
    ext i j
    rw [hY, Matrix.sum_apply]
    rfl
  -- Each `Y s` solves the equations.
  have hYeq : ∀ g s, Q g * Y s = Y s * P g := by
    intro g s
    have key : ∑ s, (c s : ℝ) • (Q g * Y s - Y s * P g).map (Int.castRingHom ℝ) = 0 := by
      have := h g
      rw [hCY, Matrix.mul_sum, Matrix.sum_mul] at this
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
      rw [← this]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.map_sub _ (map_sub (Int.castRingHom ℝ)), Matrix.map_mul, Matrix.map_mul,
        smul_sub, Matrix.mul_smul, Matrix.smul_mul]
    rw [← sub_eq_zero]
    ext i j
    have := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at this
    exact hind (fun s => (Q g * Y s - Y s * P g) i j) this s
  -- The determinant polynomial `det (∑ s, X_s • Y s)`.
  let Mp : Matrix κ κ (MvPolynomial (Module.Free.ChooseBasisIndex ℤ S) ℤ) := fun i j =>
    ∑ s, MvPolynomial.X s * MvPolynomial.C (Y s i j)
  have hMp : Mp.det ≠ 0 := by
    intro h0
    have h1 := congrArg (MvPolynomial.aeval fun s => (c s : ℝ)) h0
    rw [AlgHom.map_det, map_zero] at h1
    apply hC
    rw [← h1]
    congr 1
    ext i j
    rw [hY]
    show _ = MvPolynomial.aeval _ (Mp i j)
    simp [Mp]
  obtain ⟨q, hq⟩ : ∃ q, MvPolynomial.eval q Mp.det ≠ 0 := by
    by_contra! hall
    exact hMp (MvPolynomial.funext fun q => by rw [hall q, map_zero])
  refine ⟨∑ s, q s • Y s, ?_, fun g => ?_⟩
  · rw [RingHom.map_det] at hq
    convert hq using 2
    ext i j
    rw [Matrix.sum_apply]
    show _ = MvPolynomial.eval q (Mp i j)
    simp only [Mp, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.smul_apply,
      smul_eq_mul]
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hYeq]

end Descent

section ULiftLinear

/-- An additive map between modules over the lifted integers is linear. -/
def uliftIntLinearMap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ULift.{u} ℤ) M] [Module (ULift.{u} ℤ) N] (f : M →+ N) :
    M →ₗ[ULift.{u} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    obtain ⟨n⟩ := r
    have h : (ULift.up n : ULift.{u} ℤ) = (n : ULift.{u} ℤ) := by ext; simp
    rw [RingHom.id_apply, h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

@[simp]
theorem uliftIntLinearMap_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ULift.{u} ℤ) M] [Module (ULift.{u} ℤ) N] (f : M →+ N) (x : M) :
    uliftIntLinearMap f x = f x :=
  rfl

end ULiftLinear

section Bases

-- The lifted-integer module structure of a representation is its own instance `Rep.hV2`, not
-- the one induced from its `ℤ`-module structure.
attribute [-instance] ULift.module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If a real basis is the image of an integral basis, real coordinates of images are the
integral coordinates. -/
theorem repr_apply_eq_of_basis {X : Type*} [AddCommGroup X] {κ : Type*} [Fintype κ]
    (a : Module.Basis κ ℤ X) (aR : Module.Basis κ ℝ V) (ι : X →+ V)
    (h : ∀ i, aR i = ι (a i)) (x : X) (i : κ) :
    aR.repr (ι x) i = (a.repr x i : ℝ) := by
  conv_lhs => rw [← a.sum_repr x]
  rw [map_sum]
  simp_rw [map_zsmul, ← h, ← Int.cast_smul_eq_zsmul ℝ]
  rw [aR.repr_sum_self]

variable {G : Type u} [Group G] {A B : Rep (ULift.{u} ℤ) G}

/-- Two lattices with compatible integral and real bases in the same real representation:
there is an injective map of representations with finite cokernel between them. -/
theorem exists_injective_finite_coker {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : G → V →ₗ[ℝ] V) (a : Module.Basis κ ℤ A) (b : Module.Basis κ ℤ B)
    (aR bR : Module.Basis κ ℝ V) (ιA : A →+ V) (ιB : B →+ V)
    (haR : ∀ i, aR i = ιA (a i)) (hbR : ∀ i, bR i = ιB (b i))
    (hA : ∀ g x, ιA (A.ρ g x) = T g (ιA x)) (hB : ∀ g y, ιB (B.ρ g y) = T g (ιB y)) :
    ∃ f : A ⟶ B, Function.Injective f.hom ∧
      Finite (B ⧸ LinearMap.range f.hom.toLinearMap) := by
  classical
  let ρA : G → A →ₗ[ℤ] A := fun g => (A.ρ g).toAddMonoidHom.toIntLinearMap
  let ρB : G → B →ₗ[ℤ] B := fun g => (B.ρ g).toAddMonoidHom.toIntLinearMap
  have hCdet : (LinearMap.toMatrix aR bR LinearMap.id).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (B := LinearMap.toMatrix bR aR LinearMap.id) (by
      rw [← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.toMatrix_id])
  have hPR : ∀ g, (LinearMap.toMatrix a a (ρA g)).map (Int.castRingHom ℝ) =
      LinearMap.toMatrix aR aR (T g) := by
    intro g
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [haR j, ← hA, repr_apply_eq_of_basis a aR ιA haR]
    rfl
  have hQR : ∀ g, (LinearMap.toMatrix b b (ρB g)).map (Int.castRingHom ℝ) =
      LinearMap.toMatrix bR bR (T g) := by
    intro g
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [hbR j, ← hB, repr_apply_eq_of_basis b bR ιB hbR]
    rfl
  have hrel : ∀ g, (LinearMap.toMatrix b b (ρB g)).map (Int.castRingHom ℝ) *
      LinearMap.toMatrix aR bR LinearMap.id =
      LinearMap.toMatrix aR bR LinearMap.id *
        (LinearMap.toMatrix a a (ρA g)).map (Int.castRingHom ℝ) := by
    intro g
    rw [hPR, hQR, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, LinearMap.comp_id,
      LinearMap.id_comp]
  obtain ⟨X, hXdet, hX⟩ := exists_intMatrix_det_ne_zero _ _ _ hCdet hrel
  let φ : A →ₗ[ℤ] B := Matrix.toLin a b X
  let ψ : B →ₗ[ℤ] A := Matrix.toLin b a X.adjugate
  have hφψ : ∀ y, φ (ψ y) = X.det • y := by
    intro y
    rw [← Matrix.toLin_mul_apply, Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
    rfl
  have hψφ : ∀ x, ψ (φ x) = X.det • x := by
    intro x
    rw [← Matrix.toLin_mul_apply, Matrix.adjugate_mul, map_smul, Matrix.toLin_one]
    rfl
  have hφeq : ∀ g x, φ (A.ρ g x) = B.ρ g (φ x) := by
    intro g x
    have : φ ∘ₗ ρA g = ρB g ∘ₗ φ := (LinearMap.toMatrix a b).injective (by
      rw [LinearMap.toMatrix_comp a a b, LinearMap.toMatrix_comp a b b, LinearMap.toMatrix_toLin]
      exact (hX g).symm)
    exact LinearMap.congr_fun this x
  let f : A ⟶ B := ConcreteCategory.ofHom (C := Rep (ULift.{u} ℤ) G)
    { toLinearMap := uliftIntLinearMap φ.toAddMonoidHom
      isIntertwining' := fun g => LinearMap.ext fun x => hφeq g x }
  refine ⟨f, fun x y hxy => ?_, ?_⟩
  · have hxy' : φ x = φ y := hxy
    have h1 : X.det • x = X.det • y := by rw [← hψφ, ← hψφ, hxy']
    apply a.repr.injective
    ext i
    have h2 := congrArg (fun z => a.repr z i) h1
    simp only [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h2
    exact mul_left_cancel₀ hXdet h2
  · let R := LinearMap.range f.hom.toLinearMap
    have : Module.Finite ℤ B := Module.Finite.of_basis b
    have : Module.Finite ℤ (B ⧸ R) :=
      Module.Finite.of_surjective R.mkQ.toAddMonoidHom.toIntLinearMap (Submodule.mkQ_surjective R)
    apply Module.finite_of_fg_torsion
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective R z
    refine ⟨⟨X.det, mem_nonZeroDivisors_of_ne_zero hXdet⟩, ?_⟩
    show X.det • R.mkQ y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hφψ]
    exact ⟨ψ y, rfl⟩

/-- Lattice invariance of the Herbrand quotient, with explicit compatible bases: if the integral
bases `a` of `A` and `b` of `B` map to real bases of the same real representation `V`, then `A`
and `B` have the same Herbrand quotient. -/
theorem hasHerbrandQuotient_iff_of_bases [Finite G] [IsCyclic G] {κ : Type*} [Fintype κ]
    (T : G → V →ₗ[ℝ] V) (a : Module.Basis κ ℤ A) (b : Module.Basis κ ℤ B)
    (aR bR : Module.Basis κ ℝ V) (ιA : A →+ V) (ιB : B →+ V)
    (haR : ∀ i, aR i = ιA (a i)) (hbR : ∀ i, bR i = ιB (b i))
    (hA : ∀ g x, ιA (A.ρ g x) = T g (ιA x)) (hB : ∀ g y, ιB (B.ρ g y) = T g (ιB y)) {q : ℚ} :
    HasHerbrandQuotient A q ↔ HasHerbrandQuotient B q := by
  classical
  obtain ⟨f, hf, hfin⟩ := exists_injective_finite_coker T a b aR bR ιA ιB haR hbR hA hB
  exact hasHerbrandQuotient_iff_of_injective f hf

end Bases

section ZLattice

attribute [-instance] ULift.module

variable {G : Type u} [Group G] {A B : Rep (ULift.{u} ℤ) G}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The additive isomorphism `e` identifies the representation `A` with the lattice `M ⊆ V`,
compatibly with the real action `T`: `e (ρ_A(g) x) = T(g) (e x)` in `V`. -/
def IsEquivariantLatticeEquiv (T : G → V →ₗ[ℝ] V) (A : Rep (ULift.{u} ℤ) G)
    (M : Submodule ℤ V) (e : A ≃+ M) : Prop :=
  ∀ g x, (e (A.ρ g x) : V) = T g (e x)

/-- Two representations realized as full lattices in the same real representation admit an
injective map of representations with finite cokernel. -/
theorem exists_injective_finite_coker_of_isZLattice (T : G → V →ₗ[ℝ] V)
    (M N : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M] [DiscreteTopology N]
    [IsZLattice ℝ N] (eA : A ≃+ M) (eB : B ≃+ N) (hA : IsEquivariantLatticeEquiv T A M eA)
    (hB : IsEquivariantLatticeEquiv T B N eB) :
    ∃ f : A ⟶ B, Function.Injective f.hom ∧
      Finite (B ⧸ LinearMap.range f.hom.toLinearMap) := by
  classical
  let bM := Module.Free.chooseBasis ℤ M
  let bN := Module.Free.chooseBasis ℤ N
  let aR := bM.ofZLatticeBasis ℝ M
  let bR := bN.ofZLatticeBasis ℝ N
  let e : Module.Free.ChooseBasisIndex ℤ N ≃ Module.Free.ChooseBasisIndex ℤ M :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis bR, ← Module.finrank_eq_card_basis aR])
  exact exists_injective_finite_coker T (bM.map eA.symm.toIntLinearEquiv)
    ((bN.map eB.symm.toIntLinearEquiv).reindex e) aR (bR.reindex e)
    (M.subtype.toAddMonoidHom.comp eA.toAddMonoidHom)
    (N.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)
    (fun i => by simp [aR]) (fun i => by simp [bR]) hA hB

/-- **Lattice invariance** (Milne VII Lemma 3.5). Let `G` be finite cyclic, acting on a
finite-dimensional real vector space `V` by the linear maps `T g`, and let `A`, `B` be
representations identified equivariantly with full lattices `M`, `N ⊆ V`. Then `A` and `B` have
the same Herbrand quotient. -/
theorem hasHerbrandQuotient_iff_of_isZLattice [Finite G] [IsCyclic G] (T : G → V →ₗ[ℝ] V)
    (M N : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M] [DiscreteTopology N]
    [IsZLattice ℝ N] (eA : A ≃+ M) (eB : B ≃+ N) (hA : IsEquivariantLatticeEquiv T A M eA)
    (hB : IsEquivariantLatticeEquiv T B N eB) {q : ℚ} :
    HasHerbrandQuotient A q ↔ HasHerbrandQuotient B q := by
  obtain ⟨f, hf, hfin⟩ := exists_injective_finite_coker_of_isZLattice T M N eA eB hA hB
  exact hasHerbrandQuotient_iff_of_injective f hf

/-- Lattice invariance, division-free: if `H¹(G, A)` and `H²(G, A)` are finite, then so are
`H¹(G, B)` and `H²(G, B)`, and `|H²(G, A)| · |H¹(G, B)| = |H²(G, B)| · |H¹(G, A)|`. -/
theorem natCard_of_isZLattice [Finite G] [IsCyclic G] (T : G → V →ₗ[ℝ] V)
    (M N : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M] [DiscreteTopology N]
    [IsZLattice ℝ N] (eA : A ≃+ M) (eB : B ≃+ N) (hA : IsEquivariantLatticeEquiv T A M eA)
    (hB : IsEquivariantLatticeEquiv T B N eB) [Finite (groupCohomology A 1)]
    [Finite (groupCohomology A 2)] :
    Finite (groupCohomology B 1) ∧ Finite (groupCohomology B 2) ∧
      Nat.card (groupCohomology A 2) * Nat.card (groupCohomology B 1) =
        Nat.card (groupCohomology B 2) * Nat.card (groupCohomology A 1) := by
  obtain ⟨h₁, h₂, h⟩ := (hasHerbrandQuotient_iff_of_isZLattice T M N eA eB hA hB).1
    (hasHerbrandQuotient_of_finite_cohomology A)
  refine ⟨h₁, h₂, ?_⟩
  have hA1 : (Nat.card (groupCohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : (Nat.card (groupCohomology A 2) : ℚ) * Nat.card (groupCohomology B 1) =
      Nat.card (groupCohomology B 2) * Nat.card (groupCohomology A 1) := by
    rw [h]
    field_simp
  exact_mod_cast key

end ZLattice

end Langlands.Cohomology.Herbrand
