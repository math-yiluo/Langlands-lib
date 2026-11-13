import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The adjoint root datum of a root datum -/

noncomputable section

open Module Function Set Submodule

namespace Langlands.LinearAlgebra.AdjointRootDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootDatum ι X Y) [Finite ι]

/-- The root lattice of a root datum is a reflexive `ℤ`-module. -/
theorem isReflexive_rootSpan : IsReflexive ℤ (P.rootSpan ℤ) := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  infer_instance

/-- The map `Y → Hom(ℤR, ℤ)` restricting cocharacters to the root lattice. -/
def coweightMap : Y →ₗ[ℤ] Dual ℤ (P.rootSpan ℤ) :=
  (P.rootSpan ℤ).subtype.dualMap ∘ₗ P.toLinearMap.flip

omit [Finite ι] in
@[simp]
theorem coweightMap_apply (y : Y) (x : P.rootSpan ℤ) :
    coweightMap P y x = P.toLinearMap x y := rfl

/-- The restriction of the coroot `P.coroot i` to the root lattice. -/
def coroot (i : ι) : Dual ℤ (P.rootSpan ℤ) :=
  coweightMap P (P.coroot i)

omit [Finite ι] in
@[simp]
theorem coroot_apply (i : ι) (x : P.rootSpan ℤ) :
    coroot P i x = P.toLinearMap x (P.coroot i) := rfl

omit [Finite ι] in
theorem coroot_rootSpanMem (i j : ι) :
    coroot P i (P.rootSpanMem ℤ j) = P.pairing j i := by
  simp [RootPairing.root_coroot_eq_pairing]

theorem coroot_injective : Injective (coroot P) := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  intro i j h
  have h₁ : P.pairing i j = 2 := by
    rw [← coroot_rootSpanMem, ← h, coroot_rootSpanMem, RootPairing.pairing_same]
  have h₂ : P.pairing j i = 2 := by
    rw [← coroot_rootSpanMem, h, coroot_rootSpanMem, RootPairing.pairing_same]
  exact (P.pairing_two_two_iff i j).mp ⟨h₁, h₂⟩

/-- The adjoint root datum `(ℤR, R, Hom(ℤR, ℤ), R^∨)` of a root datum `(X, R, Y, R^∨)`. -/
def rootDatum : RootDatum ι (P.rootSpan ℤ) (Dual ℤ (P.rootSpan ℤ)) :=
  haveI := isReflexive_rootSpan P
  { toLinearMap := Dual.eval ℤ (P.rootSpan ℤ)
    root := ⟨P.rootSpanMem ℤ, fun i j h => P.root.injective (congrArg Subtype.val h)⟩
    coroot := ⟨coroot P, coroot_injective P⟩
    root_coroot_two := fun i => by
      change coroot P i (P.rootSpanMem ℤ i) = 2
      rw [coroot_rootSpanMem, RootPairing.pairing_same]
    reflectionPerm := P.reflectionPerm
    reflectionPerm_root := fun i j => by
      apply Subtype.ext
      change P.root j - P.toLinearMap (P.root j) (P.coroot i) • P.root i = _
      exact P.reflectionPerm_root i j
    reflectionPerm_coroot := fun i j => by
      ext x
      change P.toLinearMap x (P.coroot j) -
          P.toLinearMap (P.root i) (P.coroot j) * P.toLinearMap x (P.coroot i) =
        P.toLinearMap x (P.coroot (P.reflectionPerm i j))
      rw [← P.reflectionPerm_coroot i j]
      simp }

@[simp]
theorem rootDatum_root (i : ι) : (rootDatum P).root i = P.rootSpanMem ℤ i := rfl

@[simp]
theorem rootDatum_coroot (i : ι) : (rootDatum P).coroot i = coroot P i := rfl

@[simp]
theorem rootDatum_toLinearMap (x : P.rootSpan ℤ) (f : Dual ℤ (P.rootSpan ℤ)) :
    (rootDatum P).toLinearMap x f = f x := rfl

/-- The root lattice is finitely generated when there are finitely many roots. -/
instance finite_rootSpan : Module.Finite ℤ (P.rootSpan ℤ) := by
  have : (P.rootSpan ℤ).FG := Submodule.fg_span (Set.finite_range P.root)
  exact Module.Finite.iff_fg.mpr this

/-- The canonical morphism from the adjoint root datum to the root datum: inclusion of the root
lattice, and restriction of cocharacters to the root lattice. -/
def fromRootDatum : RootPairing.Hom (rootDatum P) P where
  weightMap := (P.rootSpan ℤ).subtype
  coweightMap := coweightMap P
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by
    ext y x
    rfl
  root_weightMap := rfl
  coroot_coweightMap := rfl

@[simp]
theorem fromRootDatum_weightMap : (fromRootDatum P).weightMap = (P.rootSpan ℤ).subtype := rfl

@[simp]
theorem fromRootDatum_coweightMap : (fromRootDatum P).coweightMap = coweightMap P := rfl

/-- The weight map of `fromRootDatum P` is injective. -/
theorem injective_fromRootDatum_weightMap : Injective (fromRootDatum P).weightMap :=
  (P.rootSpan ℤ).injective_subtype

/-- If the roots span a subgroup of finite index, the coweight map of `fromRootDatum P` is
injective. -/
theorem injective_fromRootDatum_coweightMap (h : Finite (X ⧸ P.rootSpan ℤ)) :
    Injective (fromRootDatum P).coweightMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  suffices P.toLinearMap.flip y = 0 from P.toLinearMap.flip.toPerfPair.injective (by simpa using this)
  ext x
  obtain ⟨n, hn, hnx⟩ : ∃ n : ℕ, 0 < n ∧ n • x ∈ P.rootSpan ℤ := by
    have hfin : IsOfFinAddOrder (Submodule.Quotient.mk (p := P.rootSpan ℤ) x) :=
      isOfFinAddOrder_of_finite _
    refine ⟨_, hfin.addOrderOf_pos, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact addOrderOf_nsmul_eq_zero _
  have hxy : P.toLinearMap (n • x) y = 0 := by
    simpa using LinearMap.congr_fun hy ⟨n • x, hnx⟩
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hxy
  simpa [hn.ne'] using hxy

/-- The adjoint root datum of a reduced root datum is reduced. -/
instance isReduced_rootDatum [P.IsReduced] : (rootDatum P).IsReduced := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : IsReflexive ℤ (P.rootSpan ℤ) := isReflexive_rootSpan P
  refine ⟨fun i j hij => ?_⟩
  rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent] at hij
  have hP : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent]
    have hpair : ∀ a b, (rootDatum P).pairing a b = P.pairing a b := fun a b => by
      change coroot P b (P.rootSpanMem ℤ a) = _
      exact coroot_rootSpanMem P b a
    simpa [RootPairing.coxeterWeight, hpair] using hij
  rcases RootPairing.IsReduced.eq_or_eq_neg i j hP with h | h
  · left
    exact Subtype.ext h
  · right
    exact Subtype.ext h

end Langlands.LinearAlgebra.AdjointRootDatum
