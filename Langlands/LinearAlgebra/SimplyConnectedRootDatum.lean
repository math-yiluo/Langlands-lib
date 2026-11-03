import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The simply connected root datum of a root datum -/

noncomputable section

open Module Function Set Submodule

namespace Langlands.LinearAlgebra.SimplyConnectedRootDatum

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootDatum ι X Y)

/-- The coroot lattice of a root datum with finitely many roots is a reflexive `ℤ`-module. -/
theorem isReflexive_corootSpan [Finite ι] : IsReflexive ℤ (P.corootSpan ℤ) := by
  have : IsReflexive ℤ Y := .of_isPerfPair P.toLinearMap.flip
  infer_instance

/-- The map `X → Hom(ℤR^∨, ℤ)` restricting characters to the coroot lattice. -/
def weightMap : X →ₗ[ℤ] Dual ℤ (P.corootSpan ℤ) :=
  (P.corootSpan ℤ).subtype.dualMap ∘ₗ P.toLinearMap

@[simp]
theorem weightMap_apply (x : X) (y : P.corootSpan ℤ) :
    weightMap P x y = P.toLinearMap x y := rfl

/-- The restriction of the root `P.root i` to the coroot lattice. -/
def root (i : ι) : Dual ℤ (P.corootSpan ℤ) :=
  weightMap P (P.root i)

@[simp]
theorem root_apply (i : ι) (y : P.corootSpan ℤ) :
    root P i y = P.toLinearMap (P.root i) y := rfl

theorem root_corootSpanMem (i j : ι) :
    root P i (P.corootSpanMem ℤ j) = P.pairing i j := by
  simp [RootPairing.root_coroot_eq_pairing]

theorem root_injective [Finite ι] : Injective (root P) := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  intro i j h
  have h₁ : P.pairing i j = 2 := by
    rw [← root_corootSpanMem, h, root_corootSpanMem, RootPairing.pairing_same]
  have h₂ : P.pairing j i = 2 := by
    rw [← root_corootSpanMem, ← h, root_corootSpanMem, RootPairing.pairing_same]
  exact (P.pairing_two_two_iff i j).mp ⟨h₁, h₂⟩

/-- The simply connected root datum `(Hom(ℤR^∨, ℤ), R, ℤR^∨, R^∨)` of a root datum
`(X, R, Y, R^∨)` with finitely many roots. -/
def rootDatum [Finite ι] : RootDatum ι (Dual ℤ (P.corootSpan ℤ)) (P.corootSpan ℤ) :=
  haveI := isReflexive_corootSpan P
  { toLinearMap := LinearMap.id
    root := ⟨root P, root_injective P⟩
    coroot := ⟨P.corootSpanMem ℤ, fun i j h => P.coroot.injective (congrArg Subtype.val h)⟩
    root_coroot_two := fun i => by
      change root P i (P.corootSpanMem ℤ i) = 2
      rw [root_corootSpanMem, RootPairing.pairing_same]
    reflectionPerm := P.reflectionPerm
    reflectionPerm_root := fun i j => by
      ext y
      change P.toLinearMap (P.root j) y -
          P.toLinearMap (P.root j) (P.coroot i) * P.toLinearMap (P.root i) y =
        P.toLinearMap (P.root (P.reflectionPerm i j)) y
      rw [← P.reflectionPerm_root i j]
      simp
    reflectionPerm_coroot := fun i j => by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_smul]
      exact P.reflectionPerm_coroot i j }

variable [Finite ι]

/-- The weight lattice `Hom(ℤR^∨, ℤ)` of the simply connected root datum is finitely
generated. -/
instance finite_dual_corootSpan : Module.Finite ℤ (Dual ℤ (P.corootSpan ℤ)) := by
  have : IsReflexive ℤ (P.corootSpan ℤ) := isReflexive_corootSpan P
  have : Module.Free ℤ (P.corootSpan ℤ) := Module.free_of_finite_type_torsion_free'
  infer_instance

@[simp]
theorem rootDatum_toLinearMap :
    (rootDatum P).toLinearMap = LinearMap.id := rfl

@[simp]
theorem rootDatum_root (i : ι) : (rootDatum P).root i = root P i := rfl

@[simp]
theorem rootDatum_coroot (i : ι) : (rootDatum P).coroot i = P.corootSpanMem ℤ i := rfl

@[simp]
theorem rootDatum_reflectionPerm (i : ι) :
    (rootDatum P).reflectionPerm i = P.reflectionPerm i := rfl

@[simp]
theorem rootDatum_pairing (i j : ι) : (rootDatum P).pairing i j = P.pairing i j :=
  root_corootSpanMem P i j

/-- The coroots of the simply connected root datum span its whole coweight lattice. -/
theorem corootSpan_rootDatum : (rootDatum P).corootSpan ℤ = ⊤ := by
  have h : range (rootDatum P).coroot =
      ((↑) : P.corootSpan ℤ → Y) ⁻¹' range P.coroot := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  change span ℤ (range (rootDatum P).coroot) = ⊤
  rw [h]
  exact span_span_coe_preimage

/-- The canonical morphism from a root datum to its simply connected root datum: restriction of
characters to the coroot lattice, and inclusion of the coroot lattice. -/
def toRootDatum : RootPairing.Hom P (rootDatum P) where
  weightMap := weightMap P
  coweightMap := (P.corootSpan ℤ).subtype
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by
    ext y x
    rfl
  root_weightMap := rfl
  coroot_coweightMap := rfl

@[simp]
theorem toRootDatum_weightMap : (toRootDatum P).weightMap = weightMap P := rfl

@[simp]
theorem toRootDatum_coweightMap :
    (toRootDatum P).coweightMap = (P.corootSpan ℤ).subtype := rfl

@[simp]
theorem toRootDatum_indexEquiv : (toRootDatum P).indexEquiv = Equiv.refl ι := rfl

/-- The coweight map of `toRootDatum P` is injective. -/
theorem injective_toRootDatum_coweightMap : Injective (toRootDatum P).coweightMap :=
  (P.corootSpan ℤ).injective_subtype

/-- If the coroots span a subgroup of finite index, the weight map of `toRootDatum P` is
injective. -/
theorem injective_toRootDatum_weightMap (h : Finite (Y ⧸ P.corootSpan ℤ)) :
    Injective (toRootDatum P).weightMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  suffices P.toLinearMap x = 0 from P.toLinearMap.toPerfPair.injective (by simpa using this)
  ext y
  obtain ⟨n, hn, hny⟩ : ∃ n : ℕ, 0 < n ∧ n • y ∈ P.corootSpan ℤ := by
    have hfin : IsOfFinAddOrder (Submodule.Quotient.mk (p := P.corootSpan ℤ) y) :=
      isOfFinAddOrder_of_finite _
    refine ⟨_, hfin.addOrderOf_pos, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact addOrderOf_nsmul_eq_zero _
  have hxy : P.toLinearMap x (n • y) = 0 := by
    simpa using LinearMap.congr_fun hx ⟨n • y, hny⟩
  rw [map_nsmul, nsmul_eq_mul] at hxy
  simpa [hn.ne'] using hxy

omit [Finite ι] in
/-- If the coroots of `P` span its coweight lattice, so do the coroots of every root datum
equivalent to `P`. -/
theorem corootSpan_eq_top_of_equiv {ι₂ X₂ Y₂ : Type*} [AddCommGroup X₂] [AddCommGroup Y₂]
    {P : RootDatum ι X Y} {Q : RootDatum ι₂ X₂ Y₂} (e : RootPairing.Equiv P Q)
    (h : P.corootSpan ℤ = ⊤) : Q.corootSpan ℤ = ⊤ := by
  have hmap : (Q.corootSpan ℤ).map e.toHom.coweightMap = P.corootSpan ℤ := by
    rw [Submodule.map_span, ← Set.range_comp, e.toHom.coroot_coweightMap,
      e.toHom.indexEquiv.symm.surjective.range_comp]
  rw [eq_top_iff]
  intro y _
  have hy : e.toHom.coweightMap y ∈ (Q.corootSpan ℤ).map e.toHom.coweightMap := by
    rw [hmap, h]
    exact mem_top
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [e.bijective_coweightMap.injective hzy] at hz

/-- The simply connected root datum of a reduced root datum is reduced. -/
instance isReduced_rootDatum [P.IsReduced] : (rootDatum P).IsReduced := by
  have : IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : IsReflexive ℤ (P.corootSpan ℤ) := isReflexive_corootSpan P
  refine ⟨fun i j hij => ?_⟩
  rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent] at hij
  have hP : ¬ LinearIndependent ℤ ![P.root i, P.root j] := by
    rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent]
    simpa [RootPairing.coxeterWeight] using hij
  rcases RootPairing.IsReduced.eq_or_eq_neg i j hP with h | h
  · left
    simp [root, h]
  · right
    simp [root, h]

end Langlands.LinearAlgebra.SimplyConnectedRootDatum
