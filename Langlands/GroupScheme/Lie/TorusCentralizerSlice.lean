import Langlands.GroupScheme.Lie.AdjointSliceExtension
import Langlands.GroupScheme.Lie.TorusRegularElement
import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # A dense adjoint slice through the centralizer of a torus Lie algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true in
/-- A torus over `k` splits over an infinite field extension of `k` (an algebraic closure of
any splitting field). -/
theorem _root_.Langlands.GroupScheme.IsTorus.exists_infinite_isSplitTorus {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω), Infinite Ω ∧
      IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap k Ω)).obj T) := by
  obtain ⟨K, _, _, h⟩ := hT
  exact ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance,
    h.baseChange_fieldTower k K (AlgebraicClosure K) T⟩

section LinearAlgebra

/-- **Common kernels commute with field extension.** If every vector over `k` killed by all
the matrices `M y` lies in the column space of `B`, then the same holds over any field
extension `E` of `k` for the matrices with entries mapped to `E`. -/
theorem exists_mulVec_map_eq_of_commonKernel {k E κ n m : Type*} [Field k] [Field E]
    [Algebra k E] [Fintype n] [Fintype m] (M : κ → Matrix n n k) (B : Matrix n m k)
    (hB : ∀ v : n → k, (∀ y, M y *ᵥ v = 0) → ∃ u : m → k, B *ᵥ u = v)
    (w : n → E) (hw : ∀ y, (M y).map (algebraMap k E) *ᵥ w = 0) :
    ∃ t : m → E, B.map (algebraMap k E) *ᵥ t = w := by
  classical
  let bE := Module.Basis.ofVectorSpace k E
  let v : Module.Basis.ofVectorSpaceIndex k E → n → k := fun b i => bE.repr (w i) b
  have hv : ∀ b y, M y *ᵥ v b = 0 := by
    intro b y
    funext i
    have h := congrArg (fun x => bE.repr x b) (congrFun (hw y) i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_zero,
      Finsupp.zero_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply] at h
    simpa [v, Matrix.mulVec, dotProduct, ← Algebra.smul_def] using h
  choose u hu using fun b => hB (v b) (hv b)
  let s : Finset (Module.Basis.ofVectorSpaceIndex k E) :=
    Finset.univ.biUnion fun i => (bE.repr (w i)).support
  refine ⟨fun j => ∑ b ∈ s, algebraMap k E (u b j) * bE b, ?_⟩
  funext i
  have hwi : w i = ∑ b ∈ s, bE.repr (w i) b • bE b := by
    conv_lhs => rw [← bE.linearCombination_repr (w i)]
    rw [Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _
      (Finset.subset_biUnion_of_mem (fun i => (bE.repr (w i)).support) (Finset.mem_univ i))
      (fun b c => c • bE b) (fun _ _ => zero_smul k _)
  rw [hwi]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := congrFun (hu b) i
  simp only [Matrix.mulVec, dotProduct] at hb
  change ∑ j, algebraMap k E (B i j) * (algebraMap k E (u b j) * bE b) = v b i • bE b
  rw [← hb, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc]

end LinearAlgebra

section Centralizer

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)

/-- The centralizer of the Lie algebra of `T₀` in finite Lie coordinates: the common kernel
of the adjoint differentials `ad(j₀ Y)` for all Lie elements `Y` of `T₀`. -/
def torusCentralizerCoordinates : Submodule k (Fin d → k) :=
  ⨅ Y : lieKernel T₀.toGrp (CommRingCat.of k),
    LinearMap.ker (adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y)))

/-- A matrix whose columns form a basis of `torusCentralizerCoordinates c j₀`. -/
def torusCentralizerMatrix :
    Matrix (Fin d) (Fin (Module.finrank k (torusCentralizerCoordinates c j₀))) k :=
  Matrix.of fun i j => (Module.finBasis k (torusCentralizerCoordinates c j₀) j : Fin d → k) i

theorem mem_torusCentralizerCoordinates_iff (v : Fin d → k) :
    v ∈ torusCentralizerCoordinates c j₀ ↔
      ∀ Y : lieKernel T₀.toGrp (CommRingCat.of k),
        adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y)) v = 0 := by
  simp [torusCentralizerCoordinates, Submodule.mem_iInf]

/-- The columns of `torusCentralizerMatrix c j₀` are centralized by the Lie algebra of
`T₀`. -/
theorem adjointDifferentialFamily_torusCentralizerMatrix
    (Y : lieKernel T₀.toGrp (CommRingCat.of k)) (j) :
    adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y))
      (fun i => torusCentralizerMatrix c j₀ i j) = 0 :=
  (mem_torusCentralizerCoordinates_iff c j₀ _).1
    (Module.finBasis k (torusCentralizerCoordinates c j₀) j).2 Y

/-- Every vector centralized by the Lie algebra of `T₀` lies in the column space of
`torusCentralizerMatrix c j₀`. -/
theorem exists_torusCentralizerMatrix_mulVec (v : Fin d → k)
    (hv : ∀ Y : lieKernel T₀.toGrp (CommRingCat.of k),
      adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y)) v = 0) :
    ∃ u, torusCentralizerMatrix c j₀ *ᵥ u = v := by
  let b := Module.finBasis k (torusCentralizerCoordinates c j₀)
  let x : torusCentralizerCoordinates c j₀ := ⟨v, (mem_torusCentralizerCoordinates_iff c j₀ v).2 hv⟩
  refine ⟨b.equivFun x, ?_⟩
  have hx := congrArg Subtype.val (b.sum_equivFun x)
  funext i
  have hxi := congrFun hx i
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at hxi
  change _ = (x : Fin d → k) i
  rw [← hxi]
  simp only [Matrix.mulVec, dotProduct, torusCentralizerMatrix, Matrix.of_apply, b, mul_comm]

/-- The Lie algebra of `T₀` centralizes every column of `torusCentralizerMatrix c j₀`. -/
theorem targetMap_mem_elementCentralizerLie_torusCentralizerMatrix
    (Y : lieKernel T₀.toGrp (CommRingCat.of k)) (j) :
    Additive.ofMul (targetMap j₀ _ Y) ∈ elementCentralizerLie G
      ((c.equiv (.of (CommRingCat.of k) k)).symm
        (fun i => torusCentralizerMatrix c j₀ i j)).toMul := by
  rw [mem_elementCentralizerLie_iff_adjointDifferential c]
  change adjointDifferentialFamily c (Additive.ofMul (targetMap j₀ _ Y))
    (c.equiv (.of (CommRingCat.of k) k) ((c.equiv (.of (CommRingCat.of k) k)).symm
      (fun i => torusCentralizerMatrix c j₀ i j))) = 0
  rw [LinearEquiv.apply_symm_apply]
  exact adjointDifferentialFamily_torusCentralizerMatrix c j₀ Y j

end Centralizer

section Extension

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {d : ℕ}
  (c : FiniteCoordinates G d)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} (j₀ : T₀.toGrp ⟶ G)

local notation "G_E" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k E)) G

local instance torusCentralizerSliceAffine : IsAffineHom (G_E).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- The adjoint matrix of the scalar extension of a Lie element of `T₀` is the scalar
extension of its adjoint matrix. -/
theorem tangentMatrix_targetMap_kernelFieldExtension
    (Y : lieKernel T₀.toGrp (CommRingCat.of k)) :
    (adjointRepresentation (c.baseChange k E)).tangentMatrix E
        (targetMap ((GroupScheme.baseChange (algebraBaseMap k E)).map j₀) E
          (kernelFieldExtension (K := E) T₀.toGrp Y)) =
      ((adjointRepresentation c).tangentMatrix k (targetMap j₀ _ Y)).map (algebraMap k E) := by
  rw [← kernelFieldExtension_target, adjointRepresentation_baseChange_tangentMatrix,
    kernelFieldExtension, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MatrixRepresentation.tangentMatrix_naturality]
  rfl

/-- **The centralizer of the torus Lie algebra after field extension.** Every vector over `E`
centralized by the Lie algebra of the base change of `T₀` lies in the `E`-column space of
`torusCentralizerMatrix c j₀`. -/
theorem exists_torusCentralizerMatrix_map_mulVec (w : Fin d → E)
    (hw : ∀ Y : lieKernel ((GroupScheme.baseChange (algebraBaseMap k E)).obj T₀.toGrp)
        (CommRingCat.of E),
      adjointDifferentialFamily (c.baseChange k E)
        (Additive.ofMul (targetMap ((GroupScheme.baseChange (algebraBaseMap k E)).map j₀) _ Y))
        w = 0) :
    ∃ t, (torusCentralizerMatrix c j₀).map (algebraMap k E) *ᵥ t = w := by
  refine exists_mulVec_map_eq_of_commonKernel
    (fun Y : lieKernel T₀.toGrp (CommRingCat.of k) =>
      (adjointRepresentation c).tangentMatrix k (targetMap j₀ _ Y))
    (torusCentralizerMatrix c j₀) (fun v hv => exists_torusCentralizerMatrix_mulVec c j₀ v
      fun Y => by rw [adjointDifferentialFamily_apply, Matrix.toLin'_apply]; exact hv Y) w
    fun Y => ?_
  have h := hw (kernelFieldExtension (K := E) T₀.toGrp Y)
  rw [adjointDifferentialFamily_apply, Matrix.toLin'_apply] at h
  rwa [tangentMatrix_targetMap_kernelFieldExtension] at h

local instance torusCentralizerSliceLocallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (G_E).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

omit [Field E] [Algebra k E] in
/-- **Dominance of the slice through the torus centralizer.** Let `G` be a smooth affine group
over a field `k` and `T₀ ⟶ G` a homomorphism from a torus. The slice map
`G × 𝔸^r ⟶ Lie(G)`, `(g, t) ↦ Ad(g) (B t)`, where the columns of `B` form a basis of the
centralizer of `Lie(T₀)` in `Lie(G)`, has dense range. -/
theorem denseRange_sliceMap_torusCentralizerMatrix [Smooth G.X.hom] (hT : IsTorus T₀.toGrp) :
    DenseRange (sliceMap (adjointRepresentation c) (torusCentralizerMatrix c j₀)).left := by
  obtain ⟨Ω, _, _, _, hS'⟩ := hT.exists_infinite_isSplitTorus
  let S := (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀
  have hS : IsSplitTorus S.toGrp := hS'
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  obtain ⟨Y, hY₁, hY₂⟩ := exists_regular_targetMap (c.baseChange k Ω) (S := S)
    ((GroupScheme.baseChange (algebraBaseMap k Ω)).map j₀) hS
  obtain ⟨t₀, ht₀⟩ := exists_torusCentralizerMatrix_map_mulVec c j₀ _ hY₁
  refine denseRange_sliceMap_of_extension (K := Ω) _ _ t₀ fun v => ?_
  obtain ⟨X, z, hz, hXz⟩ := hY₂ v
  obtain ⟨t', ht'⟩ := exists_torusCentralizerMatrix_map_mulVec c j₀ z hz
  refine ⟨kernelBaseChangeEquiv k Ω G Ω X, t', ?_⟩
  rw [adjointDifferentialFamily_apply, Matrix.toLin'_apply] at hXz
  rw [ht₀, ht', ← adjointRepresentation_baseChange_tangentMatrix]
  exact hXz

omit [Field E] [Algebra k E] in
/-- **A dense adjoint slice centralized by a torus.** Let `G` be a smooth affine group over a
field `k` with finite Lie coordinates `c`, and `T₀ ⟶ G` a homomorphism from a torus. There is a
matrix `B` over `k` whose columns are centralized by the Lie algebra of `T₀` such that the slice
map `(g, t) ↦ Ad(g) (B t)` has dense range. -/
theorem exists_torusCentralizerSlice [Smooth G.X.hom] (hT : IsTorus T₀.toGrp) :
    ∃ (r : ℕ) (B : Matrix (Fin d) (Fin r) k),
      (∀ j (Y : lieKernel T₀.toGrp (CommRingCat.of k)),
        Additive.ofMul (targetMap j₀ _ Y) ∈ elementCentralizerLie G
          ((c.equiv (.of (CommRingCat.of k) k)).symm (fun i => B i j)).toMul) ∧
      DenseRange (sliceMap (adjointRepresentation c) B).left :=
  ⟨_, torusCentralizerMatrix c j₀,
    fun j Y => targetMap_mem_elementCentralizerLie_torusCentralizerMatrix c j₀ Y j,
    denseRange_sliceMap_torusCentralizerMatrix c j₀ hT⟩

end Extension

end Langlands.GroupScheme.Lie
