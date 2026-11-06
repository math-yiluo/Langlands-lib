import Langlands.GroupScheme.Reductive.CovariantSocle
import Langlands.GroupScheme.MatrixRepresentation.UnipotentCyclicIrreducibility

/-! # Actual irreducibility of the finite covariant socle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module TensorProduct
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
      w ∈ V → rightAct ψ w ∈ V)

set_option backward.isDefEq.respectTransparency false in
/-- The transported regular representation has the constructed coaction
matrix at the universal point of the original affine group. -/
theorem affineRegularRepresentation_universalMatrix :
    letI := (bialgebra (corepresentation G)).toCoalgebra
    ((affineRegularRepresentation G V b hV).affineMatrix (algebra G)
      (algPoint G (𝟙 _)) : Matrix (Fin d) (Fin d) (algebra G)) =
        subspaceMatrix V b := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  rw [affineRegularRepresentation, affineMatrix_restrict]
  have hx : algPoint G (𝟙 _) ≫ (groupSchemeIso G).inv.hom.hom = 𝟙 _ := by
    rw [algPoint, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun z => z.hom.hom) (groupSchemeIso G).hom_inv_id
  rw [hx]
  exact regularRepresentation_universalMatrix (corepresentation G) V b hV

include hV in
/-- Contracting a universal matrix translate agrees with right contraction
of the corresponding coordinate function. -/
theorem affineRegularCoordinateMap_rightAct
    (ψ : Module.Dual k (algebra G)) (v : Fin d → k) :
    letI := (bialgebra (corepresentation G)).toCoalgebra
    affineRegularCoordinateMap G V b
      (fun i => ψ ((subspaceMatrix V b *ᵥ
        (fun j => algebraMap k (algebra G) (v j))) i)) =
      rightAct ψ (affineRegularCoordinateMap G V b v) := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  have hr (j : Fin d) :
      rightAct ψ (b j : algebra G) =
        ∑ i, ψ (subspaceMatrix V b i j) • (b i : algebra G) := by
    rw [rightAct_apply, comul_basis V b hV, map_sum, map_sum]
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  have hc (i : Fin d) :
      ψ ((subspaceMatrix V b *ᵥ
        (fun j => algebraMap k (algebra G) (v j))) i) =
          ∑ j, v j * ψ (subspaceMatrix V b i j) := by
    simp only [Matrix.mulVec, dotProduct, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [affineRegularCoordinateMap_apply, affineRegularCoordinateMap_apply, map_sum]
  simp only [map_smul, hr, hc, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- All-test stability of a coordinate subspace implies coalgebra stability
of its image in the actual coordinate algebra. -/
theorem rightAct_mem_map_affineRegularCoordinateMap
    (W : Submodule k (Fin d → k))
    (hW : (affineRegularRepresentation G V b hV).IsStableSubspace W) :
    letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
      w ∈ W.map (affineRegularCoordinateMap G V b) →
        rightAct ψ w ∈ W.map (affineRegularCoordinateMap G V b) := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  rintro ψ _ ⟨v, hv, rfl⟩
  have hs := hW (algebra G) (algPoint G (𝟙 _)) v hv ψ
  rw [affineRegularRepresentation_universalMatrix G V b hV] at hs
  exact ⟨_, hs, affineRegularCoordinateMap_rightAct G V b hV ψ v⟩

/-- The actual finite regular representation on the singleton regular span,
using a chosen finite basis. Its construction requires no cell hypothesis. -/
def affineCovariantSocleRepresentation (f : algebra G) :
    MatrixRepresentation G (Fin (Module.finrank k (affineCovariantSocle G f))) :=
  affineRegularRepresentation G (affineCovariantSocle G f)
    (Module.finBasis k (affineCovariantSocle G f))
    (rightAct_mem_affineCovariantSocle G f)

section Socle

variable {H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]

local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Leastness of the covariant socle makes its actual regular representation
irreducible for every finite basis. Stability is on all affine tests. -/
theorem affineRegularRepresentation_isIrreducible_covariantSocle
    {f : algebra G} {m : ℕ} (b : Basis (Fin m) k (affineCovariantSocle G f))
    (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
    {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ)
    (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 1) :
    (affineRegularRepresentation G (affineCovariantSocle G f) b
      (rightAct_mem_affineCovariantSocle G f)).IsIrreducible := by
  let C := affineRegularCoordinateMap G (affineCovariantSocle G f) b
  have hC : Function.Injective C :=
    affineRegularCoordinateMap_injective G (affineCovariantSocle G f) b
  let v := b.equivFun ⟨f, mem_affineCovariantSocle G f⟩
  have hCv : C v = f := by
    change ((b.equivFun.symm (b.equivFun ⟨f, mem_affineCovariantSocle G f⟩) :
      affineCovariantSocle G f) : algebra G) = f
    simp only [LinearEquiv.symm_apply_apply]
  have hv0 : v ≠ 0 := by
    intro hv
    have hf0 : f = 0 := by rw [← hCv, hv, map_zero]
    rw [hf0, map_zero] at hf1
    exact zero_ne_one hf1
  refine ⟨⟨v, 0, hv0⟩, ?_⟩
  intro W hW
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  have hWC0 : W.map C ≠ ⊥ := by
    intro he
    apply hW0
    apply Submodule.map_injective_of_injective hC
    simpa only [Submodule.map_bot] using he
  have hcov : W.map C ≤ AffineCoordinates.leftCovariantSubspace i χ := by
    rintro _ ⟨w, -, rfl⟩
    exact affineCovariantSocle_le_leftCovariantSubspace G i χ hf
      (affineRegularCoordinateMap_mem G (affineCovariantSocle G f) b w)
  have hle : affineCovariantSocle G f ≤ W.map C :=
    affineCovariantSocle_le_of_nonzero_rightAct_mem G i j hU χ (W.map C)
      (rightAct_mem_map_affineRegularCoordinateMap G (affineCovariantSocle G f) b
        (rightAct_mem_affineCovariantSocle G f) W hW)
      hcov hWC0 hq hcell hf hfU hf1
  apply top_unique
  intro w _
  obtain ⟨z, hz, he⟩ :=
    hle (affineRegularCoordinateMap_mem G (affineCovariantSocle G f) b w)
  exact hC he ▸ hz

/-- The constructed covariant socle representation is irreducible under
supplied unipotence, a product cell and a normalized invariant covariant. -/
theorem affineCovariantSocleRepresentation_isIrreducible
    {f : algebra G} (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
    {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ)
    (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 1) :
    (affineCovariantSocleRepresentation G f).IsIrreducible :=
  affineRegularRepresentation_isIrreducible_covariantSocle G
    (Module.finBasis k (affineCovariantSocle G f)) i j hU χ hq hcell hf hfU hf1

/-- Rational-point stability detection transfers the socle's all-test
irreducibility to its actual rational-point representation. -/
theorem affineCovariantSocleRepresentation_rationalRepresentation_isIrreducible
    [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    {f : algebra G} (i : H ⟶ G) (j : U ⟶ G) (hU : IsUnipotent U) (χ : algebra H)
    {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
    (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      IsUnit (pointAlgebraHom G T g q) →
        ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
          g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ)
    (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 1) :
    (affineCovariantSocleRepresentation G f).rationalRepresentation.IsIrreducible := by
  let ρ := affineCovariantSocleRepresentation G f
  have hρ := affineCovariantSocleRepresentation_isIrreducible G i j hU χ
    hq hcell hf hfU hf1
  let := hρ.1
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro he
    have hh : (⊥ : Submodule k
        (Fin (Module.finrank k (affineCovariantSocle G f)) → k)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top hh
  · intro W
    have hW : ρ.IsStableSubspace W.toSubmodule :=
      isStableSubspace_of_rationalMatrix ρ W.toSubmodule
        (fun g _ hx => W.apply_mem_toSubmodule g hx)
    rcases hρ.2 W.toSubmodule hW with he | he
    · exact Or.inl (Subrepresentation.toSubmodule_injective he)
    · exact Or.inr (Subrepresentation.toSubmodule_injective he)

end Socle

end Langlands.GroupScheme.Chevalley
