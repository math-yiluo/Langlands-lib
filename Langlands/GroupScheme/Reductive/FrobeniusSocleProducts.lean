import Langlands.GroupScheme.Reductive.CovariantFrobeniusProducts
import Langlands.GroupScheme.Reductive.CovariantSocleIrreducible
import Langlands.GroupScheme.Reductive.CovariantTensorEmbedding

/-! # Regular spans of irreducible Frobenius products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module TensorProduct
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
  {C : Matrix m n k}

/-- A bijective actual intertwiner transfers all-test irreducibility. -/
theorem Intertwines.isIrreducible_of_bijective (hC : Intertwines ρ σ C)
    (hρ : ρ.IsIrreducible) (hbij : Function.Bijective C.mulVecLin) :
    σ.IsIrreducible := by
  let := hρ.1
  obtain ⟨v, w, hvw⟩ := exists_pair_ne (n → k)
  refine ⟨⟨C.mulVecLin v, C.mulVecLin w, fun h => hvw (hbij.1 h)⟩, ?_⟩
  intro W hW
  have hinj := Submodule.comap_injective_of_surjective hbij.2
  rcases hρ.2 _ (hW.comap hC) with h | h
  · left
    apply hinj
    simpa only [Submodule.comap_bot, LinearMap.ker_eq_bot.mpr hbij.1] using h
  · right
    apply hinj
    simpa only [Submodule.comap_top] using h

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

section Algebra

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
  (W V : Submodule k B) {a b : ℕ}
  (bW : Basis (Fin a) k W) (bV : Basis (Fin b) k V) (hWV : W ≤ V)

/-- The existing inclusion coordinates are the matrix of the actual inclusion. -/
theorem coactionCoordinates_eq_toMatrix_inclusion :
    coactionCoordinates V bV (fun j => (bW j : B)) =
      LinearMap.toMatrix bW bV (Submodule.inclusion hWV) := by
  ext i j
  have hp := LinearMap.congr_fun (subspaceRetraction_comp_subtype V)
    (Submodule.inclusion hWV (bW j))
  change subspaceRetraction V (bW j : B) = _ at hp
  simp only [coactionCoordinates, Matrix.of_apply, extendedCoord,
    LinearMap.comp_apply, LinearMap.toMatrix_apply, Basis.coord_apply, hp,
    LinearMap.id_apply]

/-- Inclusion coordinates compute the inclusion of every vector. -/
theorem coactionCoordinates_mulVec_equivFun (w : W) :
    coactionCoordinates V bV (fun j => (bW j : B)) *ᵥ bW.equivFun w =
      bV.equivFun (Submodule.inclusion hWV w) := by
  rw [coactionCoordinates_eq_toMatrix_inclusion W V bW bV hWV]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

end Algebra

section Regular

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (bV : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (v : algebra G),
      v ∈ V → rightAct ψ v ∈ V)

/-- An irreducible regular space has no proper nonzero finite regular subspace. -/
theorem eq_of_le_of_affineRegularRepresentation_isIrreducible
    (hρ : (affineRegularRepresentation G V bV hV).IsIrreducible)
    (W : Submodule k (algebra G)) {a : ℕ} (bW : Basis (Fin a) k W)
    (hW : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
        w ∈ W → rightAct ψ w ∈ W)
    (hWV : W ≤ V) (hW0 : W ≠ ⊥) :
    W = V := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  let C := coactionCoordinates V bV (fun j => (bW j : algebra G))
  have hC : Intertwines (affineRegularRepresentation G W bW hW)
      (affineRegularRepresentation G V bV hV) C :=
    intertwines_affine_coactionCoordinates G W V bW bV hW hV hWV
  rcases hρ.2 _ hC.isStableSubspace_range with he | he
  · exfalso
    apply hW0
    apply bot_unique
    intro w hw
    have hz : C *ᵥ bW.equivFun ⟨w, hw⟩ = 0 := by
      change C.mulVecLin _ = 0
      rw [LinearMap.range_eq_bot.mp he, LinearMap.zero_apply]
    rw [coactionCoordinates_mulVec_equivFun W V bW bV hWV] at hz
    have hz' := bV.equivFun.injective (hz.trans (map_zero bV.equivFun).symm)
    exact congrArg Subtype.val hz'
  · apply le_antisymm hWV
    intro v hv
    obtain ⟨w, hw⟩ :=
      (LinearMap.range_eq_top.mp he) (bV.equivFun ⟨v, hv⟩)
    change C *ᵥ w = bV.equivFun ⟨v, hv⟩ at hw
    have hw' := coactionCoordinates_mulVec_equivFun W V bW bV hWV
      (bW.equivFun.symm w)
    rw [LinearEquiv.apply_symm_apply, hw] at hw'
    have hh := bV.equivFun.injective hw'
    have hval : v = (bW.equivFun.symm w : algebra G) := congrArg Subtype.val hh
    rw [hval]
    exact (bW.equivFun.symm w).property

include hV in
/-- Every nonzero coordinate generates an irreducible regular coordinate space. -/
theorem affineCovariantSocle_eq_of_mem_of_isIrreducible
    (hρ : (affineRegularRepresentation G V bV hV).IsIrreducible)
    {f : algebra G} (hf : f ∈ V) (hf0 : f ≠ 0) :
    affineCovariantSocle G f = V := by
  classical
  let := (bialgebra (corepresentation G)).toCoalgebra
  apply eq_of_le_of_affineRegularRepresentation_isIrreducible G V bV hV hρ
    (affineCovariantSocle G f) (Module.finBasis k (affineCovariantSocle G f))
    (rightAct_mem_affineCovariantSocle G f)
  · apply regularSpan_le_of_rightAct_mem {f} V _ hV
    intro w hw
    obtain rfl := Finset.mem_singleton.mp hw
    exact hf
  · intro he
    have hm := mem_affineCovariantSocle G f
    rw [he, Submodule.mem_bot] at hm
    exact hf0 hm

end Regular

section Frobenius

variable {k : Type u} [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [IsReduced G.X.left]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance frobeniusSocleProductsReducedAlgebra :
    _root_.IsReduced (algebra G) := by
  have : IsIso (groupSchemeIso G).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (groupSchemeIso G))).hom)
  have h := isReduced_of_isOpenImmersion (groupSchemeIso G).hom.hom.hom.left
  exact (affine_isReduced_iff (CommRingCat.of (algebra G))).mp h

variable (V W : Submodule k (algebra G)) {a b : ℕ}
  (bV : Basis (Fin a) k V) (bW : Basis (Fin b) k W)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (v : algebra G),
      v ∈ V → rightAct ψ v ∈ V)
  (hW : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
      w ∈ W → rightAct ψ w ∈ W)
  (e : ℕ)

/-- A supplied irreducible tensor and a nonzero product make the actual regular
representation on the product image irreducible on every affine test. -/
theorem affineRegularRepresentation_mul_frobeniusCoordinateSpan_isIrreducible
    {c : ℕ} (bP : Basis (Fin c) k (V * frobeniusCoordinateSpan p e W))
    (hP : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (z : algebra G),
        z ∈ V * frobeniusCoordinateSpan p e W →
          rightAct ψ z ∈ V * frobeniusCoordinateSpan p e W)
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    (hnonzero : ∃ v ∈ V, ∃ w ∈ W, v * w ^ p ^ e ≠ (0 : algebra G)) :
    (affineRegularRepresentation G (V * frobeniusCoordinateSpan p e W) bP hP).IsIrreducible := by
  have hM := intertwines_affine_frobeniusProductMatrix p G V W bV bW hV hW e bP hP
  apply hM.isIrreducible_of_bijective hρ
  exact ⟨frobeniusProductMatrix_injective_of_isIrreducible p G V W bV bW hV hW
      e bP hP hρ hnonzero,
    productMatrix_mulVecLin_surjective V (frobeniusCoordinateSpan p e W) bV
      (frobeniusCoordinateBasis p e W bW) bP⟩

include bV bW hV hW in
/-- A nonzero product generates the entire regular product image when its
actual Frobenius tensor is supplied as irreducible. -/
theorem affineCovariantSocle_mul_pow_eq_of_frobeniusTensor_isIrreducible
    (hρ : ((affineRegularRepresentation G V bV hV).tensor
      ((affineRegularRepresentation G W bW hW).frobeniusPower p e)).IsIrreducible)
    {v w : algebra G} (hv : v ∈ V) (hw : w ∈ W) (hvw : v * w ^ p ^ e ≠ 0) :
    affineCovariantSocle G (v * w ^ p ^ e) = V * frobeniusCoordinateSpan p e W := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  have : Module.Finite k V := Module.Finite.of_basis bV
  have : Module.Finite k W := Module.Finite.of_basis bW
  have : Module.Finite k (frobeniusCoordinateSpan p e W) :=
    finite_frobeniusCoordinateSpan p e W
  have : Module.Finite k (V * frobeniusCoordinateSpan p e W) :=
    finite_coordinateProduct V (frobeniusCoordinateSpan p e W)
  let bP := Module.finBasis k (V * frobeniusCoordinateSpan p e W)
  have hP := affine_rightAct_mem_mul_frobeniusCoordinateSpan p G V W bV bW hV hW e
  apply affineCovariantSocle_eq_of_mem_of_isIrreducible G
    (V * frobeniusCoordinateSpan p e W) bP hP
    (affineRegularRepresentation_mul_frobeniusCoordinateSpan_isIrreducible
      p G V W bV bW hV hW e bP hP hρ ⟨v, hv, w, hw, hvw⟩)
  · exact Submodule.mul_mem_mul hv (pow_mem_frobeniusCoordinateSpan p e W hw)
  · exact hvw

omit V W bV bW hV hW in
/-- Equality of singleton regular spans for an irreducible Frobenius product. -/
theorem affineCovariantSocle_mul_pow_eq (e : ℕ) (f g : algebra G)
    (hρ : ((affineCovariantSocleRepresentation G f).tensor
      ((affineCovariantSocleRepresentation G g).frobeniusPower p e)).IsIrreducible)
    (hfg : f * g ^ p ^ e ≠ 0) :
    affineCovariantSocle G (f * g ^ p ^ e) =
      affineCovariantSocle G f * frobeniusCoordinateSpan p e (affineCovariantSocle G g) :=
  affineCovariantSocle_mul_pow_eq_of_frobeniusTensor_isIrreducible p G
    (affineCovariantSocle G f) (affineCovariantSocle G g)
    (Module.finBasis k (affineCovariantSocle G f))
    (Module.finBasis k (affineCovariantSocle G g))
    (rightAct_mem_affineCovariantSocle G f) (rightAct_mem_affineCovariantSocle G g)
    e hρ (mem_affineCovariantSocle G f) (mem_affineCovariantSocle G g) hfg

omit V W bV bW hV hW in
/-- Actual multiplication identifies the tensor of singleton regular spans,
with the second span Frobenius-powered, with the singleton regular span
of the product, under supplied tensor irreducibility and nonzero product. -/
def frobeniusSocleProductEquiv (e : ℕ) (f g : algebra G)
    (hρ : ((affineCovariantSocleRepresentation G f).tensor
      ((affineCovariantSocleRepresentation G g).frobeniusPower p e)).IsIrreducible)
    (hfg : f * g ^ p ^ e ≠ 0) :
    (affineCovariantSocle G f ⊗[k] frobeniusCoordinateSpan p e (affineCovariantSocle G g))
      ≃ₗ[k] affineCovariantSocle G (f * g ^ p ^ e) :=
  (frobeniusCoordinateProductEquiv p G (affineCovariantSocle G f) (affineCovariantSocle G g)
    (Module.finBasis k (affineCovariantSocle G f))
    (Module.finBasis k (affineCovariantSocle G g))
    (rightAct_mem_affineCovariantSocle G f) (rightAct_mem_affineCovariantSocle G g)
    e hρ ⟨f, mem_affineCovariantSocle G f, g, mem_affineCovariantSocle G g, hfg⟩).trans
    (LinearEquiv.ofEq _ _ (affineCovariantSocle_mul_pow_eq p G e f g hρ hfg).symm)

omit V W bV bW hV hW in
@[simp]
theorem frobeniusSocleProductEquiv_tmul (e : ℕ) (f g : algebra G)
    (hρ : ((affineCovariantSocleRepresentation G f).tensor
      ((affineCovariantSocleRepresentation G g).frobeniusPower p e)).IsIrreducible)
    (hfg : f * g ^ p ^ e ≠ 0)
    (v : affineCovariantSocle G f)
    (w : frobeniusCoordinateSpan p e (affineCovariantSocle G g)) :
    (frobeniusSocleProductEquiv p G e f g hρ hfg (v ⊗ₜ[k] w) : algebra G) =
      (v : algebra G) * (w : algebra G) := rfl

omit V W bV bW hV hW in
/-- The dimension of an irreducible Frobenius product is the product of the
dimensions of its two singleton regular spans. -/
theorem finrank_affineCovariantSocle_mul_pow (e : ℕ) (f g : algebra G)
    (hρ : ((affineCovariantSocleRepresentation G f).tensor
      ((affineCovariantSocleRepresentation G g).frobeniusPower p e)).IsIrreducible)
    (hfg : f * g ^ p ^ e ≠ 0) :
    Module.finrank k (affineCovariantSocle G (f * g ^ p ^ e)) =
      Module.finrank k (affineCovariantSocle G f) *
        Module.finrank k (affineCovariantSocle G g) := by
  rw [← (frobeniusSocleProductEquiv p G e f g hρ hfg).finrank_eq,
    Module.finrank_tensorProduct,
    Module.finrank_eq_card_basis
      (frobeniusCoordinateBasis p e (affineCovariantSocle G g)
        (Module.finBasis k (affineCovariantSocle G g))), Fintype.card_fin]

end Frobenius

end Langlands.GroupScheme.Chevalley
