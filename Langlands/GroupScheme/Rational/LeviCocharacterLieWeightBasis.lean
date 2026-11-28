import Langlands.GroupScheme.Rational.LeviCocharacterLieWeights
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Lie.KernelBaseChangeSpan

/-! # A weight basis of the Lie algebra adapted to a parabolic and a Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

/-- Every character of `𝔾_m` over a field is a power map. -/
theorem Gm.powerHom_gmEndEquiv (k : Type u) [Field k]
    (χ : characterLattice (Gm (Spec (CommRingCat.of k)))) :
    Gm.powerHom _ (gmEndEquiv k χ) = χ := by
  rw [Gm.powerHom, zmultiplesHom_apply]
  exact (eq_gmEndEquiv_zsmul k χ).symm

/-- A submodule is spanned by the ambient images of a basis of it. -/
theorem le_span_basis_coe {R M J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {W : Submodule R M} (b : Module.Basis J R W) :
    W ≤ Submodule.span R (Set.range fun i => (b i : M)) := by
  intro x hx
  have h : (⟨x, hx⟩ : W) ∈ Submodule.span R (Set.range b) := by
    rw [b.span_eq]
    trivial
  have h2 := Submodule.mem_map_of_mem (f := W.subtype) h
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

set_option maxHeartbeats 1600000 in
/-- A basis of the Lie algebra of `G` consisting of weight vectors of a central cocharacter `ψ`
of the Levi subgroup `M'` presenting the parabolic `Q`, with the weight-zero vectors spanning
`Lie M'` and the positive-weight vectors spanning `Lie V`. -/
theorem exists_leviCocharacterLieWeightBasis (k : Type u) [Field k]
    (G Q M' V : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] [IsAffineHom M'.X.hom] [IsAffineHom V.X.hom]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q) (hG : IsConnectedReductive G)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl : IsRationalLeviSubgroup l') :
    ∃ (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M') (n : ℕ)
      (e : Module.Basis (Fin n) k (Additive (lieKernel G k))) (w : Fin n → ℤ),
      IsCentral ψ ∧ (Dynamic.parabolic (ψ ≫ l' ≫ q)).IsRepresentedBy q ∧
      (∀ i, e i ∈ weightSpace (ψ ≫ l' ≫ q) (Gm.powerHom _ (w i))) ∧
      (∀ i, w i = 0 → e i ∈ LinearMap.range (Lie.targetMapLinear (l' ≫ q) k)) ∧
      LinearMap.range (Lie.targetMapLinear (l' ≫ q) k) ≤ Submodule.span k (e '' {i | w i = 0}) ∧
      (∀ i, 0 < w i → e i ∈ LinearMap.range (Lie.targetMapLinear (iV ≫ q) k)) ∧
      LinearMap.range (Lie.targetMapLinear (iV ≫ q) k) ≤ Submodule.span k (e '' {i | 0 < w i}) := by
  classical
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨ψ, hψ, hP, h0, hpos, -⟩ :=
    leviCocharacterLieWeights k G Q M' V q iV l' hG hq hV hl
  have hint := isInternal_weightSpace_of_isSplitTorus k G (Gm (Spec (CommRingCat.of k)))
    isSplitTorus_gm (ψ ≫ l' ≫ q)
  let bχ : ∀ χ, Module.Basis (Fin (Module.finrank k (weightSpace (ψ ≫ l' ≫ q) χ))) k
      (weightSpace (ψ ≫ l' ≫ q) χ) := fun χ => Module.finBasis k _
  let B := hint.collectedBasis bχ
  have : Finite (Σ χ, Fin (Module.finrank k (weightSpace (ψ ≫ l' ≫ q) χ))) :=
    Module.Finite.finite_basis B
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (Σ χ, Fin (Module.finrank k
    (weightSpace (ψ ≫ l' ≫ q) χ)))
  let e := B.reindex eqv
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℤ, ∀ i, w i = gmEndEquiv k (eqv.symm i).1 :=
    ⟨fun i => gmEndEquiv k (eqv.symm i).1, fun _ => rfl⟩
  have he (i : Fin n) : e i = B (eqv.symm i) := by simp [e, Module.Basis.reindex_apply]
  have hmem (i : Fin n) : e i ∈ weightSpace (ψ ≫ l' ≫ q) (Gm.powerHom _ (w i)) := by
    rw [he]
    have h := hint.collectedBasis_mem bχ (eqv.symm i)
    rw [hw, Gm.powerHom_gmEndEquiv]
    exact h
  have hpow (m : ℤ) : gmEndEquiv k (Gm.powerHom (Spec (CommRingCat.of k)) m) = m := by
    rw [Gm.powerHom, zmultiplesHom_apply, gmEndEquiv_zsmul_id]
  have hspan (χ : characterLattice (Gm (Spec (CommRingCat.of k)))) (P : ℤ → Prop)
      (hχ : P (gmEndEquiv k χ)) :
      weightSpace (ψ ≫ l' ≫ q) χ ≤ Submodule.span k (e '' {i | P (w i)}) := by
    refine (le_span_basis_coe (bχ χ)).trans (Submodule.span_mono ?_)
    rintro _ ⟨j, rfl⟩
    refine ⟨eqv ⟨χ, j⟩, ?_, ?_⟩
    · change P (w (eqv ⟨χ, j⟩))
      rw [hw, Equiv.symm_apply_apply]
      exact hχ
    · rw [he, Equiv.symm_apply_apply, hint.collectedBasis_coe]
  refine ⟨ψ, n, e, w, hψ, hP, hmem, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := hmem i
    rw [hi] at h
    exact h0.le h
  · exact h0.ge.trans (hspan _ (fun m => m = 0) (hpow 0))
  · intro i hi
    have h := hmem i
    generalize w i = r at h hi
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = (m : ℤ) + 1 := ⟨r.toNat - 1, by omega⟩
    exact hpos.le (Submodule.mem_iSup_of_mem m h)
  · refine hpos.ge.trans (iSup_le fun m => hspan _ (fun r => 0 < r) ?_)
    rw [hpow]
    omega

/-- The weight basis after a change of coefficients: for every commutative `k`-algebra `A`, a basis
of `lieKernel G A` of weight vectors of a central cocharacter `ψ` of `M'` presenting `Q`, with the
weight-zero vectors spanning the image of `Lie M'` and the positive-weight vectors spanning the
image of `Lie V`. -/
theorem exists_leviCocharacterLieWeightBasis_baseChange (k : Type u) [Field k]
    (G Q M' V : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] [IsAffineHom M'.X.hom] [IsAffineHom V.X.hom]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q) (hG : IsConnectedReductive G)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl : IsRationalLeviSubgroup l') :
    ∃ (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M') (n : ℕ) (w : Fin n → ℤ),
      IsCentral ψ ∧ (Dynamic.parabolic (ψ ≫ l' ≫ q)).IsRepresentedBy q ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A],
        ∃ e : Module.Basis (Fin n) A (Additive (lieKernel G A)),
          (∀ i (t : Lie.AffinePoints (Gm (Spec (CommRingCat.of k))).toGrp A),
            adjoint G A (t ≫ (ψ ≫ l' ≫ q).hom.hom) (e i) =
              (Lie.characterValue (Gm.powerHom _ (w i)) t : A) • e i) ∧
          (∀ i, w i = 0 → e i ∈ LinearMap.range (Lie.targetMapLinear (l' ≫ q) A)) ∧
          LinearMap.range (Lie.targetMapLinear (l' ≫ q) A) ≤
            Submodule.span A (e '' {i | w i = 0}) ∧
          (∀ i, 0 < w i → e i ∈ LinearMap.range (Lie.targetMapLinear (iV ≫ q) A)) ∧
          LinearMap.range (Lie.targetMapLinear (iV ≫ q) A) ≤
            Submodule.span A (e '' {i | 0 < w i}) := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth M'.X.hom := hl.isConnectedReductive.smooth
  have : Smooth V.X.hom := hV.1.smooth
  obtain ⟨ψ, n, e₀, w, hψ, hP, hmem, h0, h0le, hp, hple⟩ :=
    exists_leviCocharacterLieWeightBasis k G Q M' V q iV l' hG hq hV hl
  refine ⟨ψ, n, w, hψ, hP, fun A _ _ => ?_⟩
  let e := Lie.kernelBaseChangeBasis G A e₀
  have he (i : Fin n) : e i = lieKernelMapLinear G (Algebra.ofId k A) (e₀ i) :=
    Lie.kernelBaseChangeBasis_apply G A e₀ i
  have himage (P : ℤ → Prop) :
      lieKernelMapLinear G (Algebra.ofId k A) '' (e₀ '' {i | P (w i)}) = e '' {i | P (w i)} := by
    rw [Set.image_image]
    exact Set.image_congr fun i _ => (he i).symm
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    rw [he]
    exact (mem_weightSpace.mp (hmem i)) A t
  · intro i hi
    rw [he]
    exact Lie.lieKernelMapLinear_mem_range_targetMapLinear A (l' ≫ q) (h0 i hi)
  · rw [← himage (fun m => m = 0)]
    exact Lie.range_targetMapLinear_le_span_of_le_span A (l' ≫ q) _ h0le
  · intro i hi
    rw [he]
    exact Lie.lieKernelMapLinear_mem_range_targetMapLinear A (iV ≫ q) (hp i hi)
  · rw [← himage (fun m => 0 < m)]
    exact Lie.range_targetMapLinear_le_span_of_le_span A (iV ≫ q) _ hple

end Langlands.GroupScheme
