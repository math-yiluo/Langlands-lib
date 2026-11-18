import Langlands.GroupScheme.Reductive.TitsDominantClass
import Langlands.GroupScheme.Reductive.HighestWeightSubquotientRepresentation
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraCompression

/-! # Coefficient matrices of the highest-weight subquotient -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Coefficient matrices preserve stable subspaces. -/
theorem coefficientMatrix_mulVec_mem
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {V : Submodule K (n → K)} (hV : ρ.IsStableSubspace V) (φ : CharacterUnits.Coord G →ₗ[k] k)
    {v : n → K} (hv : v ∈ V) : coefficientMatrix ρ φ *ᵥ v ∈ V := by
  have h := hV (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] CharacterUnits.Coord G))
    (universalScalarPoint K G) v hv (baseFunctional K φ)
  rw [functional_mulVec_algebraMap] at h
  exact h

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
  {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
  {nu : characterLattice p.torus}

local instance titsSubquotientAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

theorem HighestSubquotientData.proj_retr_mulVec_eq_zero (D : p.HighestSubquotientData ρ nu)
    {y : n → K} (hy : y ∈ p.highestRadical ρ nu) : D.proj *ᵥ (D.retr *ᵥ y) = 0 := by
  have hyX : y ∈ LinearMap.range D.incl.mulVecLin := by
    rw [D.range_incl]
    exact p.highestRadical_le ρ nu hy
  obtain ⟨w, rfl⟩ := hyX
  change D.proj *ᵥ (D.retr *ᵥ (D.incl *ᵥ w)) = 0
  rw [Matrix.mulVec_mulVec (M := D.retr), D.retr_incl, Matrix.one_mulVec]
  have hk : w ∈ LinearMap.ker D.proj.mulVecLin := by
    rw [D.ker_proj, Submodule.mem_comap]
    exact hy
  exact hk

theorem HighestSubquotientData.retr_mulVec_of_mem (D : p.HighestSubquotientData ρ nu)
    {x : n → K} (hx : x ∈ p.highestGenerated ρ nu) : D.incl *ᵥ (D.retr *ᵥ x) = x := by
  rw [← D.range_incl] at hx
  obtain ⟨w, rfl⟩ := hx
  change D.incl *ᵥ (D.retr *ᵥ (D.incl *ᵥ w)) = D.incl *ᵥ w
  rw [Matrix.mulVec_mulVec (M := D.retr), D.retr_incl, Matrix.one_mulVec]

/-- Compression of the ambient coefficient matrices through a rational idempotent adapted to
`X ⊇ Y` gives the coefficient matrices of the subquotient. -/
theorem HighestSubquotientData.compression (D : p.HighestSubquotientData ρ nu)
    {f : Matrix n n K} (hff : f * f = f) (hfX : ∀ v, f *ᵥ v ∈ p.highestGenerated ρ nu)
    (hfY : ∀ y ∈ p.highestRadical ρ nu, f *ᵥ y = 0)
    (hfid : ∀ x ∈ p.highestGenerated ρ nu, f *ᵥ x - x ∈ p.highestRadical ρ nu) :
    (D.proj * D.retr * f) * (f * D.incl * D.sect) = 1 ∧
      (f * D.incl * D.sect) * (D.proj * D.retr * f) = f ∧
      ∀ φ, coefficientMatrix D.quot φ =
        (D.proj * D.retr * f) * coefficientMatrix ρ φ * (f * D.incl * D.sect) := by
  have hXst := p.isStableSubspace_highestGenerated ρ nu
  have hYst := p.isStableSubspace_highestRadical ρ nu
  have hsect : ∀ u, D.proj *ᵥ (D.sect *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, D.proj_sect, Matrix.one_mulVec]
  have hinclX : ∀ w, D.incl *ᵥ w ∈ p.highestGenerated ρ nu := fun w => by
    rw [← D.range_incl]
    exact ⟨w, rfl⟩
  -- `f` is the identity modulo `Y` on `X`, so `proj ∘ retr ∘ f = proj ∘ retr` on `X`
  have hkey : ∀ x ∈ p.highestGenerated ρ nu,
      D.proj *ᵥ (D.retr *ᵥ (f *ᵥ x)) = D.proj *ᵥ (D.retr *ᵥ x) := by
    intro x hx
    have h := D.proj_retr_mulVec_eq_zero (hfid x hx)
    rwa [Matrix.mulVec_sub, Matrix.mulVec_sub, sub_eq_zero] at h
  refine ⟨?_, ?_, fun φ => ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    rw [hkey _ (hfX _), hkey _ (hinclX _),
      show D.retr *ᵥ (D.incl *ᵥ (D.sect *ᵥ u)) = D.sect *ᵥ u by
        rw [Matrix.mulVec_mulVec (M := D.retr), D.retr_incl, Matrix.one_mulVec], hsect]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    set w := D.retr *ᵥ (f *ᵥ v) with hw
    have hfv : D.incl *ᵥ w = f *ᵥ v := D.retr_mulVec_of_mem (hfX v)
    have hdiff : D.incl *ᵥ (D.sect *ᵥ (D.proj *ᵥ w)) - D.incl *ᵥ w ∈ p.highestRadical ρ nu := by
      rw [← Matrix.mulVec_sub]
      have hk : D.sect *ᵥ (D.proj *ᵥ w) - w ∈ LinearMap.ker D.proj.mulVecLin := by
        rw [LinearMap.mem_ker]
        change D.proj *ᵥ (D.sect *ᵥ (D.proj *ᵥ w) - w) = 0
        rw [Matrix.mulVec_sub, hsect, sub_self]
      rw [D.ker_proj, Submodule.mem_comap] at hk
      exact hk
    have h1 := hfY _ hdiff
    rw [Matrix.mulVec_sub, sub_eq_zero, hfv] at h1
    rw [h1]
    rw [Matrix.mulVec_mulVec, hff]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    set x := D.incl *ᵥ (D.sect *ᵥ u) with hx
    have hxX : x ∈ p.highestGenerated ρ nu := hinclX _
    -- `f x = x + y₁` with `y₁ ∈ Y`
    have hy1 := hfid x hxX
    set y₁ := f *ᵥ x - x
    have hfx : f *ᵥ x = x + y₁ := by simp [y₁]
    rw [hfx, Matrix.mulVec_add, Matrix.mulVec_add, hfY _ (coefficientMatrix_mulVec_mem hYst φ hy1),
      add_zero, hkey _ (coefficientMatrix_mulVec_mem hXst φ hxX)]
    -- `retr (X x) = X_sub (sect u)` since `X x ∈ X`
    have hcoef_sub := coefficientMatrix_intertwines_of D.incl_intertwines φ
    have hcoef_quot := coefficientMatrix_intertwines_of D.proj_intertwines φ
    have hXx : coefficientMatrix ρ φ *ᵥ x = D.incl *ᵥ (coefficientMatrix D.sub φ *ᵥ (D.sect *ᵥ u)) := by
      rw [hx, Matrix.mulVec_mulVec, ← hcoef_sub, ← Matrix.mulVec_mulVec]
    rw [hXx, Matrix.mulVec_mulVec (M := D.retr), D.retr_incl, Matrix.one_mulVec,
      Matrix.mulVec_mulVec (M := D.proj), hcoef_quot, ← Matrix.mulVec_mulVec, hsect]

/-- The Tits algebra of the subquotient is the compression of a descended algebra containing
the Tits algebra of the ambient representation, along a rational adapted idempotent. -/
theorem HighestSubquotientData.titsAlgebra_quot_eq_compressed [IsGalois k K]
    (D : p.HighestSubquotientData ρ nu) (hirr : D.quot.IsIrreducible)
    (hscalar : ∀ C : Matrix (Fin D.r) (Fin D.r) K, D.quot.Intertwines D.quot C →
      ∃ c : K, C = Matrix.scalar (Fin D.r) c)
    (P' : (K ≃ₐ[k] K) → Matrix (Fin D.r) (Fin D.r) K) (hP'u : ∀ σ, IsUnit (P' σ))
    (hP' : ∀ σ, D.quot.Intertwines (galoisTwist σ D.quot) (P' σ))
    (B : Subalgebra k (Matrix n n K)) (P : (K ≃ₐ[k] K) → Matrix n n K) (hPu : ∀ σ, IsUnit (P σ))
    (hB : B ≤ Algebra.GaloisTwistedMatrix.twistedFixed P) (hρB : titsAlgebra ρ ≤ B)
    {f : Matrix n n K} (hfB : f ∈ B) (hff : f * f = f)
    (hfX : ∀ v, f *ᵥ v ∈ p.highestGenerated ρ nu)
    (hfY : ∀ y ∈ p.highestRadical ρ nu, f *ᵥ y = 0)
    (hfid : ∀ x ∈ p.highestGenerated ρ nu, f *ᵥ x - x ∈ p.highestRadical ρ nu) :
    ∃ (hFE : (D.proj * D.retr * f) * (f * D.incl * D.sect) = 1)
      (hEF : (f * D.incl * D.sect) * (D.proj * D.retr * f) ∈ B),
      titsAlgebra D.quot = Algebra.GaloisTwistedMatrix.compressed B (D.proj * D.retr * f)
        (f * D.incl * D.sect) hFE hEF := by
  obtain ⟨hFE, hEF, hcomp⟩ := D.compression hff hfX hfY hfid
  have hEFB : (f * D.incl * D.sect) * (D.proj * D.retr * f) ∈ B := by rw [hEF]; exact hfB
  exact ⟨hFE, hEFB, titsAlgebra_eq_compressed ρ D.quot hirr hscalar P' hP'u hP' B P hPu hB hρB
    _ _ hFE hEFB hcomp⟩

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme

open MatrixRepresentation

/-- Compression form of the subquotient of Tits's Proposition 3.4: along an idempotent adapted to
`X ⊇ Y`, the coefficient matrices of the subquotient are compressions of those of the ambient
representation. -/
def TitsSubquotientCompressionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) (N : ℕ)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin N))
    (nu : characterLattice p.torus) (D : p.HighestSubquotientData ρ nu)
    (f : Matrix (Fin N) (Fin N) K), f * f = f →
    (∀ v, f *ᵥ v ∈ p.highestGenerated ρ nu) →
    (∀ y ∈ p.highestRadical ρ nu, f *ᵥ y = 0) →
    (∀ x ∈ p.highestGenerated ρ nu, f *ᵥ x - x ∈ p.highestRadical ρ nu) →
      (D.proj * D.retr * f) * (f * D.incl * D.sect) = 1 ∧
      (f * D.incl * D.sect) * (D.proj * D.retr * f) = f ∧
      ∀ φ, coefficientMatrix D.quot φ =
        (D.proj * D.retr * f) * coefficientMatrix ρ φ * (f * D.incl * D.sect)

theorem titsSubquotientCompression : TitsSubquotientCompressionStatement.{u} := by
  intro k K _ _ _ G _ p N ρ nu D f hff hfX hfY hfid
  exact D.compression hff hfX hfY hfid

end Langlands.GroupScheme
