import Langlands.GroupScheme.Reductive.CovariantSocleIrreducible
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Interval

/-! # Restriction and dimension bounds for entire covariant spaces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  {G H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom U.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom

variable (i : H ⟶ G) (j : U ⟶ G) (χ : algebra H)

/-- Actual restriction of the entire covariant space to the second cell factor. -/
def covariantCellRestriction :
    leftCovariantSubspace i χ →ₗ[k] algebra U :=
  (AffineHomImageHopfAdapter.pullback j).hom.toAlgHom.toLinearMap.comp
    (leftCovariantSubspace i χ).subtype

@[simp]
theorem covariantCellRestriction_apply (f : leftCovariantSubspace i χ) :
    covariantCellRestriction i j χ f =
      AffineHomImageHopfAdapter.pullback j (f : algebra G) := rfl

variable {q : algebra G}
  (hq : q ∈ nonZeroDivisors (algebra G))
  (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
    IsUnit (pointAlgebraHom G T g q) →
      ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
        g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))

include hq hcell in
/-- A supplied dense product cell makes restriction injective on the entire
covariant space, without reducedness or rational-point assumptions. -/
theorem covariantCellRestriction_injective :
    Function.Injective (covariantCellRestriction i j χ) := by
  intro f f' he
  apply Subtype.ext
  apply eq_of_pointAlgebraHom_eq_on_unit_locus hq
  intro T g hg
  obtain ⟨a, u, rfl⟩ := hcell T g hg
  rw [pointAlgebraHom_leftCovariant i χ f.property,
    pointAlgebraHom_leftCovariant i χ f'.property]
  congr 1
  rw [AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  exact congrArg (pointAlgebraHom U T u) he

variable {σ : Type v}
  (e : algebra U ≃ₐ[k] MvPolynomial σ k)

/-- Polynomial restriction in supplied coordinates on the second cell factor. -/
def covariantPolynomialRestriction :
    leftCovariantSubspace i χ →ₗ[k] MvPolynomial σ k :=
  e.toLinearEquiv.toLinearMap.comp (covariantCellRestriction i j χ)

include hq hcell in
theorem covariantPolynomialRestriction_injective :
    Function.Injective (covariantPolynomialRestriction i j χ e) :=
  e.injective.comp (covariantCellRestriction_injective i j χ hq hcell)

/-- The coefficients in a specified finite set of monomials after actual
restriction. No bound or injectivity is built into this definition. -/
def covariantCellCoefficients (S : Finset (σ →₀ ℕ)) :
    leftCovariantSubspace i χ →ₗ[k] (S → k) :=
  LinearMap.pi fun m =>
    (MvPolynomial.lcoeff k m.val).comp (covariantPolynomialRestriction i j χ e)

@[simp]
theorem covariantCellCoefficients_apply (S : Finset (σ →₀ ℕ))
    (f : leftCovariantSubspace i χ) (m : S) :
    covariantCellCoefficients i j χ e S f m =
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).coeff m.val := rfl

include hq hcell in
/-- A uniform finite support bound makes the finite coefficient map faithful
on the entire covariant space. -/
theorem covariantCellCoefficients_injective (S : Finset (σ →₀ ℕ))
    (hsupp : ∀ f : leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).support ⊆ S) :
    Function.Injective (covariantCellCoefficients i j χ e S) := by
  intro f f' he
  apply covariantPolynomialRestriction_injective i j χ hq hcell e
  apply MvPolynomial.ext
  intro m
  by_cases hm : m ∈ S
  · exact congrFun he ⟨m, hm⟩
  · have hf : m ∉ (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).support :=
      fun h => hm (hsupp f h)
    have hf' : m ∉ (e (AffineHomImageHopfAdapter.pullback j (f' : algebra G))).support :=
      fun h => hm (hsupp f' h)
    exact (MvPolynomial.notMem_support_iff.mp hf).trans
      (MvPolynomial.notMem_support_iff.mp hf').symm

include hq hcell in
/-- A finite support bound on restrictions proves finite dimensionality of
the entire covariant space, rather than only of a generated regular subspace. -/
theorem finite_leftCovariantSubspace_of_cell_support (S : Finset (σ →₀ ℕ))
    (hsupp : ∀ f : leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).support ⊆ S) :
    Module.Finite k (leftCovariantSubspace i χ) :=
  Module.Finite.of_injective (covariantCellCoefficients i j χ e S)
    (covariantCellCoefficients_injective i j χ hq hcell e S hsupp)

include hq hcell in
/-- The number of allowed restriction monomials bounds the dimension of the
entire covariant space. -/
theorem finrank_leftCovariantSubspace_le_of_cell_support (S : Finset (σ →₀ ℕ))
    (hsupp : ∀ f : leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).support ⊆ S) :
    Module.finrank k (leftCovariantSubspace i χ) ≤ S.card := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (covariantCellCoefficients_injective i j χ hq hcell e S hsupp)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

include hq hcell in
/-- A coordinatewise monomial degree bound gives an explicit product bound. -/
theorem finrank_leftCovariantSubspace_le_of_cell_degrees (N : σ →₀ ℕ)
    (hdeg : ∀ f : leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).degrees ≤ N.toMultiset) :
    Module.finrank k (leftCovariantSubspace i χ) ≤
      ∏ a ∈ N.support, (N a + 1) := by
  classical
  have hsupp (f : leftCovariantSubspace i χ) :
      (e (AffineHomImageHopfAdapter.pullback j (f : algebra G))).support ⊆ Finset.Iic N := by
    intro m hm
    apply Finset.mem_Iic.mpr
    apply Finsupp.orderIsoMultiset.le_iff_le.mp
    exact (Finset.le_sup hm).trans (hdeg f)
  have h := finrank_leftCovariantSubspace_le_of_cell_support i j χ hq hcell e
    (Finset.Iic N) hsupp
  simpa only [Finsupp.card_Iic, Nat.card_Iic] using h

end Langlands.GroupScheme.AffineCoordinates

namespace Langlands.GroupScheme.Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {H U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom U.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
local instance : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom

variable (i : H ⟶ G) (j : U ⟶ G) (χ : algebra H)
  {q : algebra G} (hq : q ∈ nonZeroDivisors (algebra G))
  (hcell : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
    IsUnit (pointAlgebraHom G T g q) →
      ∃ (a : T ⟶ H.X) (u : T ⟶ U.X),
        g = (a ≫ i.hom.hom) * (u ≫ j.hom.hom))
  {σ : Type v} (e : algebra U ≃ₐ[k] MvPolynomial σ k)

include hq hcell in
/-- Matching a lower dimension bound for a generated regular subspace with
the finite support upper bound proves equality with the entire covariant
space. Neither equality nor irreducibility of that entire space is assumed. -/
theorem affineCovariantSocle_eq_leftCovariantSubspace_of_cell_support
    (S : Finset (σ →₀ ℕ))
    (hsupp : ∀ w : AffineCoordinates.leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (w : algebra G))).support ⊆ S)
    {f : algebra G} (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ)
    (hdim : S.card ≤ Module.finrank k (affineCovariantSocle G f)) :
    affineCovariantSocle G f = AffineCoordinates.leftCovariantSubspace i χ := by
  let := finite_leftCovariantSubspace_of_cell_support i j χ hq hcell e S hsupp
  exact Submodule.eq_of_le_of_finrank_le
    (affineCovariantSocle_le_leftCovariantSubspace G i χ hf)
    ((finrank_leftCovariantSubspace_le_of_cell_support i j χ hq hcell e S hsupp).trans hdim)

include hq hcell in
/-- The restriction bound and a matching socle dimension prove all-test
irreducibility of the entire finite covariant space under the supplied
unipotent cell and normalized invariant-coordinate hypotheses. -/
theorem affineRegularRepresentation_leftCovariant_isIrreducible_of_cell_support
    (hU : IsUnipotent U) (S : Finset (σ →₀ ℕ))
    (hsupp : ∀ w : AffineCoordinates.leftCovariantSubspace i χ,
      (e (AffineHomImageHopfAdapter.pullback j (w : algebra G))).support ⊆ S)
    {f : algebra G} (hf : f ∈ AffineCoordinates.leftCovariantSubspace i χ)
    (hfU : f ∈ rightInvariantSubspace j)
    (hf1 : counit (corepresentation G) f = 1)
    (hdim : S.card ≤ Module.finrank k (affineCovariantSocle G f))
    {m : ℕ} (b : Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i χ)) :
    (affineRegularRepresentation G _ b
      (fun ψ _ hw => AffineCoordinates.rightAct_mem_leftCovariantSubspace i χ ψ hw)
      ).IsIrreducible := by
  have he := affineCovariantSocle_eq_leftCovariantSubspace_of_cell_support
    G i j χ hq hcell e S hsupp hf hdim
  have htransfer (V : Submodule k (algebra G))
      (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
        ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
          w ∈ V → rightAct ψ w ∈ V)
      (hVe : V = affineCovariantSocle G f) (c : Basis (Fin m) k V) :
      (affineRegularRepresentation G V c hV).IsIrreducible := by
    subst V
    exact affineRegularRepresentation_isIrreducible_covariantSocle G c i j hU χ
      hq hcell hf hfU hf1
  exact htransfer _ _ he.symm b

end Langlands.GroupScheme.Chevalley
