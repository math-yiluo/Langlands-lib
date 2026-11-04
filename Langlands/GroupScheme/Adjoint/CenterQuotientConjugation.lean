import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.GroupScheme.Adjoint.CenterQuotientLinearAlgebra

/-! # Conjugates of a point with commuting conjugates

Over an algebraically closed field, let `G` be a reduced connected group scheme locally of
finite type with a matrix representation `ρ`, and let `h` be a rational point whose matrix
commutes with the matrices of all its rational conjugates. Then every rational commutator
`g h g⁻¹ h⁻¹` acts unipotently through `ρ`. The proof applies the nested-block criterion of
`CenterQuotientLinearAlgebra`; the nesting of the blocks comes from connectedness of `G`
through an idempotent determinant function. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.CenterQuotient

open CentralIntersection

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Evaluating the inverse universal matrix at a rational point gives the inverse of the
matrix of that point. -/
theorem evalPoint_mapMatrix_pointMatrix_inv (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (CentralIntersection.evalPoint g).mapMatrix
        (((ρ.pointMatrix G.X (𝟙 G.X))⁻¹ : GL n Γ(G.X.left, ⊤)) : Matrix n n Γ(G.X.left, ⊤)) =
      (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K) := by
  have hmul : (CentralIntersection.evalPoint g).mapMatrix
        (ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)) *
      (CentralIntersection.evalPoint g).mapMatrix
        (((ρ.pointMatrix G.X (𝟙 G.X))⁻¹ : GL n Γ(G.X.left, ⊤)) :
          Matrix n n Γ(G.X.left, ⊤)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [RingHom.mapMatrix_apply (CentralIntersection.evalPoint g)
    (ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)),
    evalPoint_mapMatrix_pointMatrix] at hmul
  calc _ = (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K) *
        ((ρ.rationalMatrix g : Matrix n n K) * (CentralIntersection.evalPoint g).mapMatrix
          (((ρ.pointMatrix G.X (𝟙 G.X))⁻¹ : GL n Γ(G.X.left, ⊤)) :
            Matrix n n Γ(G.X.left, ⊤))) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [hmul, mul_one]

/-- A conjugate of an idempotent by a unit is idempotent. -/
theorem isIdempotentElem_units_conj {A : Type*} [Ring A] (u : Aˣ) {π : A}
    (hπ : IsIdempotentElem π) : IsIdempotentElem ((u : A) * π * ((u⁻¹ : Aˣ) : A)) := by
  rw [IsIdempotentElem, ← pow_two, Units.conj_pow, pow_two, hπ.eq]

variable [IsAlgClosed K] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
  [ConnectedSpace G.X.left]

/-- **Connectedness of the nesting.** For an idempotent matrix `π` commuting with each of its
rational conjugates `ρ(g) π ρ(g)⁻¹`, every such conjugate absorbs `π`:
`π (ρ(g) π ρ(g)⁻¹) = π`. The function `det (π M π M⁻¹ + (1 - π))` on `G`, with `M` the
universal matrix, is idempotent because it is so at every rational point; it is `1` at the
identity, hence `1` by connectedness. -/
theorem mul_conj_eq_of_commute (ρ : MatrixRepresentation G n) {π : Matrix n n K}
    (hπ : IsIdempotentElem π)
    (hcomm : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      Commute π ((ρ.rationalMatrix g : Matrix n n K) * π *
        (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K)))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    π * ((ρ.rationalMatrix g : Matrix n n K) * π *
      (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K)) = π := by
  set M := ρ.pointMatrix G.X (𝟙 G.X) with hMdef
  set p := (scalarMap G.X).mapMatrix π with hpdef
  set F : Γ(G.X.left, ⊤) :=
    (p * ((M : Matrix n n Γ(G.X.left, ⊤)) * p * ((M⁻¹ : GL n Γ(G.X.left, ⊤)) :
      Matrix n n Γ(G.X.left, ⊤))) + (1 - p)).det with hFdef
  have hev : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      CentralIntersection.evalPoint g F = (π * ((ρ.rationalMatrix g : Matrix n n K) * π *
        (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K)) + (1 - π)).det := by
    intro g
    rw [hFdef, RingHom.map_det]
    congr 1
    rw [map_add, map_sub, map_one, map_mul, map_mul, map_mul, hpdef,
      evalPoint_mapMatrix_scalarMap, evalPoint_mapMatrix_pointMatrix_inv,
      RingHom.mapMatrix_apply (CentralIntersection.evalPoint g) (M : Matrix n n Γ(G.X.left, ⊤)), hMdef,
      evalPoint_mapMatrix_pointMatrix]
  have hidem : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      IsIdempotentElem (π * ((ρ.rationalMatrix g : Matrix n n K) * π *
        (((ρ.rationalMatrix g)⁻¹ : GL n K) : Matrix n n K)) + (1 - π)) := fun g =>
    isIdempotentElem_mul_add_one_sub hπ (isIdempotentElem_units_conj _ hπ) (hcomm g)
  have hF : IsIdempotentElem F := by
    rw [IsIdempotentElem, ← sub_eq_zero]
    refine eq_zero_of_forall_evalPoint_eq_zero _ fun g => ?_
    rw [map_sub, map_mul, hev, sub_eq_zero]
    exact (isIdempotentElem_det (hidem g)).eq
  have hF1 : CentralIntersection.evalPoint 1 F = 1 := by
    rw [hev, map_one, inv_one, Units.val_one, one_mul, mul_one, hπ.eq, add_sub_cancel,
      Matrix.det_one]
  rcases eq_zero_or_eq_one_of_isIdempotentElem hF with h0 | h1
  · rw [h0, map_zero] at hF1
    exact absurd hF1 zero_ne_one
  · have hdet := hev g
    rw [h1, map_one] at hdet
    have hE := eq_one_of_isIdempotentElem_of_det_eq_one (hidem g) hdet.symm
    have := eq_sub_of_add_eq hE
    rwa [sub_sub_cancel] at this

/-- **Commutators with a point having commuting conjugates are unipotent.** If the matrix of a
rational point `h` commutes with the matrix of every rational conjugate `g h g⁻¹`, then every
rational commutator `g h g⁻¹ h⁻¹` acts unipotently through `ρ`. -/
theorem isNilpotent_rationalMatrix_commutator_sub_one (ρ : MatrixRepresentation G n)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (hcomm : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      Commute (ρ.rationalMatrix h : Matrix n n K) (ρ.rationalMatrix (g * h * g⁻¹)))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    IsNilpotent ((ρ.rationalMatrix (g * h * g⁻¹ * h⁻¹) : Matrix n n K) - 1) := by
  set γ := (ρ.rationalMatrix h : Matrix n n K) with hγ
  have hconj : ∀ g' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      (ρ.rationalMatrix (g' * h * g'⁻¹) : Matrix n n K) =
        (ρ.rationalMatrix g' : Matrix n n K) * γ *
          (((ρ.rationalMatrix g')⁻¹ : GL n K) : Matrix n n K) := by
    intro g'
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  set γ' := (ρ.rationalMatrix (g * h * g⁻¹) : Matrix n n K) with hγ'
  have hN : IsNilpotent (γ' - γ) := by
    refine isNilpotent_sub_of_forall_blockPolynomial γ γ' (hcomm g) ?_
    intro c c' hne hc hc'
    obtain ⟨P, hP1, hP0, hPidem⟩ := exists_blockPolynomial γ hc
    refine ⟨P, hP1, hP0 c' ?_ (Ne.symm hne), ?_⟩
    · rw [hγ', hconj, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hc'
      exact hc'
    · rw [hγ', hconj, aeval_units_conj]
      refine mul_conj_eq_of_commute ρ hPidem (fun g' => ?_) g
      rw [← aeval_units_conj, ← hconj]
      exact commute_aeval (hcomm g') P P
  have hcomm' : Commute ((ρ.rationalMatrix h : GL n K) : Matrix n n K) γ' := hcomm g
  have := isNilpotent_mul_inv_sub_one (ρ.rationalMatrix h) γ' hcomm' hN
  rwa [hγ', ← Units.val_mul, ← map_inv, ← map_mul] at this

end Langlands.GroupScheme.CenterQuotient
