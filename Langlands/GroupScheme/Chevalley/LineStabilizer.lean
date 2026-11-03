import Langlands.GroupScheme.Chevalley.CoordinateRestriction
import Langlands.GroupScheme.Chevalley.TensorCoordinates
import Langlands.GroupScheme.Chevalley.MatrixExterior
import Langlands.GroupScheme.Chevalley.ReindexRepresentation

/-! # Chevalley line stabilizers on all scheme tests -/

noncomputable section

universe u

open Module CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Classical CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding

variable {R : CommRingCat.{u}}
  {F H : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B C : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (H ⋙ forget GrpCat).CorepresentableBy C)
  (α : H ⟶ F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite-type corepresented group and an arbitrary closed subgroup admit an
actual finite matrix representation with an exact unit-scalar line stabilizer
on every scheme test. -/
theorem exists_corepresented_line_stabilizer
    (hR : IsField R) [Algebra.FiniteType R B]
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α)) :
    ∃ (N r : ℕ) (s : Fin r ↪o Fin N)
      (ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Set.powersetCard (Fin N) r)),
      ∀ (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X),
        x ∈ (SubgroupFunctor.range (Corepresented.groupSchemeMap d e α)).carrier T ↔
          ∃ u : Γ(T.left, ⊤)ˣ,
            (ρ.pointMatrix T x :
              Matrix (Set.powersetCard (Fin N) r) (Set.powersetCard (Fin N) r) Γ(T.left, ⊤)) *ᵥ
                Pi.single (Set.powersetCard.ofFinEmbEquiv s) 1 =
              (u : Γ(T.left, ⊤)) •
                (Pi.single (Set.powersetCard.ofFinEmbEquiv s) (1 : Γ(T.left, ⊤)) :
                  Set.powersetCard (Fin N) r → Γ(T.left, ⊤)) := by
  let := hR.toField
  let := bialgebra e
  let := bialgebra d
  let q := coordinateRestrictionBialgHom e d α
  have hq : Function.Surjective q := coordinateRestriction_surjective e d α hc
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨V, hfinite, hV, hcrit⟩ := exists_finite_subspace_stabilizer q hq
    (Ideal.fg_of_isNoetherianRing _)
  let := hfinite
  let W := idealSubspace V q.toLinearMap
  obtain ⟨N, r, b, s, hW⟩ := exists_adapted_subspace_basis V W inf_le_left
  let σ := regularRepresentation e hR V b hV
  refine ⟨N, r, s, exteriorRepresentation N r R σ, ?_⟩
  intro T x
  let A := ((algΓ R).obj T).unop
  let f : B →ₐ[R] A := (e.homEquiv.symm (Corepresented.pointsEquiv F e T x)).hom
  have hm : (σ.pointMatrix T x : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      ((subspaceMatrix V b).map f : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) := by
    ext i j
    exact regularRepresentation_pointMatrix e hR V b hV T x i j
  rw [exteriorRepresentation_pointMatrix]
  calc
    x ∈ (SubgroupFunctor.range (Corepresented.groupSchemeMap d e α)).carrier T ↔
        ∃ ψ : C →ₐ[R] A, ψ.comp q.toAlgHom = f :=
      mem_range_iff_coordinate_factors e d α T x
    _ ↔ (∀ w : B, w ∈ W → translate f.toLinearMap w ∈ tensorSubspace W A) :=
      (hcrit A f).symm
    _ ↔ (∀ v : Fin N → A,
        v ∈ coordinateSpan (Pi.basisFun A (Fin N)) s.toEmbedding →
        (subspaceMatrix V b).map f *ᵥ v ∈
          coordinateSpan (Pi.basisFun A (Fin N)) s.toEmbedding) :=
      stabilizes_iff_matrix_preserves V b s.toEmbedding hV W hW f.toLinearMap
    _ ↔ _ := by
      rw [← hm]
      exact (exteriorGL_basisLine_iff s (σ.pointMatrix T x)).symm

/-- The line stabilizer can be put in a positive finite coordinate dimension. -/
theorem exists_corepresented_line_stabilizer_fin
    (hR : IsField R) [Algebra.FiniteType R B]
    (hc : IsClosedSubgroup (Corepresented.groupSchemeMap d e α)) :
    ∃ (n : ℕ) (j : Fin (n + 1))
      (ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin (n + 1))),
      ∀ (T : Over (Spec R)) (x : T ⟶ (Corepresented.groupScheme F e).X),
        x ∈ (SubgroupFunctor.range (Corepresented.groupSchemeMap d e α)).carrier T ↔
          ∃ u : Γ(T.left, ⊤)ˣ,
            (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
                Pi.single j 1 =
              (u : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) :
                Fin (n + 1) → Γ(T.left, ⊤)) := by
  obtain ⟨N, r, s, ρ, hρ⟩ := exists_corepresented_line_stabilizer e d α hR hc
  let J := Set.powersetCard (Fin N) r
  let t : J := Set.powersetCard.ofFinEmbEquiv s
  have : Nonempty J := ⟨t⟩
  have hpos : 0 < Fintype.card J := Fintype.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hpos)
  let indexEquiv : J ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn
  refine ⟨n, indexEquiv t, reindexRepresentation indexEquiv R ρ, ?_⟩
  intro T x
  rw [reindexRepresentation_pointMatrix, reindexGL_basisLine_iff]
  exact hρ T x

end Langlands.GroupScheme.Chevalley
