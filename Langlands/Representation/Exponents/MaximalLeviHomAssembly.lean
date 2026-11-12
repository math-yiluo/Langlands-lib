import Langlands.Representation.Filtration.HomGluing
import Langlands.Representation.Schur.TwistedPieceHom
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Geometric.SelfIntersectionPiece

/-! Algebraic and adjunction assembly for the maximal-Levi morphism dichotomy. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.HomSpace

universe uK uG uV uW uC vC

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {W : Type uW} [AddCommGroup W] [Module k W]
variable {C : Type uC} [Category.{vC} C]

/-- A nonzero map out of a naturally glued representation forces a nonzero map out of
one of the supplied pieces. -/
theorem exists_piece_ne_zero_of_isGluedFrom
    {F : C ⥤ Rep.{uV} k G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} k G}
    (h : IsGluedFrom F pieces) (X : C) (σ : Representation k G W)
    (f : (F.obj X).ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ i : Fin n, ∃ g : ((pieces i).obj X).ρ.IntertwiningMap σ, g ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  have hzero : ∀ i, length ((pieces i).obj X).ρ σ = 0 := by
    intro i
    apply Module.length_eq_zero_iff.mpr
    exact ⟨fun g g' => (hne i g).trans (hne i g').symm⟩
  have hlen : length (F.obj X).ρ σ = 0 := by
    refine le_antisymm ?_ zero_le
    calc
      length (F.obj X).ρ σ ≤ ∑ i : Fin n, length ((pieces i).obj X).ρ σ :=
        length_le_sum_of_isGluedFrom h X σ
      _ = 0 := Finset.sum_eq_zero fun i _ => hzero i
  have : Subsingleton ((F.obj X).ρ.IntertwiningMap σ) := Module.length_eq_zero_iff.mp hlen
  exact hf (Subsingleton.elim _ _)

end Langlands.HomSpace

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- The actual linear equivalence `Hom_G(i_P^G τ', i_P^G τ) ≃ Hom_M(r_P^G(i_P^G τ'), τ)`
supplied by proved Frobenius reciprocity, at independent field and carrier universes. -/
def homReciprocityEquiv :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ τ τ' : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        ((leviInductionFunctor p l r hp hr hl hmul).obj τ').representation.IntertwiningMap
            ((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation ≃ₗ[ℂ]
          ((leviJacquetInductionFunctor p l r hp hr hl hmul p l r hp hr hl hmul).obj τ').ρ.IntertwiningMap
            τ.representation := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro τ τ'
  exact (leviFrobeniusReciprocity k G hG P M U p l r hp hl hr hmul
    ((leviInductionFunctor p l r hp hr hl hmul).obj τ') τ).choose

/-- The exact morphism dichotomy follows from the full represented geometric lemma. The
geometric lemma is an explicit premise of this conditional result. -/
theorem maximalLeviSupercuspidalInductionHom_of_geometricLemma
    (hgeo : RepresentedGeometricLemmaStatement.{u, v}) :
    MaximalLeviSupercuspidalInductionHomStatement.{u, v} := by
  classical
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul _hproper _hmax
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro τ τ' hirr hirr' _hsuper hsuper' f hf
  have : τ.representation.IsIrreducible := hirr
  have : τ'.representation.IsIrreducible := hirr'
  obtain ⟨n, c, z, hz, D, hglue⟩ :=
    hgeo k G hG P M N P M N p l r hp hl hr hmul p l r hp hl hr hmul
  have hsurj (ψ : M ≅ M) : Function.Surjective (rationalPoints.map ψ.hom) := by
    intro m
    refine ⟨rationalPoints.map ψ.inv m, ?_⟩
    rw [← pointMap_comp_apply, ψ.inv_hom_id]
    simp [rationalPoints.map_apply]
  have hinj : Function.Injective (rationalPoints.map (l ≫ p)) := by
    intro x y hxy
    apply (leviPointsEquiv p l hp hl).injective
    exact Subtype.ext hxy
  -- The Frobenius image of `f` is a nonzero map `r_P^G(i_P^G τ') → τ`.
  let e := homReciprocityEquiv k G hG P M N p l r hp hl hr hmul τ τ'
  have hf0 : e (SmoothRep.hom f) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hf
    apply hx
    have h1 : SmoothRep.hom f = 0 := e.injective (h0.trans (map_zero e).symm)
    rw [h1]
    rfl
  -- Some graded piece of the geometric lemma maps nonzero to `τ`.
  obtain ⟨i, S, hS⟩ := HomSpace.exists_piece_ne_zero_of_isGluedFrom hglue τ'
    τ.representation (e (SmoothRep.hom f)) hf0
  rcases (D i).subsingleton_or_exists_selfPieceEquiv τ' hsuper' with
    hzero | ⟨_, ψ, hψ, T, hT⟩
  · exfalso
    apply hS
    ext x
    change S.toLinearMap x = 0
    have := hzero
    have hx : x = 0 := Subsingleton.elim _ _
    simp only [hx, map_zero]
  -- The piece is `τ'` twisted by `ψ`, so `S ∘ T⁻¹` identifies `τ' ∘ ψ` with `τ`.
  let α := rationalPoints.map ψ.hom
  let S' : τ' →ₗ[ℂ] τ := S.toLinearMap.comp T.symm.toLinearMap
  have hS' : S' ≠ 0 := by
    intro h
    apply hS
    ext x
    change S.toLinearMap x = 0
    have hx := LinearMap.congr_fun h (T x)
    simpa only [S', LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using hx
  have hcov : ∀ m y, S' (τ'.representation (α m) y) = τ.representation m (S' y) := by
    intro m y
    have hinv : T.symm (τ'.representation (α m) y) =
        ((D i).pieceFunctor.obj τ').ρ m (T.symm y) := by
      apply T.injective
      rw [T.apply_symm_apply, hT, T.apply_symm_apply]
    change S (T.symm (τ'.representation (α m) y)) = τ.representation m (S (T.symm y))
    rw [hinv]
    exact Representation.IntertwiningMap.isIntertwining _ _ S m (T.symm y)
  let E := (Schur.twistedIntertwinerEquiv τ'.representation τ.representation α
    (hsurj ψ) S' hS' hcov).symm
  have hE : ∀ m x, E (τ.representation m x) = τ'.representation (α m) (E x) :=
    fun m x => Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap m x
  by_cases hzi : z i ∈ pointImage (l ≫ p)
  · -- `z i = m₀` lies in the Levi image: `ψ` is conjugation by `m₀`, and
    -- `τ'(m₀)⁻¹ ∘ E` is an isomorphism `τ ≅ τ'`.
    left
    obtain ⟨m₀, hm₀⟩ := hzi
    have hα : ∀ m, α m = m₀ * m * m₀⁻¹ := by
      intro m
      apply hinj
      calc
        rationalPoints.map (l ≫ p) (α m) = rationalPoints.map (ψ.hom ≫ l ≫ p) m :=
          (pointMap_comp_apply ψ.hom (l ≫ p) m).symm
        _ = rationalPoints.map ((l ≫ p) ≫ (G.innerIso (z i)).hom) m := by
          rw [hψ, Category.assoc]
        _ = z i * rationalPoints.map (l ≫ p) m * (z i)⁻¹ := by
          rw [pointMap_comp_apply, rationalPoints_map_innerIso]
          rfl
        _ = rationalPoints.map (l ≫ p) (m₀ * m * m₀⁻¹) := by
          rw [← hm₀, map_mul, map_mul, map_inv]
    let A : τ' ≃ₗ[ℂ] τ' := LinearEquiv.ofLinearMap (τ'.representation m₀⁻¹)
      (τ'.representation m₀)
      (by ext y; simp) (by ext y; simp)
    let R : τ.representation.Equiv τ'.representation :=
      Representation.Equiv.mk (E.toLinearEquiv.trans A) (fun m => by
        ext x
        change τ'.representation m₀⁻¹ (E (τ.representation m x)) =
          τ'.representation m (τ'.representation m₀⁻¹ (E x))
        rw [hE, hα, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group)
    exact ⟨SmoothRep.mkIso R.symm⟩
  · -- Otherwise `g = z i` and `φ = ψ` give the exceptional alternative.
    right
    exact ⟨z i, ψ, hψ, hzi, E.toLinearEquiv, hE⟩

end Langlands.Aubert.General.RepresentedParabolic
