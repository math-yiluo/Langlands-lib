import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Interface
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Points
import Langlands.GroupScheme.Rational.Characters

/-! # The split Cayley automorphism group scheme has trivial centre

An automorphism matrix of Zorn's algebra commuting with the twelve root elements `x_α(1)` is the
identity, over every commutative ring (`centerRigidity`). Hence the scheme-theoretic centre of the
automorphism group scheme is trivial (`center_eq_bot`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

/-! ### Rigidity of central matrices -/

section Rigidity

variable {A : Type u} [CommRing A]

/-- A matrix commuting with `x_α(1)` intertwines its action on vectors. -/
theorem rootFun_mulVec_of_commute {g : Matrix (Fin 8) (Fin 8) A} {α : Root}
    (h : Commute g (rootMatrix α 1)) (v : Fin 8 → A) :
    rootFun α 1 (g *ᵥ v) = g *ᵥ rootFun α 1 v := by
  rw [← rootMatrix_mulVec, ← rootMatrix_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.eq]

theorem centerRigidity : CenterRigidityStatement.{u} := by
  intro A _ g hg hcomm
  obtain ⟨hu, hm⟩ := hg
  set w := g *ᵥ Pi.single 0 1 with hw_def
  -- the long root elements fix `e₀`, hence fix `w`
  have hlong : ∀ α : Root, rootFun α (1 : A) (Pi.single 0 1) = Pi.single 0 1 →
      rootFun α 1 w = w := by
    intro α hα
    rw [hw_def, rootFun_mulVec_of_commute (hcomm α), hα]
  have f12 := hlong .l12 (by funext i; fin_cases i <;> simp [rootFun])
  have f21 := hlong .l21 (by funext i; fin_cases i <;> simp [rootFun])
  have f13 := hlong .l13 (by funext i; fin_cases i <;> simp [rootFun])
  have f31 := hlong .l31 (by funext i; fin_cases i <;> simp [rootFun])
  have w2 : w 2 = 0 := by simpa [rootFun] using congrFun f12 1
  have w4 : w 4 = 0 := by simpa [rootFun] using congrFun f12 5
  have w1 : w 1 = 0 := by simpa [rootFun] using congrFun f21 2
  have w5 : w 5 = 0 := by simpa [rootFun] using congrFun f21 4
  have w3 : w 3 = 0 := by simpa [rootFun] using congrFun f13 1
  have w6 : w 6 = 0 := by simpa [rootFun] using congrFun f31 4
  -- the short root elements move `e₀` to `e₀ + eᵢ`
  have hshort : ∀ (α : Root) (i : Fin 8),
      rootFun α (1 : A) (Pi.single 0 1) = Pi.single 0 1 + Pi.single i 1 →
      g *ᵥ Pi.single i 1 = rootFun α 1 w - w := by
    intro α i hα
    rw [hw_def, rootFun_mulVec_of_commute (hcomm α), hα, Matrix.mulVec_add, add_sub_cancel_left]
  have s1 := hshort .u1 1 (by funext i; fin_cases i <;> simp [rootFun])
  have s4 := hshort .v1 4 (by funext i; fin_cases i <;> simp [rootFun])
  -- `g e₁ = c e₁` and `g e₄ = c e₄` with `c = w₀ - w₇`
  have e1 : g *ᵥ Pi.single 1 1 = (w 0 - w 7) • Pi.single 1 1 := by
    rw [s1]
    funext i
    fin_cases i <;> simp [rootFun, w1, w2, w3, w4, w5, w6]
  have e4 : g *ᵥ Pi.single 4 1 = (w 0 - w 7) • Pi.single 4 1 := by
    rw [s4]
    funext i
    fin_cases i <;> simp [rootFun, w1, w2, w3, w4, w5, w6]
  have m14 : mulFun A (Pi.single 1 1) (Pi.single 4 1) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [mulFun]
  have m41 : mulFun A (Pi.single 4 1) (Pi.single 1 1) = Pi.single 7 1 := by
    funext i; fin_cases i <;> simp [mulFun]
  have k14 := hm (Pi.single 1 1) (Pi.single 4 1)
  have k41 := hm (Pi.single 4 1) (Pi.single 1 1)
  rw [m14, e1, e4] at k14
  rw [m41, e1, e4] at k41
  have hs7 : (Pi.single 7 1 : Fin 8 → A) = unit A - Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [unit]
  rw [hs7, Matrix.mulVec_sub, hu] at k41
  have w7 : w 7 = 0 := by
    have h := congrFun k14 7
    simp [mulFun] at h
    rw [hw_def, Matrix.mulVec_single_one]
    simpa using h
  have w0 : w 0 = 1 := by
    have h := congrFun k41 0
    simp [mulFun, unit, ← hw_def] at h
    exact (sub_eq_zero.1 h).symm
  -- now `g e₀ = e₀`, and every coordinate vector is fixed
  have hc0 : g *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [← hw_def]
    funext i
    fin_cases i <;> simp [w0, w1, w2, w3, w4, w5, w6, w7]
  have hfix : ∀ (α : Root) (i : Fin 8),
      rootFun α (1 : A) (Pi.single 0 1) = Pi.single 0 1 + Pi.single i 1 →
      g *ᵥ Pi.single i 1 = Pi.single i 1 := by
    intro α i hα
    have hw0 : w = Pi.single 0 1 := hc0
    rw [hshort α i hα, hw0, hα, add_sub_cancel_left]
  have hcol : ∀ j : Fin 8, g *ᵥ Pi.single j 1 = Pi.single j 1 := by
    intro j
    fin_cases j
    · exact hc0
    · exact hfix .u1 1 (by funext i; fin_cases i <;> simp [rootFun])
    · exact hfix .u2 2 (by funext i; fin_cases i <;> simp [rootFun])
    · exact hfix .u3 3 (by funext i; fin_cases i <;> simp [rootFun])
    · exact hfix .v1 4 (by funext i; fin_cases i <;> simp [rootFun])
    · exact hfix .v2 5 (by funext i; fin_cases i <;> simp [rootFun])
    · exact hfix .v3 6 (by funext i; fin_cases i <;> simp [rootFun])
    · show g *ᵥ Pi.single 7 1 = Pi.single 7 1
      rw [hs7, Matrix.mulVec_sub, hu, hc0]
  ext i j
  have := congrFun (hcol j) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply] using this

end Rigidity

/-! ### The centre of the group scheme -/

section Center

variable {K : Type u} [Field K]

/-- The point of the automorphism group scheme over a test scheme given by the root element
`x_α(1)`. -/
def rootOnePoint (T : Over (Spec (CommRingCat.of K))) (α : Root) :
    T ⟶ (CayleyDatum.split K).automorphismGroup.X :=
  (pointsEquiv K T).symm ⟨rootGL α 1,
    (mem_automorphismSubgroup_split_iff _ _).2 (isAutomorphism_rootGL α 1)⟩

theorem pointsEquiv_rootOnePoint (T : Over (Spec (CommRingCat.of K))) (α : Root) :
    ((pointsEquiv K T (rootOnePoint T α) : GL (Fin 8) Γ(T.left, ⊤)) :
        Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) = rootMatrix α 1 := by
  rw [rootOnePoint, MulEquiv.apply_symm_apply]
  rfl

variable (K) in
/-- **Trivial centre.** The scheme-theoretic centre of the automorphism group scheme of Zorn's
split Cayley algebra is trivial. -/
theorem center_eq_bot : center (CayleyDatum.split K).automorphismGroup = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    have hcomm : ∀ α : Root, Commute
        ((pointsEquiv K T x : GL (Fin 8) Γ(T.left, ⊤)) : Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤))
        (rootMatrix α 1) := by
      intro α
      have h := commute_of_mem_center hx (rootOnePoint T α)
      have h' := (h.map (pointsEquiv K T).toMonoidHom).map (Subgroup.subtype _)
      have h'' := h'.map (Units.coeHom (Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)))
      rw [← pointsEquiv_rootOnePoint T α]
      exact h''
    have hg := (mem_automorphismSubgroup_split_iff _ _).1 (pointsEquiv K T x).2
    have h1 := centerRigidity Γ(T.left, ⊤) _ hg hcomm
    apply (pointsEquiv K T).injective
    rw [map_one]
    exact Subtype.ext (Units.ext h1)
  · rintro rfl
    exact Subgroup.one_mem _

end Center

end SplitCayley

end Langlands.GroupScheme
