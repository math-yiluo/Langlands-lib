import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugator
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange

/-! # Transferring generic torus conjugators along field extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

/-- Every rational function field over `K`, regarded over `k` through `b`, is isomorphic over
`k` to a rational function field over `k` in finitely many variables. -/
def ReducesRationalFunctionFields : Prop :=
  ∀ (n : Type u), Finite n → ∃ (n' : Type u) (_ : Finite n'),
    Nonempty ((Over.map b).obj (rationalFunctionFieldOver K n) ≅ rationalFunctionFieldOver k n')

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}

/-- A generic conjugator for the base change of `j₀` along `b` gives a generic conjugator for
`j₀`, when every rational function field over `K` is a rational function field over `k`. -/
theorem HasGenericTorusConjugator.of_baseChange (hb : ReducesRationalFunctionFields b)
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    {j : T.toGrp ⟶ (GroupScheme.baseChange b).obj G}
    (hj : SubgroupFunctor.range j = (SubgroupFunctor.range j₀).baseChange b)
    (h : HasGenericTorusConjugator j) : HasGenericTorusConjugator j₀ := by
  obtain ⟨n, hn, X', π', g', hflat, hsurj, hqc, hdesc, hdense⟩ := h
  obtain ⟨n', hn', ⟨e⟩⟩ := hb n hn
  let X : Over (Spec (CommRingCat.of k)) := (Over.map b).obj X'
  let π : X ⟶ rationalFunctionFieldOver k n' := (Over.map b).map π' ≫ e.hom
  let g : X ⟶ G.X := baseChangePointsEquiv b G X' g'
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hflat
  have := hsurj
  have := hqc
  refine ⟨n', hn', X, π, g, ?_, ?_, ?_, ?_, ?_⟩
  · change Flat (π'.left ≫ e.hom.left)
    infer_instance
  · change Surjective (π'.left ≫ e.hom.left)
    infer_instance
  · change QuasiCompact (π'.left ≫ e.hom.left)
    infer_instance
  · intro U a₁ a₂ ha
    have ha' : a₁ ≫ (Over.map b).map π' = a₂ ≫ (Over.map b).map π' := by
      simpa only [π, ← Category.assoc, cancel_mono] using ha
    let U' : Over (Spec (CommRingCat.of K)) := Over.mk (a₁.left ≫ X'.hom)
    have hleft : a₁.left ≫ π'.left = a₂.left ≫ π'.left := congrArg (fun f => f.left) ha'
    have h₂ : a₂.left ≫ X'.hom = a₁.left ≫ X'.hom := by
      rw [← Over.w π', ← Category.assoc, ← hleft, Category.assoc]
    let a₁' : U' ⟶ X' := Over.homMk a₁.left rfl
    let a₂' : U' ⟶ X' := Over.homMk a₂.left h₂
    have h' := hdesc U' a₁' a₂' (by ext; exact hleft)
    rw [torusNormalizer, hj] at h'
    have h'' := SubgroupFunctor.normalizer_le_baseChange b _ U' h'
    rw [SubgroupFunctor.mem_baseChange, map_mul, map_inv] at h''
    let isoU : U ≅ (Over.map b).obj U' :=
      Over.isoMk (Iso.refl _) (by simpa [U', X] using Over.w a₁)
    have hU := (SubgroupFunctor.range j₀).normalizer.comp_mem isoU.hom h''
    have e₁ : isoU.hom ≫ baseChangePointsEquiv b G U' (a₁' ≫ g') = a₁ ≫ g := by
      rw [baseChangePointsEquiv_naturality, ← Category.assoc]
      congr 1
    have e₂ : isoU.hom ≫ baseChangePointsEquiv b G U' (a₂' ≫ g') = a₂ ≫ g := by
      rw [baseChangePointsEquiv_naturality, ← Category.assoc]
      congr 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, e₁, e₂] at hU
    exact hU
  · have hfst : Surjective (pullback.fst G.X.hom b) := by
      rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst, range_eq_univ,
        Set.preimage_univ]
    change DenseRange (g'.left ≫ pullback.fst G.X.hom b)
    exact ((pullback.fst G.X.hom b).surjective.denseRange).comp hdense
      (pullback.fst G.X.hom b).continuous

end Langlands.GroupScheme
