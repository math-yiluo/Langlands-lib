import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugatorInduction
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReductionStatement

/-! # The two cases of the maximal-torus conjugator reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Translate

variable {k K : Type u} [Field k] [Field K]
  {b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of K))} {T : CommGroupScheme (Spec (CommRingCat.of K))}
  {j₀ : T₀.toGrp ⟶ G} {j : T.toGrp ⟶ H}
  {i : H ⟶ (GroupScheme.baseChange b).obj G} {Y : Over (Spec (CommRingCat.of K))}

/-- Transfer data for a left translate `p = i(h₁) · c`: the density condition holds as soon as
`c`, viewed in `G` over `k`, has dense range. -/
theorem isTorusConjugatorTransfer_of_translate (hflat : Flat Y.hom) (hsurj : Surjective Y.hom)
    (hqc : QuasiCompact Y.hom) (h₁ : Y ⟶ H.X) (c : Y ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hconj : ∀ (V : Over (Spec (CommRingCat.of K))) (y : V ⟶ Y)
        (t : V ⟶ ((GroupScheme.baseChange b).obj G).X),
      t ∈ ((SubgroupFunctor.range j₀).baseChange b).carrier V ↔
        (y ≫ ((h₁ ≫ i.hom.hom) * c)) * t * (y ≫ ((h₁ ≫ i.hom.hom) * c))⁻¹ ∈
          (SubgroupFunctor.range (j ≫ i)).carrier V)
    (hc : DenseRange (baseChangePointsEquiv b G Y c).left) :
    IsTorusConjugatorTransfer b j₀ j i Y ((h₁ ≫ i.hom.hom) * c) := by
  refine ⟨hflat, hsurj, hqc, hconj, ?_⟩
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd H.X.hom Y.hom ≫ Y.hom)
  let f₁ : P ⟶ H.X := Over.homMk (pullback.fst H.X.hom Y.hom) pullback.condition
  let f₂ : P ⟶ Y := Over.homMk (pullback.snd H.X.hom Y.hom) rfl
  let m : P ⟶ ((GroupScheme.baseChange b).obj G).X :=
    (f₁ ≫ i.hom.hom) * (f₂ ≫ ((h₁ ≫ i.hom.hom) * c))
  let s : Y ⟶ P := Over.homMk (pullback.lift (h₁⁻¹).left (𝟙 Y.left)
    (by rw [Over.w, Category.id_comp])) (by
      simp only [P, Over.mk_hom]
      rw [pullback.lift_snd_assoc, Category.id_comp])
  have e₁ : s ≫ f₁ = h₁⁻¹ := by
    ext
    simp only [s, f₁, Over.comp_left, Over.homMk_left]
    rw [pullback.lift_fst]
  have e₂ : s ≫ f₂ = 𝟙 Y := by
    ext
    simp only [s, f₂, Over.comp_left, Over.homMk_left, Over.id_left]
    rw [pullback.lift_snd]
  let f := IsMonHom.monoidHom i.hom.hom Y
  have hf : ∀ y : Y ⟶ H.X, f y = y ≫ i.hom.hom := fun _ => rfl
  have hsm : s ≫ m = c := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, e₁, e₂, Category.id_comp,
      ← hf, ← hf, map_inv, inv_mul_cancel_left]
  have hdense' : DenseRange (baseChangePointsEquiv b G P m).left := by
    have hnat := baseChangePointsEquiv_naturality b G s m
    rw [hsm] at hnat
    rw [hnat, Over.comp_left] at hc
    exact hc.mono (Set.range_comp_subset_range _ _)
  exact hdense'

end Translate

section Cases

variable {k : Type u} [Field k]

/-- The base change of `G` to an algebraic closure of `k` has a semisimple Lie element whose
Lie centralizer is not everything. -/
def HasNoncentralGeometricSemisimpleElement (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] : Prop :=
  let Gbar := (GroupScheme.baseChange (toAlgebraicClosure k)).obj G
  letI : IsAffineHom Gbar.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  ∃ X : lieKernel Gbar (AlgebraicClosure k),
    Lie.IsSemisimpleElement Gbar X ∧ Lie.elementCentralizerLie Gbar X ≠ ⊤

variable {G : GroupScheme (Spec (CommRingCat.of k))} {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A reduction below `d` is a reduction below every larger bound. -/
theorem HasSmallerTorusConjugatorReduction.mono {j₀ : T₀.toGrp ⟶ G} {d d' : ℕ}
    (h : HasSmallerTorusConjugatorReduction j₀ d) (hd : d ≤ d') :
    HasSmallerTorusConjugatorReduction j₀ d' := by
  obtain ⟨K, hK, b, hb, H, h₁, h₂, h₃, T, j, i, Y, p, hj, hH, htr⟩ := h
  exact ⟨K, hK, b, hb, H, h₁, h₂, h₃, T, j, i, Y, p, hj, lt_of_lt_of_le hH hd, htr⟩

end Cases

/-- **Case B: isogeny step.** Every maximal torus `j₀` of a smooth connected affine group `G`
over a field maps, along a flat, surjective, quasi-compact, universally open homomorphism
`φ : G ⟶ G'` onto a smooth connected affine group of no larger Lie dimension that reflects
torus normalizers, to a maximal torus `j₀'` of `G'`. Moreover either every point of `G'`
normalizes `j₀'`, or `G'` has a geometric semisimple Lie element that is not central. -/
def MaximalTorusIsogenyReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ →
      ∃ (G' : GroupScheme (Spec (CommRingCat.of k))) (_ : Smooth G'.X.hom)
        (_ : IsAffineHom G'.X.hom) (_ : ConnectedSpace G'.X.left)
        (T₀' : CommGroupScheme (Spec (CommRingCat.of k))) (j₀' : T₀'.toGrp ⟶ G')
        (φ : G ⟶ G'),
        Flat φ.hom.hom.left ∧ Surjective φ.hom.hom.left ∧ QuasiCompact φ.hom.hom.left ∧
          UniversallyOpen φ.hom.hom.left ∧ ReflectsTorusNormalizer φ j₀ j₀' ∧
          IsMaximalTorus j₀' ∧ Lie.dimension G' ≤ Lie.dimension G ∧
          ((∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G'.X),
              g ∈ (torusNormalizer j₀').carrier U) ∨
            HasNoncentralGeometricSemisimpleElement G')

/-- **Case C: generic semisimple centralizer step.** If a smooth connected affine group over a
field has a geometric semisimple Lie element that is not central, then each of its maximal
tori reduces to a maximal torus of a group of smaller Lie dimension. -/
def SemisimpleCentralizerConjugatorReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ → HasNoncentralGeometricSemisimpleElement G →
      HasSmallerTorusConjugatorReduction j₀ (Lie.dimension G)

/-- The two cases give the reduction statement. -/
theorem maximalTorusConjugatorReduction_of_cases
    (hB : MaximalTorusIsogenyReductionStatement.{u})
    (hC : SemisimpleCentralizerConjugatorReductionStatement.{u}) :
    MaximalTorusConjugatorReductionStatement.{u} := by
  intro k _ G _ _ _ T₀ j₀ hj₀
  obtain ⟨G', _, _, _, T₀', j₀', φ, h₁, h₂, h₃, h₄, hφ, hj₀', hdim, hcase⟩ :=
    hB k G T₀ j₀ hj₀
  refine ⟨G', inferInstance, inferInstance, T₀', j₀', φ, h₁, h₂, h₃, h₄, hφ, ?_⟩
  rcases hcase with hN | hS
  · exact Or.inl hN
  · exact Or.inr ((hC k G' T₀' j₀' hj₀' hS).mono hdim)

/-- The two cases give unirationality of every actual parameter scheme. -/
theorem maximalTorusParameterUnirational_of_cases
    (hB : MaximalTorusIsogenyReductionStatement.{u})
    (hC : SemisimpleCentralizerConjugatorReductionStatement.{u}) :
    MaximalTorusParameterUnirationalStatement.{u} :=
  maximalTorusParameterUnirational_of_reduction (maximalTorusConjugatorReduction_of_cases hB hC)

end Langlands.GroupScheme
