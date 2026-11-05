import Langlands.GroupScheme.Rational.MaximalTorusParameter
import Langlands.AlgebraicGeometry.PointTopology.UnirationalSpreading
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descending parameter points of conjugate tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The conjugate of the torus `j₀` by a point `g : X ⟶ G.X` descends along `π : X ⟶ Y`:
whenever two test points of `X` have the same image in `Y`, the corresponding points of `G`
differ by a point of the torus normalizer. -/
def TorusConjugateDescends (j₀ : T₀.toGrp ⟶ G) {X Y : Over (Spec (CommRingCat.of k))}
    (π : X ⟶ Y) (g : X ⟶ G.X) : Prop :=
  ∀ (U : Over (Spec (CommRingCat.of k))) (a₁ a₂ : U ⟶ X), a₁ ≫ π = a₂ ≫ π →
    (a₁ ≫ g)⁻¹ * (a₂ ≫ g) ∈ (torusNormalizer j₀).carrier U

/-- The spectrum of the rational function field of the affine space `𝔸(n; Spec k)`, over
`Spec k`. -/
abbrev rationalFunctionFieldOver (k : Type u) [Field k] (n : Type u) :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk ((𝔸(n; Spec (CommRingCat.of k))).fromSpecStalk
      (genericPoint (𝔸(n; Spec (CommRingCat.of k)))) ≫
    (𝔸(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

variable {j₀ : T₀.toGrp ⟶ G} {Q : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q}

/-- If the conjugate torus descends along an effective epimorphism `π`, then the parameter point
`g ≫ q` descends along `π`. -/
theorem IsMaximalTorusParameter.exists_desc (hq : IsMaximalTorusParameter j₀ q)
    {X Y : Over (Spec (CommRingCat.of k))} (π : X ⟶ Y) [EffectiveEpi π.left]
    (g : X ⟶ G.X) (hg : TorusConjugateDescends j₀ π g) :
    ∃ e : Y ⟶ Q, π ≫ e = g ≫ q := by
  have h : ∀ {Z : Scheme.{u}} (z₁ z₂ : Z ⟶ X.left), z₁ ≫ π.left = z₂ ≫ π.left →
      z₁ ≫ (g ≫ q).left = z₂ ≫ (g ≫ q).left := by
    intro Z z₁ z₂ hz
    let U : Over (Spec (CommRingCat.of k)) := Over.mk (z₁ ≫ X.hom)
    have hz₂ : z₂ ≫ X.hom = z₁ ≫ X.hom := by
      calc z₂ ≫ X.hom = z₂ ≫ π.left ≫ Y.hom := by rw [Over.w π]
        _ = z₁ ≫ π.left ≫ Y.hom := by rw [← Category.assoc, ← hz, Category.assoc]
        _ = z₁ ≫ X.hom := by rw [Over.w π]
    let a₁ : U ⟶ X := Over.homMk z₁ rfl
    let a₂ : U ⟶ X := Over.homMk z₂ hz₂
    have ha : a₁ ≫ π = a₂ ≫ π := by
      ext
      exact hz
    have hfib := (hq.fiber_iff U (a₁ ≫ g) (a₂ ≫ g)).2 (hg U a₁ a₂ ha)
    have := congrArg (fun f : U ⟶ Q => f.left) hfib
    simpa [a₁, a₂] using this
  refine ⟨Over.homMk (EffectiveEpi.desc π.left (g ≫ q).left h) ?_, ?_⟩
  · rw [← cancel_epi π.left, EffectiveEpi.fac_assoc]
    simp
  · ext
    exact EffectiveEpi.fac _ _ h

/-- If the conjugate torus by a point `g` over `X` descends along a flat, surjective,
quasi-compact morphism `π` to the spectrum of the rational function field of `𝔸(n; Spec k)`,
and the parameter point `g ≫ q` has dense image, then `Q` has a dense point over that rational
function field. -/
theorem IsMaximalTorusParameter.hasDenseRationalFunctionFieldPoint
    (hq : IsMaximalTorusParameter j₀ q) {n : Type u} [Finite n]
    {X : Over (Spec (CommRingCat.of k))} (π : X ⟶ rationalFunctionFieldOver k n)
    [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (g : X ⟶ G.X) (hg : TorusConjugateDescends j₀ π g) (hdense : DenseRange (g ≫ q).left) :
    HasDenseRationalFunctionFieldPoint k Q := by
  obtain ⟨e, he⟩ := hq.exists_desc π g hg
  refine ⟨n, inferInstance, e.left, Over.w e, hdense.mono ?_⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨π.left x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]

/-- **Descent reduction.** A point `g` of `G` over `X` with dense image, whose conjugate torus
descends along a flat, surjective, quasi-compact morphism from `X` to the spectrum of the
rational function field of `𝔸(n; Spec k)`, makes every actual parameter scheme unirational. -/
theorem IsMaximalTorusParameter.isUnirational_of_torusConjugateDescends
    (hq : IsMaximalTorusParameter j₀ q) {n : Type u} [Finite n]
    {X : Over (Spec (CommRingCat.of k))} (π : X ⟶ rationalFunctionFieldOver k n)
    [Flat π.left] [Surjective π.left] [QuasiCompact π.left]
    (g : X ⟶ G.X) (hg : TorusConjugateDescends j₀ π g) (hdense : DenseRange g.left) :
    IsUnirational k Q := by
  have : LocallyOfFiniteType Q.hom := hq.locallyOfFiniteType
  have : Surjective q.left := hq.surjective_map
  refine (hq.hasDenseRationalFunctionFieldPoint π g hg ?_).isUnirational
  exact (q.left.surjective.denseRange).comp hdense q.left.continuous

end Langlands.GroupScheme
