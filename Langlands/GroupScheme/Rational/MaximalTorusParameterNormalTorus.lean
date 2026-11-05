import Langlands.GroupScheme.Rational.MaximalTorusParameter
import Langlands.AlgebraicGeometry.PointTopology.UnirationalSpreading

/-! # The parameter scheme of a maximal torus whose normalizer is the whole group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]

/-- A ground-field rational point with dense image makes a scheme unirational. -/
theorem IsUnirational.of_section_denseRange {X : Over (Spec (CommRingCat.of k))}
    (s : Spec (CommRingCat.of k) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _) (hdense : DenseRange s) :
    IsUnirational k X := by
  let A := 𝔸(PEmpty.{u + 1}; Spec (CommRingCat.of k))
  let V : A.Opens := ⊤
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨a, -⟩ := (A ↘ Spec (CommRingCat.of k)).surjective t
  have hV : (V : Set A).Nonempty := ⟨a, trivial⟩
  refine (isUnirational_affineSpace (k := k) PEmpty.{u + 1}).of_open_denseRange
    (Y := Over.mk (A ↘ Spec (CommRingCat.of k))) V hV
    (V.ι ≫ (A ↘ Spec (CommRingCat.of k)) ≫ s) ?_ ?_
  · simp [hs]
  · refine hdense.mono ?_
    rintro _ ⟨b, rfl⟩
    refine ⟨⟨a, trivial⟩, ?_⟩
    change s ((A ↘ Spec (CommRingCat.of k)) (V.ι ⟨a, trivial⟩)) = s b
    rw [Subsingleton.elim ((A ↘ Spec (CommRingCat.of k)) (V.ι ⟨a, trivial⟩)) b]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {j₀ : T₀.toGrp ⟶ G}
  {Q : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q}

/-- If every point of `G`, over every test scheme, normalizes the torus, then the
image of the identity section is the only point of the parameter scheme. -/
theorem IsMaximalTorusParameter.range_one_eq_univ (hq : IsMaximalTorusParameter j₀ q)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X),
      g ∈ (torusNormalizer j₀).carrier U) :
    Set.range ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q).left = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have : Surjective q.left := hq.surjective_map
  obtain ⟨x, rfl⟩ := q.left.surjective y
  let U : Over (Spec (CommRingCat.of k)) :=
    Over.mk (G.X.left.fromSpecResidueField x ≫ G.X.hom)
  let g : U ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField x) rfl
  let a : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk U.hom (by simp)
  have hfib : g ≫ q = (1 : U ⟶ G.X) ≫ q := (hq.fiber_iff U g 1).2 (hN U _)
  have hone : (1 : U ⟶ G.X) = a ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
    (MonObj.comp_one a).symm
  obtain ⟨p⟩ : Nonempty (Spec (G.X.left.residueField x)) := inferInstance
  refine ⟨a.left p, ?_⟩
  have h := congrArg (fun f : U ⟶ Q => f.left p) hfib
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  rw [hone] at h
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h ⊢
  rw [← h]
  exact congrArg q.left (Scheme.fromSpecResidueField_apply (X := G.X.left) x p)

/-- **Base case.** If every point of `G`, over every test scheme, normalizes the
maximal torus, then every actual parameter scheme is unirational. -/
theorem IsMaximalTorusParameter.isUnirational_of_normalizer_eq_top
    (hq : IsMaximalTorusParameter j₀ q)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X),
      g ∈ (torusNormalizer j₀).carrier U) :
    IsUnirational k Q := by
  refine IsUnirational.of_section_denseRange
    ((1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ≫ q).left ?_ ?_
  · simp
  · rw [DenseRange, hq.range_one_eq_univ hN]
    exact dense_univ

end Langlands.GroupScheme
