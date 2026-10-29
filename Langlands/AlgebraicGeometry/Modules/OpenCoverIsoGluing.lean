import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluingStatement

/-! # Isomorphism gluing from unique gluing of module morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- Compatible isomorphisms between the actual pullbacks of two fixed module
sheaves glue uniquely, with the prescribed forward maps on every cover member. -/
def OpenCoverIsoGluingStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (𝒰 : X.OpenCover.{u}) (M N : X.Modules)
    (e : ∀ i,
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).obj M ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).obj N),
    (∀ i j,
      (AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.fst (𝒰.f i) (𝒰.f j))).map (e i).hom ≫
          (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition N).hom =
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom ≫
          (AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd (𝒰.f i) (𝒰.f j))).map (e j).hom) →
    ∃! E : M ≅ N, ∀ i,
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map E.hom = (e i).hom

private lemma comp_eq_id_of_local_inverse
    (hglue : OpenCoverHomGluingStatement.{u})
    (X : AlgebraicGeometry.Scheme.{u}) (𝒰 : X.OpenCover.{u}) (M N : X.Modules)
    (f : M ⟶ N) (g : N ⟶ M)
    (h : ∀ i,
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map f ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map g = 𝟙 _) :
    f ≫ g = 𝟙 M := by
  obtain ⟨q, _, hq⟩ := hglue X 𝒰 M M (fun _ ↦ 𝟙 _) (by
    intro i j
    simp)
  apply (hq (f ≫ g) ?_).trans (hq (𝟙 M) ?_).symm
  · intro i
    simpa only [Functor.map_comp] using h i
  · intro i
    simp

/-- Unique gluing of module morphisms supplies unique gluing of isomorphisms.
The morphism-gluing proposition remains an explicit input. -/
theorem openCoverIsoGluing_of_homGluing
    (hglue : OpenCoverHomGluingStatement.{u}) :
    OpenCoverIsoGluingStatement.{u} := by
  intro X 𝒰 M N e he
  obtain ⟨f, hf, hfunique⟩ := hglue X 𝒰 M N (fun i ↦ (e i).hom) he
  have hinv : ∀ i j,
      (AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.fst (𝒰.f i) (𝒰.f j))).map (e i).inv ≫
          (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom =
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition N).hom ≫
          (AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd (𝒰.f i) (𝒰.f j))).map (e j).inv := by
    intro i j
    apply (Iso.inv_comp_eq
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.fst (𝒰.f i) (𝒰.f j))).mapIso (e i))).2
    simp only [Functor.mapIso_hom]
    rw [← Category.assoc, he i j]
    simp only [Category.assoc, Iso.map_hom_inv_id, Category.comp_id]
  obtain ⟨g, hg, _⟩ := hglue X 𝒰 N M (fun i ↦ (e i).inv) hinv
  have hfg : f ≫ g = 𝟙 M := comp_eq_id_of_local_inverse hglue X 𝒰 M N f g (by
    intro i
    rw [hf i, hg i]
    exact (e i).hom_inv_id)
  have hgf : g ≫ f = 𝟙 N := comp_eq_id_of_local_inverse hglue X 𝒰 N M g f (by
    intro i
    rw [hg i, hf i]
    exact (e i).inv_hom_id)
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro E hE
  apply Iso.ext
  exact hfunique E.hom hE

end Langlands.Scheme.Modules
