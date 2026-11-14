import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-! # Fppf locality of equality of group-scheme homomorphisms -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Equality of actual group-scheme homomorphisms is local on an arbitrary fppf
cover of the base. -/
theorem hom_ext_of_baseChange_fppfCover
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) {f g : G ⟶ H}
    (h : ∀ k, (baseChange (𝒰.f k)).map f = (baseChange (𝒰.f k)).map g) :
    f = g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply CategoryTheory.Precoverage.ZeroHypercover.hom_ext (𝒰.pullback₁ G.X.hom)
  intro k
  change pullback.fst G.X.hom (𝒰.f k) ≫ f.hom.hom.left =
    pullback.fst G.X.hom (𝒰.f k) ≫ g.hom.hom.left
  have hk : (Over.pullback (𝒰.f k)).map f.hom.hom =
      (Over.pullback (𝒰.f k)).map g.hom.hom :=
    congrArg (fun a => a.hom.hom) (h k)
  have hk' := congrArg (fun a => a.left ≫ pullback.fst H.X.hom (𝒰.f k)) hk
  simpa only [Over.pullback_map_left, pullback.lift_fst] using hk'

/-- Fppf neighborhoods of individual base points suffice to detect equality,
without quasi-compactness of the base or the neighborhoods. -/
theorem hom_ext_of_pointwise_fppf_baseChange {f g : G ⟶ H}
    (h : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      Flat b ∧ LocallyOfFinitePresentation b ∧ s ∈ Set.range b ∧
        (baseChange b).map f = (baseChange b).map g) :
    f = g := by
  choose T b hb hp hs he using h
  let 𝒰 : Scheme.Cover Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers S T b
      (fun s => by obtain ⟨t, ht⟩ := hs s; exact ⟨s, t, ht⟩)
      (fun s => ⟨hb s, hp s⟩)
  exact hom_ext_of_baseChange_fppfCover 𝒰 he

/-- Equality of actual homomorphisms is detected on pointwise etale
neighborhoods of the base. -/
theorem hom_ext_of_pointwise_etale_baseChange {f g : G ⟶ H}
    (h : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      Etale b ∧ s ∈ Set.range b ∧
        (baseChange b).map f = (baseChange b).map g) :
    f = g := by
  apply hom_ext_of_pointwise_fppf_baseChange
  intro s
  obtain ⟨T, b, hb, hs, he⟩ := h s
  let : Etale b := hb
  exact ⟨T, b, inferInstance, inferInstance, hs, he⟩

/-- A composite of group-scheme homomorphisms vanishes if it vanishes after
pullback to a pointwise family of etale neighborhoods. -/
theorem comp_eq_zero_of_pointwise_etale_baseChange
    {U P H : GroupScheme S} (r : U ⟶ P) (f : P ⟶ H)
    (h : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      Etale b ∧ s ∈ Set.range b ∧
        (baseChange b).map r ≫ (baseChange b).map f = 0) :
    r ≫ f = 0 := by
  apply hom_ext_of_pointwise_etale_baseChange
  intro s
  obtain ⟨T, b, hb, hs, he⟩ := h s
  exact ⟨T, b, hb, hs, by simpa only [Functor.map_comp, Functor.map_zero] using he⟩

/-- Equality of group-scheme homomorphisms is detected on fppf neighborhoods
through every point of the base. -/
def PointwiseFppfHomEqualityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S) (f g : G ⟶ H),
    (∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S),
      Flat b ∧ LocallyOfFinitePresentation b ∧ s ∈ Set.range b ∧
        (baseChange b).map f = (baseChange b).map g) →
      f = g

/-- Pointwise fppf locality of actual group-scheme homomorphisms. -/
theorem pointwiseFppfHomEquality : PointwiseFppfHomEqualityStatement.{u} := by
  intro S G H f g h
  exact hom_ext_of_pointwise_fppf_baseChange h

end Langlands.GroupScheme
