import Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.SimplyConnected.OuterTypeAQuadraticExtension
import Langlands.LinearAlgebra.CartanE6Root

/-! # The quadratic field of inner type for an outer E6 group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private local instance extendedAffine {F E : Type u} [Field F] [Field E] [Algebra F E]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F E))
  infer_instance

private local instance extendedFiniteType {F E : Type u} [Field F] [Field E] [Algebra F E]
    {G : GroupScheme (Spec (CommRingCat.of F))} [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F E))
  infer_instance

/-- For an actual E6 index with nontrivial star action, the fixed field of
the star kernel is quadratic Galois and its scalar extension is of inner E6
type under a transported Cartan numbering. -/
def TypeE6OuterQuadraticStarFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 6),
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    (¬ ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
    Algebra.IsQuadraticExtension F d.starField ∧ IsGalois F d.starField ∧
      letI := (separableClosure d.starField (AlgebraicClosure d.starField)).algebra
      ∃ (p : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F d.starField)).obj G))
        (f : p.Vertex ≃ Fin 6),
        (∀ a b, p.cartan a b = CartanMatrix.E 6 (f a) (f b)) ∧
        ∀ (τ : SeparableClosure d.starField ≃ₐ[d.starField] SeparableClosure d.starField)
          (a : p.Vertex), p.star τ a = a

theorem typeE6OuterQuadraticStarField : TypeE6OuterQuadraticStarFieldStatement.{u} := by
  classical
  intro F _ G _ _ d e hcart houter
  let s := Langlands.CartanE6Root.symmetry
  have hne : s ≠ 1 := by
    intro h
    have hz := congrArg (fun f : Equiv.Perm (Fin 6) => f 0) h
    exact (by decide : s 0 ≠ 0) hz
  have hcases (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
      (∀ a, e (d.star σ a) = e a) ∨ (∀ a, e (d.star σ a) = s (e a)) :=
    d.star_cases_of_cartan e s hcart Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves σ
  have hpair : d.StarImagePair e s := by
    refine ⟨hne, hcases, ?_⟩
    obtain ⟨σ, hσ⟩ := not_forall.mp houter
    obtain ⟨a, hs⟩ := not_forall.mp hσ
    exact ⟨σ, (hcases σ).resolve_left (fun h => hs (e.injective (h a)))⟩
  let E := d.starField
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let : Algebra.IsSeparable E (SeparableClosure F) :=
    Algebra.isSeparable_tower_top_of_isSeparable F E (SeparableClosure F)
  let : IsSepClosure E (SeparableClosure F) := ⟨inferInstance, inferInstance⟩
  let c : SeparableClosure E ≃ₐ[E] SeparableClosure F := IsSepClosure.equiv _ _ _
  let X := d.separableScalarExtension E c
  let f := X.vertices.symm.trans e
  refine ⟨hpair.isQuadraticExtension, hpair.isGalois, X.index, f, ?_, ?_⟩
  · intro a b
    have h := X.cartan_eq (X.vertices.symm a) (X.vertices.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.trans (hcart _ _)
  · intro τ a
    let σ := (AlgEquiv.autCongr c τ).restrictScalars F
    have hfix (x : SeparableClosure F) (hx : x ∈ E) : σ x = x :=
      (AlgEquiv.autCongr c τ).commutes (⟨x, hx⟩ : E)
    have hin := (d.fixes_starField_iff σ).mp hfix (X.vertices.symm a)
    have hh := X.star_eq τ (X.vertices.symm a)
    rw [show (AlgEquiv.autCongr c τ).restrictScalars F = σ from rfl, hin,
      X.vertices.apply_symm_apply] at hh
    exact hh.symm

end Langlands.GroupScheme
