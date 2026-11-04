import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterStatement

/-! # Reduction of the finite-field envelope compatibility -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open EnvelopeInfiniteReduction

/-- Grothendieck's theorem on maximal tori under field extension, conjugacy of maximal tori
over an algebraically closed field, and a maximal torus over a finite field whose conjugates
all lie in the closed torus envelope together give the finite-field compatibility of the
closed torus envelope with algebraic closure. -/
theorem torusGeneratedEnvelopeAlgebraicClosureFinite_of
    (hbc : MaximalTorusBaseChangeStatement.{u})
    (hconj : MaximalTorusConjugacyStatement.{u})
    (htr : FiniteFieldMaximalTorusTransporterStatement.{u}) :
    TorusGeneratedEnvelopeAlgebraicClosureFiniteStatement.{u} := by
  intro k _ _ G _ _ _
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let GK := F.obj G
  rw [closedTorusEnvelope_baseChange_eq_iff_containsTori K G]
  have : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom GK.X.hom := TorusExistence.isAffineHom_baseChange K G
  have : ConnectedSpace GK.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨T₀, j₀, hj₀, htr₀⟩ := htr k G
  have hj₀K : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T₀) (F.map j₀) :=
    (hbc k K G T₀ j₀ hj₀.1 hj₀.2.1).1 hj₀
  -- Every `K`-conjugate of `(T₀)_K` lies in the base-changed envelope.
  have hconjle : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ GK.X,
      SubgroupFunctor.range (F.map j₀ ≫ (GK.innerIso g).hom) ≤
        (closedTorusEnvelope G).baseChange b := by
    intro g T' y hy
    obtain ⟨t, rfl⟩ := hy
    let x : T' ⟶ GK.X := t ≫ (F.map j₀).hom.hom
    let c : T' ⟶ GK.X := GK.constantPoint g T'
    have hy : t ≫ (F.map j₀ ≫ (GK.innerIso g).hom).hom.hom = c * x * c⁻¹ := by
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    change t ≫ (F.map j₀ ≫ (GK.innerIso g).hom).hom.hom ∈
      ((closedTorusEnvelope G).baseChange b).carrier T'
    rw [hy, SubgroupFunctor.mem_baseChange, map_mul, map_mul, map_inv]
    apply htr₀
    have hx : x ∈ (SubgroupFunctor.range (F.map j₀)).carrier T' := ⟨t, rfl⟩
    rw [SubgroupFunctor.range_baseChangeHom] at hx
    exact hx
  -- Every closed `K`-torus lies in a maximal one, which is a conjugate of `(T₀)_K`.
  intro S i hS hi
  obtain ⟨S', i', f, hi', hf⟩ := exists_isMaximalTorus_factor GK i hS hi
  obtain ⟨g, φ, hg⟩ := hconj K GK ((CommGroupScheme.baseChange b).obj T₀) S' (F.map j₀) i' hj₀K hi'
  have hi'eq : i' = CommGroupScheme.groupHom φ.inv ≫ (CommGroupScheme.groupHom φ.hom ≫ i') := by
    rw [← Category.assoc]
    change i' = CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ i'
    rw [φ.inv_hom_id]
    exact (Category.id_comp i').symm
  calc SubgroupFunctor.range i = SubgroupFunctor.range (f ≫ i') := by rw [hf]
    _ ≤ SubgroupFunctor.range i' := SubgroupFunctor.range_comp_le f i'
    _ ≤ SubgroupFunctor.range (CommGroupScheme.groupHom φ.hom ≫ i') := by
      conv_lhs => rw [hi'eq]
      exact SubgroupFunctor.range_comp_le _ _
    _ = SubgroupFunctor.range (F.map j₀ ≫ (GK.innerIso g).hom) := by rw [hg]
    _ ≤ (closedTorusEnvelope G).baseChange b := hconjle g

end Langlands.GroupScheme
