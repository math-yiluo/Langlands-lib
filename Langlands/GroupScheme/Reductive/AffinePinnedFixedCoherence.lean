import Langlands.GroupScheme.Reductive.AffinePinnedFixedExistence

/-! # Coherence and descent of canonical fixed pinned comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N K : AffinePinnedModel.{u}}
    (θ : RootPairing.Equiv N.rootDatum M.rootDatum)
    (hθ : ∀ s : N.rootIndex, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support)
    (ρ : RootPairing.Equiv K.rootDatum N.rootDatum)
    (hρ : ∀ s : K.rootIndex, s ∈ K.basis.support ↔ ρ.indexEquiv s ∈ N.basis.support)

include hθ hρ in
/-- The composition of the specified based-datum equivalences matches bases. -/
theorem fixedBasis_comp (s : K.rootIndex) :
    s ∈ K.basis.support ↔ (θ.comp ρ).indexEquiv s ∈ M.basis.support :=
  (hρ s).trans (hθ (ρ.indexEquiv s))

/-- Fixed simple-root correspondences compose without relabelling choices. -/
theorem fixedSimpleEquiv_comp (s : K.basis.support) :
    fixedSimpleEquiv (θ.comp ρ) (fixedBasis_comp θ hθ ρ hρ) s =
      fixedSimpleEquiv θ hθ (fixedSimpleEquiv ρ hρ s) :=
  Subtype.ext rfl

/-- The whole-lattice fixed torus maps compose in the actual group category. -/
theorem fixedTorusIso_comp (T : Scheme.{u}) :
    (fixedTorusIso θ T).hom ≫ (fixedTorusIso ρ T).hom =
      (fixedTorusIso (θ.comp ρ) T).hom := by
  classical
  change CommGroupScheme.groupHom
    (splitTorus.exponentHom T M.coordinates N.coordinates θ.weightMap ≫
      splitTorus.exponentHom T N.coordinates K.coordinates ρ.weightMap) = _
  exact congrArg CommGroupScheme.groupHom
    (splitTorus.exponentHom_comp T M.coordinates N.coordinates K.coordinates
      θ.weightMap ρ.weightMap)

variable {T : Scheme.{u}} {f : T ⟶ M.base} {g : T ⟶ N.base} {k : T ⟶ K.base}

/-- Compose actual fixed pinned comparisons, retaining the composed full
datum map and precisely its fixed simple-root correspondence. -/
def FixedComparison.trans (e : FixedComparison θ hθ f g)
    (d : FixedComparison ρ hρ g k) :
    FixedComparison (θ.comp ρ) (fixedBasis_comp θ hθ ρ hρ) f k := by
  refine ⟨e.val ≪≫ d.val, ?_, ?_⟩
  · change M.inclusionOver f ≫ e.val.hom ≫ d.val.hom = _
    rw [← Category.assoc, e.property.1, Category.assoc, d.property.1,
      ← Category.assoc, fixedTorusIso_comp]
  · intro A _ _ _ a ha hc s
    let : Algebra N.ring A := (Spec.preimage (a ≫ g)).hom.toAlgebra
    have hb : algebraBaseMap N.ring A = a ≫ g := Spec.map_preimage _
    have he := e.property.2 A a ha hb (fixedSimpleEquiv ρ hρ s)
    have hd := d.property.2 A a hb hc s
    change M.rootVectorPoint f A a ha
      (fixedSimpleEquiv (θ.comp ρ) (fixedBasis_comp θ hθ ρ hρ) s) ≫
        e.val.hom.hom.hom.left ≫ d.val.hom.hom.hom.left = _
    rw [fixedSimpleEquiv_comp θ hθ ρ hρ s, ← Category.assoc, he, hd]

/-- The identity datum gives the actual identity torus map. -/
theorem fixedTorusIso_id (M : AffinePinnedModel.{u}) (T : Scheme.{u}) :
    (fixedTorusIso (RootPairing.Equiv.id M.rootDatum) T).hom = 𝟙 _ := by
  classical
  change CommGroupScheme.groupHom
    (splitTorus.exponentHom T M.coordinates M.coordinates LinearMap.id) = _
  rw [splitTorus.exponentHom_id]
  rfl

/-- The actual identity comparison has the identity fixed datum. -/
def FixedComparison.refl (M : AffinePinnedModel.{u}) (f : T ⟶ M.base) :
    FixedComparison (RootPairing.Equiv.id M.rootDatum) (fun _ => Iff.rfl) f f := by
  refine ⟨Iso.refl _, ?_, ?_⟩
  · change M.inclusionOver f ≫ 𝟙 _ =
      (fixedTorusIso (RootPairing.Equiv.id M.rootDatum) T).hom ≫ M.inclusionOver f
    rw [fixedTorusIso_id, Category.comp_id, Category.id_comp]
  · intro A _ α β a ha hb s
    have hαβ : α = β := by
      apply Algebra.algebra_ext
      intro r
      have hm := congrArg
        (fun z : Spec (CommRingCat.of A) ⟶ M.base => (Spec.preimage z).hom r)
        (ha.trans hb.symm)
      simp only [algebraBaseMap, Spec.preimage_map] at hm
      change α.algebraMap r = β.algebraMap r at hm
      exact hm
    cases hαβ
    exact Category.comp_id _

/-- Canonical fixed comparisons carry identity datum to identity comparison. -/
theorem fixedComparison_refl (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (M : AffinePinnedModel.{u}) (f : T ⟶ M.base) :
    (fixedComparison (RootPairing.Equiv.id M.rootDatum) (fun _ => Iff.rfl) hAffine f f).val =
      Iso.refl _ :=
  (fixedComparison_unique _ _ hAffine f f (FixedComparison.refl M f)).symm

/-- Canonical comparisons for successive fixed data compose coherently. -/
theorem fixedComparison_trans (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (k : T ⟶ K.base) :
    (fixedComparison (θ.comp ρ) (fixedBasis_comp θ hθ ρ hρ) hAffine f k).val =
      (fixedComparison θ hθ hAffine f g).val ≪≫
        (fixedComparison ρ hρ hAffine g k).val :=
  (fixedComparison_unique _ _ hAffine f k
    ((fixedComparison θ hθ hAffine f g).trans θ hθ ρ hρ
      (fixedComparison ρ hρ hAffine g k))).symm

variable {V : Scheme.{u}}

/-- Canonical comparison values on any cover are independent of the cover
point because they are the actual pullback of the canonical global comparison. -/
theorem fixedComparison_isIndependent
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (p : V ⟶ T) :
    (comparisonLocalIso p (fixedComparison θ hθ hAffine (p ≫ f) (p ≫ g)).val).IsIndependent := by
  rw [← fixedComparison_pull θ hθ hAffine f g p]
  unfold comparisonLocalIso
  rw [comparisonToIterated_pullComparison]
  exact LocalGroupIso.ofBaseChangeIso_mapIso_isIndependent _

/-- Descend the canonical local comparison along any single fppf cover. -/
def fixedComparisonDescended (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (p : V ⟶ T)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p] : Comparison f g :=
  descendComparison p (fixedComparison θ hθ hAffine (p ≫ f) (p ≫ g)).val
    (fixedComparison_isIndependent θ hθ hAffine f g p)

/-- The descended comparison is exactly the canonical global comparison,
independently of the chosen single fppf cover. -/
theorem fixedComparisonDescended_eq
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (p : V ⟶ T)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p] :
    fixedComparisonDescended θ hθ hAffine f g p = (fixedComparison θ hθ hAffine f g).val := by
  apply pullComparison_injective p
  exact (pullComparison_descendComparison p _ _).trans
    (fixedComparison_pull θ hθ hAffine f g p).symm

end Langlands.GroupScheme.AffinePinnedModel
