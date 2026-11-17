import Langlands.GroupScheme.Reductive.AffinePinnedFixedComparison
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent
import Langlands.GroupScheme.FppfHomLocality

/-! # Affine pinned solutions and rigidity on arbitrary common schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}}
  (θ : RootPairing.Equiv N.rootDatum M.rootDatum)
  (hθ : ∀ s : N.rootIndex, s ∈ N.basis.support ↔ θ.indexEquiv s ∈ M.basis.support)

/-- The fixed torus map has exactly the prescribed character formula on
all relative tests over the whole common scheme. -/
theorem fixedTorusIso_characters (T : Scheme.{u})
    (U : Over T) (x : U ⟶ (splitTorus T M.coordinates).X) (m : N.coordinates → ℤ) :
    ∏ j, splitTorus.pointsEquiv N.coordinates U
        (x ≫ (fixedTorusIso θ T).hom.hom.hom) j ^ m j =
      ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ θ.weightMap m i := by
  classical
  have ht : (fixedTorusIso θ T).hom ≫
      CommGroupScheme.groupHom (splitTorus.exponentCharacter T N.coordinates m) =
        CommGroupScheme.groupHom (splitTorus.exponentCharacter T M.coordinates (θ.weightMap m)) := by
    change CommGroupScheme.groupHom
      (splitTorus.exponentHom T M.coordinates N.coordinates θ.weightMap ≫
        splitTorus.exponentCharacter T N.coordinates m) = _
    exact congrArg CommGroupScheme.groupHom
      (splitTorus.exponentHom_comp_exponentCharacter T M.coordinates N.coordinates θ.weightMap m)
  rw [← splitTorus.pointsEquiv_exponentCharacter,
    Category.assoc, ← Grp.comp_hom_hom, ht,
    splitTorus.pointsEquiv_exponentCharacter]

local instance scalarAffine (P : AffinePinnedModel.{u})
    (A : Type u) [CommRing A] [Algebra P.ring A] :
    IsAffineHom (P.groupOver (algebraBaseMap P.ring A)).X.hom :=
  (P.reductive.baseChange (algebraBaseMap P.ring A)).isAffineHom

variable (A : Type u) [CommRing A] [Algebra M.ring A] [Algebra N.ring A]

/-- The exact affine pinned theorem's predicate for the scalar extensions
of the two original models to the same coefficient ring. -/
def IsAffineSolution
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)) : Prop :=
  (∃ τ : splitTorus (Spec (CommRingCat.of A)) M.coordinates ≅
      splitTorus (Spec (CommRingCat.of A)) N.coordinates,
    (M.scalarExtension A).inclusion ≫ e.hom = τ.hom ≫ (N.scalarExtension A).inclusion ∧
    ∀ (U : Over (Spec (CommRingCat.of A)))
      (x : U ⟶ (splitTorus (Spec (CommRingCat.of A)) M.coordinates).X)
      (m : N.coordinates → ℤ),
      ∏ j, splitTorus.pointsEquiv N.coordinates U (x ≫ τ.hom.hom.hom) j ^ m j =
        ∏ i, splitTorus.pointsEquiv M.coordinates U x i ^ θ.weightMap m i) ∧
    ∀ s : N.basis.support,
      Lie.targetMapLinear e.hom (CommRingCat.of A)
          ((M.scalarExtension A).pinning (fixedSimpleEquiv θ hθ s) 1).val =
        ((N.scalarExtension A).pinning s 1).val

/-- Applying the supplied affine pinned Isomorphism Theorem to the actual
scalar-extended models gives the unique exact affine solution. -/
theorem existsUnique_affineSolution
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) :
    ∃! e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A),
      IsAffineSolution θ hθ A e := by
  let L := M.scalarExtension A
  let K := N.scalarExtension A
  exact hAffine A L.group K.group L.reductive K.reductive
    L.coordinates K.coordinates L.inclusion K.inclusion L.rootIndex K.rootIndex
    L.rootDatum K.rootDatum L.closed L.maximal L.fibrewiseRootDatum L.rootLines
    K.closed K.maximal K.fibrewiseRootDatum K.rootLines
    L.basis K.basis L.pinning K.pinning θ hθ

/-- Choose the actual affine pinned solution from the supplied full
faithfulness theorem; its precise predicate remains in the specification. -/
def affineSolution (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) :
    Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A) :=
  Classical.choose (existsUnique_affineSolution θ hθ A hAffine)

/-- The chosen affine solution has the exact torus/character and differential laws. -/
theorem affineSolution_spec (hAffine : AffinePinnedIsomorphismTheoremStatement.{u}) :
    IsAffineSolution θ hθ A (affineSolution θ hθ A hAffine) :=
  (Classical.choose_spec (existsUnique_affineSolution θ hθ A hAffine)).1

/-- Fixed comparison data on a coefficient spectrum satisfy the exact
scalar-extended affine theorem's predicate. -/
theorem FixedComparison.isAffineSolution
    (e : FixedComparison θ hθ (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)) :
    IsAffineSolution θ hθ A e.val := by
  refine ⟨⟨fixedTorusIso θ _, e.property.1, fixedTorusIso_characters θ _⟩, ?_⟩
  intro s
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (((M.scalarExtension A).pinning (fixedSimpleEquiv θ hθ s) 1).val.toMul.val).left ≫
      e.val.hom.hom.hom.left =
    (((N.scalarExtension A).pinning s 1).val.toMul.val).left
  rw [scalarExtension_pinning_point, scalarExtension_pinning_point]
  exact e.property.2 A (𝟙 _) (by simp) (by simp) s

/-- Affine full faithfulness makes any two fixed comparisons over a
coefficient spectrum equal. -/
theorem FixedComparison.eq_of_affineTheorem
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    (e d : FixedComparison θ hθ (algebraBaseMap M.ring A) (algebraBaseMap N.ring A)) :
    e.val = d.val :=
  ExistsUnique.unique (existsUnique_affineSolution θ hθ A hAffine)
    (e.isAffineSolution θ hθ A) (d.isAffineSolution θ hθ A)

/-- The supplied equal-endpoint pullback has the expected actual comparison. -/
theorem FixedComparison.pullAlong_val {T W : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base}
    (e : FixedComparison θ hθ f g) (q : W ⟶ T)
    {f' : W ⟶ M.base} {g' : W ⟶ N.base} (hf : q ≫ f = f') (hg : q ≫ g = g') :
    (e.pullAlong θ hθ q hf hg).val = pullComparisonAlong e.val q hf hg := by
  subst f'
  subst g'
  simp only [FixedComparison.pullAlong, FixedComparison.pull_val, pullComparisonAlong_rfl]

/-- Reindexing the equal endpoints of a pullback preserves and reflects
equality of actual comparisons. -/
theorem pullComparisonAlong_eq_iff {T W : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base} (e d : Comparison f g) (q : W ⟶ T)
    {f' : W ⟶ M.base} {g' : W ⟶ N.base} (hf : q ≫ f = f') (hg : q ≫ g = g') :
    pullComparisonAlong e q hf hg = pullComparisonAlong d q hf hg ↔
      pullComparison e q = pullComparison d q := by
  subst f'
  subst g'
  simp only [pullComparisonAlong_rfl]

/-- Affine full faithfulness gives uniqueness of fixed comparisons over
any common test scheme, including non-affine and disconnected schemes. -/
theorem FixedComparison.eq_of_affineTheorem_scheme
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})
    {T : Scheme.{u}} {f : T ⟶ M.base} {g : T ⟶ N.base}
    (e d : FixedComparison θ hθ f g) : e.val = d.val := by
  apply Iso.ext
  apply hom_ext_of_pointwise_etale_baseChange
  intro s
  obtain ⟨j, x, hx⟩ := T.affineOpenCover.openCover.exists_eq s
  let q := T.affineOpenCover.f j
  let A := T.affineOpenCover.X j
  let : Algebra M.ring A := (Spec.preimage (q ≫ f)).hom.toAlgebra
  let : Algebra N.ring A := (Spec.preimage (q ≫ g)).hom.toAlgebra
  have hf : q ≫ f = algebraBaseMap M.ring A := (Spec.map_preimage _).symm
  have hg : q ≫ g = algebraBaseMap N.ring A := (Spec.map_preimage _).symm
  have heq := FixedComparison.eq_of_affineTheorem θ hθ A hAffine
    (e.pullAlong θ hθ q hf hg) (d.pullAlong θ hθ q hf hg)
  rw [FixedComparison.pullAlong_val, FixedComparison.pullAlong_val] at heq
  have hp : pullComparison e.val q = pullComparison d.val q :=
    (pullComparisonAlong_eq_iff e.val d.val q hf hg).mp heq
  have hm := congrArg (comparisonToIterated q) hp
  simp only [comparisonToIterated_pullComparison] at hm
  exact ⟨_, q, inferInstance, ⟨x, hx⟩, congrArg Iso.hom hm⟩

end Langlands.GroupScheme.AffinePinnedModel
