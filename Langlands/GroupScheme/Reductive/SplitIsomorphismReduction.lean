import Langlands.GroupScheme.Reductive.SplitIsomorphismStatement
import Langlands.GroupScheme.Reductive.SplitRankOneIsomorphismStatement
import Langlands.GroupScheme.Reductive.SplitLeviGluingStatement
import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.Dynamic.CentralizerRootsProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Reduction of the Isomorphism Theorem to semisimple rank at most one -/

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Subgroup

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom Z.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (t : T.toGrp ⟶ Z) (z : Z ⟶ G) (htz : t ≫ z = i)
  {J : Type v} {J' : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T) (cocharacterLattice T)}

include htz in
/-- Let the torus `i : T ⟶ G` factor as `t ≫ z` through `Z`. If the full normalizer image of
`i` is finite, then a root common to a root datum of `t` and a root datum of `i` has the same
coroot in both: the reflection realized in `Z` is also realized in `G`. -/
theorem IsRootDatumOf.coroot_eq_of_comp_of_mono_of_finite_weylImage
    [Mono i.hom.hom.left] [Mono t.hom.hom.left] [Finite (weylImage i)]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf t Q) {j : J} {j' : J'}
    (hroot : P.root j = Q.root j') : P.coroot j = Q.coroot j' := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
  obtain ⟨m, τ, hm, hτ⟩ := hQ.2.2 j'
  let n' : normalizerPoints i := ⟨n, σ, hn⟩
  let m' : normalizerPoints t := ⟨m, τ, hm⟩
  have hs : weylAction i n' = P.reflection j := by
    ext χ
    rw [weylAction_eq i (n := n') (σ := σ) hn χ]
    change characterAut σ χ = _
    rw [hσ]
  have ht : weylAction i (normalizerPointsMap t z i htz m') = Q.reflection j' := by
    rw [weylAction_normalizerPointsMap]
    ext χ
    rw [weylAction_eq t (n := m') (σ := τ) hm χ]
    change characterAut τ χ = _
    rw [hτ]
  let a : weylImage i := ⟨weylAction i n', n', rfl⟩
  let b : weylImage i := ⟨weylAction i (normalizerPointsMap t z i htz m'), _, rfl⟩
  have horder : IsOfFinOrder (P.reflection j * Q.reflection j') := by
    have h := (weylImage i).subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i n' * weylAction i (normalizerPointsMap t z i htz m')) at h
    rwa [hs, ht] at h
  let f := (latticePairing T).flip (P.coroot j)
  let g := (latticePairing T).flip (Q.coroot j')
  have hf : f (P.root j) = 2 := by
    change latticePairing T (P.root j) (P.coroot j) = 2
    rw [← hP.1]
    exact P.root_coroot_two j
  have hg : g (P.root j) = 2 := by
    change latticePairing T (P.root j) (Q.coroot j') = 2
    rw [hroot, ← hQ.1]
    exact Q.root_coroot_two j'
  have heq := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections
    (P.root j) f g (P.reflection j) (Q.reflection j') hf hg
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - P.toLinearMap χ (P.coroot j) • P.root j = _
      rw [hP.1]
      rfl)
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - Q.toLinearMap χ (Q.coroot j') • Q.root j' = _
      rw [hQ.1, ← hroot]
      rfl) horder
  apply P.flip.toPerfPair.injective
  ext χ
  change P.toLinearMap χ (P.coroot j) = P.toLinearMap χ (Q.coroot j')
  rw [hP.1]
  exact LinearMap.congr_fun heq χ

end Subgroup

/-- **Isomorphism Theorem from semisimple rank at most one.** The Isomorphism Theorem for two
connected reductive groups sharing a split maximal torus follows from four statements: existence
of root data, reductivity of the centralizers of cocharacters, the Isomorphism Theorem in
semisimple rank at most one, and the gluing step which assembles an isomorphism from
isomorphisms of the centralizers of semisimple rank at most one. The roots of those centralizers
are given by the proved `dynamicCentralizerRoots`. -/
theorem splitCommonTorusIsomorphism_of_leviGluing
    (hRD : RootDatumExistenceStatement.{u}) (hCent : DynamicCentralizerReductiveStatement.{u})
    (hA : SplitRankOneCommonTorusIsomorphismStatement.{u})
    (hC : SplitCommonTorusLeviGluingStatement.{u}) :
    SplitCommonTorusIsomorphismStatement.{u} := by
  have hB := dynamicCentralizerRoots.{u}
  intro k _ G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hroot hcoroot
  refine hC k G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hroot hcoroot ?_
  intro ν hrank Z₁ Z₂ z₁ z₂ hz₁ hz₂ hrep₁ hrep₂ t₁ t₂ ht₁ ht₂
  -- The centralizers are connected reductive, with maximal tori `t₁` and `t₂`.
  have hZ₁ := hCent k G₁ hG₁ _ Z₁ z₁ hz₁ hrep₁
  have hZ₂ := hCent k G₂ hG₂ _ Z₂ z₂ hz₂ hrep₂
  have hti₁ : IsMaximalTorus t₁ := IsMaximalTorus.of_comp hz₁ (ht₁ ▸ hi₁)
  have hti₂ : IsMaximalTorus t₂ := IsMaximalTorus.of_comp hz₂ (ht₂ ▸ hi₂)
  have := hG₁.isAffineHom
  have := hG₂.isAffineHom
  have := hZ₁.isAffineHom
  have := hZ₂.isAffineHom
  have := hG₁.smooth
  have := hG₂.smooth
  have : IsClosedImmersion i₁.hom.hom.left := hi₁.2.1
  have : IsClosedImmersion i₂.hom.hom.left := hi₂.2.1
  have : IsClosedImmersion t₁.hom.hom.left := hti₁.2.1
  have : IsClosedImmersion t₂.hom.hom.left := hti₂.2.1
  have : Finite (weylImage i₁) := splitTorusWeylImageFinite k G₁ T hT i₁ hi₁.2.1
  have : Finite (weylImage i₂) := splitTorusWeylImageFinite k G₂ T hT i₂ hi₂.2.1
  -- Root data of the centralizers, and their common roots.
  obtain ⟨K₁, _, Q₁, hQ₁, -⟩ := hRD k Z₁ hZ₁ T hT t₁ hti₁
  obtain ⟨K₂, _, Q₂, hQ₂, -⟩ := hRD k Z₂ hZ₂ T hT t₂ hti₂
  have hB₁ := hB k G₁ hG₁ T hT i₁ hi₁ ν Z₁ z₁ hz₁ hrep₁ hZ₁ t₁ ht₁
  have hB₂ := hB k G₂ hG₂ T hT i₂ hi₂ ν Z₂ z₂ hz₂ hrep₂ hZ₂ t₂ ht₂
  have hroots : roots i₁ = roots i₂ := by
    rw [← hP₁.2.1, ← hP₂.2.1, ← hroot, e.surjective.range_comp]
  have hroots_t : roots t₁ = roots t₂ := by
    rw [hB₁, hB₂, hroots]
  -- The reindexing of the root data of the centralizers along their common roots.
  let e' : K₁ ≃ K₂ := (Equiv.ofInjective Q₁.root Q₁.root.injective).trans
    ((Set.equivOfEq (hQ₁.2.1.trans (hroots_t.trans hQ₂.2.1.symm))).trans
      (Equiv.ofInjective Q₂.root Q₂.root.injective).symm)
  have he'_root (j : K₁) : Q₂.root (e' j) = Q₁.root j := by
    change Q₂.root ((Equiv.ofInjective Q₂.root Q₂.root.injective).symm _) = _
    exact congrArg Subtype.val ((Equiv.ofInjective Q₂.root Q₂.root.injective).apply_symm_apply _)
  have he'_coroot (j : K₁) : Q₂.coroot (e' j) = Q₁.coroot j := by
    have hα : Q₁.root j ∈ roots i₁ := by
      have h : Q₁.root j ∈ roots t₁ := hQ₁.2.1 ▸ Set.mem_range_self j
      rw [hB₁] at h
      exact h.1
    rw [← hP₁.2.1] at hα
    obtain ⟨j₁, hj₁⟩ := hα
    have h₁ : P₁.coroot j₁ = Q₁.coroot j :=
      IsRootDatumOf.coroot_eq_of_comp_of_mono_of_finite_weylImage i₁ t₁ z₁ ht₁ hP₁ hQ₁ hj₁
    have h₂ : P₂.coroot (e j₁) = Q₂.coroot (e' j) := by
      refine IsRootDatumOf.coroot_eq_of_comp_of_mono_of_finite_weylImage i₂ t₂ z₂ ht₂ hP₂ hQ₂ ?_
      rw [he'_root, ← hj₁]
      exact congrFun hroot j₁
    rw [← h₂, ← h₁]
    exact congrFun hcoroot j₁
  -- The rank-one case applies to the centralizers.
  have hrank' : ∀ α ∈ roots t₁, ∀ β ∈ roots t₁, ¬ LinearIndependent ℤ ![α, β] := by
    intro α hα β hβ
    rw [hB₁] at hα hβ
    exact hrank α hα.1 β hβ.1 hα.2 hβ.2
  exact hA k Z₁ Z₂ hZ₁ hZ₂ T hT t₁ t₂ hti₁ hti₂ K₁ K₂ Q₁ Q₂ hQ₁ hQ₂ e'
    (funext he'_root) (funext he'_coroot) hrank'

namespace SplitCommonTorusIsomorphism

/-- The hypotheses of the reduction `splitCommonTorusIsomorphism_of_leviGluing`: existence of
root data, reductivity of centralizers of cocharacters, the Isomorphism Theorem in semisimple
rank at most one, and the Levi gluing step. -/
def Prerequisites : Prop :=
  RootDatumExistenceStatement.{u} ∧ DynamicCentralizerReductiveStatement.{u} ∧
    SplitRankOneCommonTorusIsomorphismStatement.{u} ∧ SplitCommonTorusLeviGluingStatement.{u}

/-- The Isomorphism Theorem for a common split maximal torus follows from `Prerequisites`. -/
theorem splitCommonTorusIsomorphismStatement_of_prerequisites (h : Prerequisites.{u}) :
    SplitCommonTorusIsomorphismStatement.{u} :=
  splitCommonTorusIsomorphism_of_leviGluing h.1 h.2.1 h.2.2.1 h.2.2.2

end SplitCommonTorusIsomorphism

end Langlands.GroupScheme
