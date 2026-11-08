import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct
import Langlands.GroupScheme.Rational.SteinbergPrefixWeights
import Langlands.GroupScheme.Rational.IndependentWeightProductProof
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction

/-! # The modified product `N''` is a closed immersion -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

namespace RootParametrization

variable {α : p.rootIndex} (x : p.RootParametrization α) (n : normalizerPoints p.inclusion)

/-- A supplied root map conjugated by an actual normalizing rational point. -/
def conjugateHom : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  x.hom ≫ (G.innerIso n).hom

theorem isClosedSubgroup_conjugateHom : IsClosedSubgroup (x.conjugateHom n) :=
  x.isClosedSubgroup.comp_iso (G.innerIso n)

/-- Its scalar values are the actual conjugates on every scheme test. -/
theorem scalarPoint_conjugateHom (T : Over (Spec (CommRingCat.of k)))
    (c : Γ(T.left, ⊤)) :
    VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (x.conjugateHom n).hom.hom =
      G.constantPoint n T * x.point T c * (G.constantPoint n T)⁻¹ := by
  rw [conjugateHom, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  rfl

/-- Conjugation changes the torus weight by the actual contravariant Weyl action. -/
theorem conjugateHom_torus_equivariant (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (c : Γ(T.left, ⊤)) :
    (AutomorphicAction.conjugation p.inclusion).act t
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (x.conjugateHom n).hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (weylAction p.inclusion n (p.rootDatum.root α)) T t * c) ≫
          (x.conjugateHom n).hom.hom := by
  let σ := normalizingAut p.inclusion n
  let t' : T ⟶ p.torus.X := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hn :
      (G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T =
        t' ≫ p.inclusion.hom.hom := by
    have h := (isNormalizingPoint_normalizingAut p.inclusion n).inv.conj_comp T t
    simpa [t', σ, constantPoint_inv] using h
  have hw :
      VectorGroup.charValue (weylAction p.inclusion n (p.rootDatum.root α)) T t =
        VectorGroup.charValue (p.rootDatum.root α) T t' := by
    rfl
  rw [AutomorphicAction.conjugation_act, scalarPoint_conjugateHom,
    scalarPoint_conjugateHom, hw]
  calc
    _ = G.constantPoint n T *
        (((G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T) *
          x.point T c *
          ((G.constantPoint n T)⁻¹ * (t ≫ p.inclusion.hom.hom) * G.constantPoint n T)⁻¹) *
        (G.constantPoint n T)⁻¹ := by group
    _ = _ := by
      rw [hn]
      exact congrArg (fun z => G.constantPoint n T * z * (G.constantPoint n T)⁻¹)
        (x.torus_equivariant T t' c)

end RootParametrization

/-- A supplied reflection representative as a point of the actual normalizer. -/
def ReflectionRepresentative.normalizerPoint {α : p.rootIndex}
    (n : p.ReflectionRepresentative α) : normalizerPoints p.inclusion :=
  ⟨n.point, n.torusAut, n.normalizes⟩

theorem ReflectionRepresentative.weylAction_normalizerPoint {α : p.rootIndex}
    (n : p.ReflectionRepresentative α) :
    weylAction p.inclusion n.normalizerPoint = p.rootDatum.reflection α := by
  have h := (isNormalizingPoint_normalizingAut p.inclusion n.normalizerPoint).unique
    p.inclusion n.normalizes
  change characterAut (normalizingAut p.inclusion n.normalizerPoint) = _
  rw [h]
  exact n.characterAut_eq

variable (D : p.SteinbergModifiedData) {q : ℕ} (e : Fin q ≃ D.Complement)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

/-- The roots of the factors of `N''`: the merged root followed by the complementary simple
roots in the supplied order. -/
def modifiedRoots : Fin (q + 1) → p.rootIndex :=
  Fin.cons D.alpha fun j => ((e j).1 : p.rootIndex)

/-- The root maps of the factors of `N''`. -/
def modifiedRootMaps : (j : Fin (q + 1)) → p.RootParametrization (modifiedRoots D e j) :=
  Fin.cons D.xAlpha fun j => (x (e j).1).toRootParametrization

/-- The representatives of the factors of `N''`, as normalizer points. -/
def modifiedNormalizers : Fin (q + 1) → normalizerPoints p.inclusion :=
  Fin.cons D.nAlpha.normalizerPoint fun j => (n (e j).1).normalizerPoint

theorem weylAction_modifiedNormalizers (j : Fin (q + 1)) :
    weylAction p.inclusion (modifiedNormalizers D e n j) =
      p.rootDatum.reflection (modifiedRoots D e j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact D.nAlpha.weylAction_normalizerPoint
  · exact (n (e j).1).weylAction_normalizerPoint

/-- The factor maps of `N''` after moving the preceding representatives to the right. -/
def modifiedPrefixRootHom (j : Fin (q + 1)) : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G :=
  (modifiedRootMaps D e x j).conjugateHom
    (orderedPrefix (q + 1) (modifiedNormalizers D e n) j.castSucc)

/-- The integral characters of the prefix-conjugated factor maps. -/
def modifiedPrefixWeight (j : Fin (q + 1)) : characterLattice p.torus :=
  weylAction p.inclusion (orderedPrefix (q + 1) (modifiedNormalizers D e n) j.castSucc)
    (p.rootDatum.root (modifiedRoots D e j))

theorem modifiedPrefixWeight_eq (j : Fin (q + 1)) :
    modifiedPrefixWeight D e n j =
      orderedPrefix (q + 1) (fun i => p.rootDatum.reflection (modifiedRoots D e i)) j.castSucc
        (p.rootDatum.root (modifiedRoots D e j)) := by
  simp only [modifiedPrefixWeight, map_orderedPrefix, weylAction_modifiedNormalizers]

/-- The merged root and the complementary simple roots are linearly independent. -/
theorem modifiedRoots_linearIndependent :
    LinearIndependent ℤ (fun j => p.rootDatum.root (modifiedRoots D e j)) := by
  have hv := p.base.linearIndepOn_root.linearIndependent
  have hC : LinearIndependent ℤ (fun j : Fin q => p.rootDatum.root ((e j).1 : p.rootIndex)) :=
    hv.comp (fun j => (e j).1) (fun i j h => e.injective (Subtype.ext h))
  have hfun : (fun j => p.rootDatum.root (modifiedRoots D e j)) =
      Fin.cons (p.rootDatum.root (D.a : p.rootIndex) + p.rootDatum.root (D.b : p.rootIndex))
        (fun j : Fin q => p.rootDatum.root ((e j).1 : p.rootIndex)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [modifiedRoots, Fin.cons_zero, D.root_eq]
    · simp only [modifiedRoots, Fin.cons_succ]
  rw [hfun]
  refine LinearIndependent.finCons' (R := ℤ) (M := characterLattice p.torus)
    (p.rootDatum.root (D.a : p.rootIndex) + p.rootDatum.root (D.b : p.rootIndex))
    (fun j : Fin q => p.rootDatum.root ((e j).1 : p.rootIndex)) hC fun c y hy h => ?_
  have hsub : Submodule.span ℤ (Set.range fun j : Fin q =>
      p.rootDatum.root ((e j).1 : p.rootIndex)) ≤
      Submodule.span ℤ ((fun z : p.base.support => p.rootDatum.root (z : p.rootIndex)) ''
        (Set.univ \ {D.a})) := by
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(e j).1, ⟨Set.mem_univ _, (e j).2.1⟩, rfl⟩
  have hb : p.rootDatum.root (D.b : p.rootIndex) ∈
      Submodule.span ℤ ((fun z : p.base.support => p.rootDatum.root (z : p.rootIndex)) ''
        (Set.univ \ {D.a})) :=
    Submodule.subset_span ⟨D.b, ⟨Set.mem_univ _, Ne.symm D.a_ne_b⟩, rfl⟩
  have ha : c • p.rootDatum.root (D.a : p.rootIndex) =
      -(c • p.rootDatum.root (D.b : p.rootIndex) + y) := by
    rw [eq_neg_iff_add_eq_zero, ← add_assoc, ← smul_add]
    exact h
  refine hv.eq_zero_of_smul_mem_span D.a c ?_
  change c • p.rootDatum.root (D.a : p.rootIndex) ∈ _
  rw [ha]
  exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hb) (hsub hy))

theorem modifiedPrefixWeight_linearIndependent :
    LinearIndependent ℤ (modifiedPrefixWeight D e n) := by
  change LinearIndependent ℤ (fun j => modifiedPrefixWeight D e n j)
  simp_rw [modifiedPrefixWeight_eq]
  exact Langlands.LinearAlgebra.orderedReflectionWeights_linearIndependent (q + 1)
    (fun j => p.rootDatum.root (modifiedRoots D e j)) (modifiedRoots_linearIndependent D e)
    (fun j => p.rootDatum.coroot' (modifiedRoots D e j))
    (fun j => p.rootDatum.reflection (modifiedRoots D e j))
    (fun j z => p.rootDatum.reflection_apply (modifiedRoots D e j) z)
    (fun j => p.rootDatum.reflection_apply_self (modifiedRoots D e j))

theorem isClosedSubgroup_modifiedPrefixRootHom (j : Fin (q + 1)) :
    IsClosedSubgroup (modifiedPrefixRootHom D e x n j) :=
  (modifiedRootMaps D e x j).isClosedSubgroup_conjugateHom _

theorem modifiedPrefixRootHom_torus_equivariant (j : Fin (q + 1))
    (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ p.torus.X) (c : Γ(T.left, ⊤)) :
    (AutomorphicAction.conjugation p.inclusion).act t
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫
          (modifiedPrefixRootHom D e x n j).hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (modifiedPrefixWeight D e n j) T t * c) ≫
          (modifiedPrefixRootHom D e x n j).hom.hom :=
  (modifiedRootMaps D e x j).conjugateHom_torus_equivariant _ T t c

/-- The ordered product of all representatives of `N''`. -/
def modifiedCoxeterNormalizer : normalizerPoints p.inclusion :=
  (List.ofFn (modifiedNormalizers D e n)).prod

/-- On every test, moving the representatives of `N''` to the right gives the prefix-conjugated
factors. -/
theorem steinbergModifiedProductPoint_eq_independentWeightProduct
    (T : Over (Spec (CommRingCat.of k))) (s : Γ(T.left, ⊤)) (d : Fin q → Γ(T.left, ⊤)) :
    steinbergModifiedProductPoint D e x n T s d =
      IndependentWeightProduct.point (modifiedPrefixRootHom D e x n) T (Fin.cons s d) *
        G.constantPoint (modifiedCoxeterNormalizer D e n) T := by
  let f : normalizerPoints p.inclusion →* (T ⟶ G.X) :=
    (G.constantPointHom T).comp (normalizerPoints p.inclusion).subtype
  have hpoint : ∀ j : Fin (q + 1),
      (modifiedRootMaps D e x j).point T ((Fin.cons s d : Fin (q + 1) → Γ(T.left, ⊤)) j) *
        f (modifiedNormalizers D e n j) =
      (Fin.cons (D.xAlpha.point T s * (toUnit T ≫ D.nAlpha.point))
        (fun i : Fin q => (x (e i).1).point T (d i) * (toUnit T ≫ (n (e i).1).point)) :
          Fin (q + 1) → (T ⟶ G.X)) j := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · rfl
  have hprod : steinbergModifiedProductPoint D e x n T s d =
      (List.ofFn fun j : Fin (q + 1) =>
        (modifiedRootMaps D e x j).point T ((Fin.cons s d : Fin (q + 1) → Γ(T.left, ⊤)) j) *
          f (modifiedNormalizers D e n j)).prod := by
    simp only [hpoint]
    rw [List.ofFn_succ, List.prod_cons, steinbergModifiedProductPoint,
      simpleRootProductPoint]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hp (j : Fin (q + 1)) :
      G.constantPoint ((orderedPrefix (q + 1) (modifiedNormalizers D e n) j.castSucc :
        normalizerPoints p.inclusion) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) T =
        orderedPrefix (q + 1) (fun i => f (modifiedNormalizers D e n i)) j.castSucc := by
    change f (orderedPrefix (q + 1) (modifiedNormalizers D e n) j.castSucc) = _
    rw [map_orderedPrefix]
  have hn : G.constantPoint (modifiedCoxeterNormalizer D e n) T =
      (List.ofFn fun j => f (modifiedNormalizers D e n j)).prod := by
    change f (List.ofFn (modifiedNormalizers D e n)).prod = _
    rw [map_list_prod, List.map_ofFn]
    rfl
  rw [hprod, interleaved_prod_eq_prefix_conjugates, hn, IndependentWeightProduct.point]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [modifiedPrefixRootHom, RootParametrization.scalarPoint_conjugateHom, hp]

/-- The modified morphism `N''` is the prefix-root product followed by right translation. -/
theorem steinbergModifiedProduct_eq_independentWeightProduct :
    steinbergModifiedProduct D e x n =
      IndependentWeightProduct.morphism (modifiedPrefixRootHom D e x n) ≫
        G.rightTranslation (modifiedCoxeterNormalizer D e n) := by
  rw [comp_rightTranslation, steinbergModifiedProduct,
    steinbergModifiedProductPoint_eq_independentWeightProduct, IndependentWeightProduct.morphism]
  congr 2
  exact Fin.cons_self_tail _

/-- **Steinberg 9.13 for `N''`.** The modified product is a closed immersion of schemes. -/
theorem isClosedImmersion_steinbergModifiedProduct :
    IsClosedImmersion (steinbergModifiedProduct D e x n).left := by
  have hc : IsClosedImmersion
      (IndependentWeightProduct.morphism (modifiedPrefixRootHom D e x n)).left :=
    independentWeightProductImmersion k G p.torus p.isSplitTorus
      (AutomorphicAction.conjugation p.inclusion) (q + 1) (modifiedPrefixRootHom D e x n)
      (modifiedPrefixWeight D e n) (modifiedPrefixWeight_linearIndependent D e n)
      (isClosedSubgroup_modifiedPrefixRootHom D e x n)
      (modifiedPrefixRootHom_torus_equivariant D e x n)
  have : IsIso (G.rightTranslation (modifiedCoxeterNormalizer D e n)).left :=
    inferInstanceAs (IsIso ((Over.forget _).map
      (G.rightTranslationIso (modifiedCoxeterNormalizer D e n)).hom))
  rw [steinbergModifiedProduct_eq_independentWeightProduct, Over.comp_left]
  infer_instance

end Langlands.GroupScheme.SplitPinning
