/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# The one-term Tor-acyclic tensor comparison

Source: Stacks Project, Tag 08IB, final affine calculation; More on Algebra,
Section 15.60 (Tag 06XY), independence of K-flat resolutions.
(blueprint: lem-pc-single-support-tor-acyclic-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

private theorem tensor_map_of_kFlat
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    {K L : CochainComplex (ModuleCat R) ℤ} (a : K ⟶ L) (ha : QuasiIso a)
    (hK : (quasiIso (ModuleCat R) (.up ℤ)).kFlat K)
    (hL : (quasiIso (ModuleCat R) (.up ℤ)).kFlat L) :
    QuasiIso ((((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex
      (.up ℤ)).map a) := by
  let e := map₂HomologicalComplexFlipObjSingleIso (curriedTensor (ModuleCat R)) N
  have ht := (quasiIso (ModuleCat R) (.up ℤ)).whiskerRight_of_kFlat
    a ha hK hL ((singleFunctor (ModuleCat R) 0).obj N)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality a).symm)).1 ht

private theorem tensor_projective_augmentation
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)
    (S : ProjectiveResolution M)
    (hTor : ∀ i : ℕ, 0 < i → IsZero (((Tor' (ModuleCat R) i).obj M).obj N)) :
    QuasiIso ((((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex
      (.down ℕ)).map S.π) := by
  let F := (tensoringRight (ModuleCat R)).obj N
  constructor
  intro i
  cases i with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · change (ShortComplex.mk (F.map (S.complex.d 1 0)) (F.map (S.π.f 0)) _).Exact ∧
        Epi (F.map (S.π.f 0))
      constructor
      · exact ShortComplex.exact_of_g_is_cokernel _
          (CokernelCofork.mapIsColimit _ S.isColimitCokernelCofork F)
      · exact Cofork.IsColimit.epi
          (CokernelCofork.mapIsColimit _ S.isColimitCokernelCofork F)
    · simp
    · simp
    · simp
  | succ i =>
    apply (quasiIsoAt_iff_exactAt' _ _ ?_).2
    · rw [exactAt_iff_isZero_homology]
      exact (hTor (i + 1) (by omega)).of_iso (S.isoLeftDerivedObj F (i + 1)).symm
    · exact ExactAt.of_isZero
        (F.map_isZero (isZero_single_obj_X _ _ _ _ (by omega)))

private theorem exists_tensor_good_single_resolution
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) (k : ℤ)
    (hTor : ∀ i : ℕ, 0 < i → IsZero (((Tor' (ModuleCat R) i).obj M).obj N)) :
    ∃ (S : KFlat (ModuleCat R)) (g : S.obj ⟶ (singleFunctor (ModuleCat R) k).obj M),
      QuasiIso g ∧ QuasiIso ((((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex
        (.up ℤ)).map g) := by
  let T := projectiveResolution M
  let e := ComplexShape.embeddingUpIntLE k
  let F := (tensoringRight (ModuleCat R)).obj N
  let S : CochainComplex (ModuleCat R) ℤ := T.complex.extend e
  have hbounded : S.IsStrictlyLE k := by
    rw [isStrictlyLE_iff]
    intro n hn
    exact T.complex.isZero_extend_X e n (by intro i; change k - (i : ℤ) ≠ n; omega)
  have hflat (n : ℤ) : ObjectProperty.flat (S.X n) := by
    apply (ModuleCat.flat_iff_flat _).2
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have (X : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat R)).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight X))
  have hS := kFlat_of_isStrictlyLE_of_flat S k hflat
  let g := extendMap T.π e ≫ (extendSingleIso e M 0 k (by simp [e])).hom
  have hg : QuasiIso g := by dsimp [g]; infer_instance
  refine ⟨⟨S, hS⟩, g, hg, ?_⟩
  have ht : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map T.π) :=
    tensor_projective_augmentation M N T hTor
  have ht' : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (extendMap T.π e)) := by
    let E := e.mapExtendFunctorNatIso F
    apply (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (E.app T.complex) (E.app _) (E.hom.naturality T.π).symm)).2
    exact (quasiIso_extendMap_iff _ e).2 ht
  dsimp only [g]
  rw [Functor.map_comp]
  have hi : IsIso (((F.mapHomologicalComplex (.up ℤ)).map
      (extendSingleIso e M 0 k (by simp [e])).hom)) := by infer_instance
  exact quasiIso_comp _ _ (hφ := ht') (hφ' := quasiIso_of_isIso _)

private theorem tensor_comparison_independent_of_resolution
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (Q : CochainComplex (ModuleCat R) ℤ)
    (S P : KFlat (ModuleCat R)) (g : S.obj ⟶ Q) (f : P.obj ⟶ Q)
    (hg : QuasiIso g) (hf : QuasiIso f)
    (htg : QuasiIso ((((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex
      (.up ℤ)).map g)) :
    QuasiIso ((((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex
      (.up ℤ)).map f) := by
  have := htg
  let Λ := (Classical.arbitrary
    (Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ ModuleCat.{u} R))).reduced
  let T := Λ.resolutionFunctor
  let ρ := Λ.resolutionNatTrans
  let F := ((tensoringRight (ModuleCat R)).obj N).mapHomologicalComplex (.up ℤ)
  have hT (X : CochainComplex (ModuleCat R) ℤ) :
      (quasiIso (ModuleCat R) (.up ℤ)).kFlat (T.obj X) :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le X
  have hρ (X : CochainComplex (ModuleCat R) ℤ) : QuasiIso (ρ.app X) := by
    dsimp [ρ]
    infer_instance
  have hmap {X Y : CochainComplex (ModuleCat R) ℤ} (a : X ⟶ Y) (ha : QuasiIso a) :
      QuasiIso (T.map a) := by
    have := ha
    have := hρ X
    have := hρ Y
    have hcomp : QuasiIso (T.map a ≫ ρ.app Y) := by
      rw [ρ.naturality a]
      dsimp only [Functor.id_map]
      infer_instance
    exact quasiIso_of_comp_right (T.map a) (ρ.app Y)
  have hρS : QuasiIso (F.map (ρ.app S.obj)) :=
    tensor_map_of_kFlat N _ (hρ _) (hT _) S.property
  have hTg : QuasiIso (F.map (T.map g)) :=
    tensor_map_of_kFlat N _ (hmap g hg) (hT _) (hT _)
  have hρQ : QuasiIso (F.map (ρ.app Q)) := by
    have hcomp : QuasiIso (F.map (T.map g) ≫ F.map (ρ.app Q)) := by
      rw [← F.map_comp, ρ.naturality g, Functor.id_map, F.map_comp]
      infer_instance
    exact quasiIso_of_comp_left (F.map (T.map g)) (F.map (ρ.app Q))
  have hTf : QuasiIso (F.map (T.map f)) :=
    tensor_map_of_kFlat N _ (hmap f hf) (hT _) (hT _)
  have hρP : QuasiIso (F.map (ρ.app P.obj)) :=
    tensor_map_of_kFlat N _ (hρ _) (hT _) P.property
  have hcomp : QuasiIso (F.map (ρ.app P.obj) ≫ F.map f) := by
    rw [← F.map_comp, ← show T.map f ≫ ρ.app Q = ρ.app P.obj ≫ f from
      by simpa only [Functor.id_map] using ρ.naturality f, F.map_comp]
    infer_instance
  exact quasiIso_of_comp_left (F.map (ρ.app P.obj)) (F.map f)

/-- For a complex supported in one degree, positive Tor vanishing suffices for
any K-flat resolution to compute its ordinary tensor product.

Source: Stacks Project, Tag 08IB, final affine Tor calculation, and Tag 06XY,
Lemmas 15.60.7 and 15.60.12. The following fills in the one-term calculation
of the parent node; it is not an assertion of the entire bounded-complex result.
(blueprint: lem-pc-single-support-tor-acyclic-tensor).

Proof:
1. The support hypothesis identifies Q with the single complex on Q.X k in
   degree k, using the identity in degree k and the unique maps between zero
   objects in the other degrees. All its differentials are zero.
2. Take a projective resolution of Q.X k, reindex it in cochain degrees k-i,
   and augment it to Q. Its terms are flat and it is bounded above, hence K-flat
   by the bounded-flat K-flat lemma. After tensoring with B its cohomology in
   degree k-i is Tor_i(Q.X k,B). Its degree-k augmentation is an isomorphism by
   right exactness of tensor and the Tor-zero comparison. In degrees above k
   both complexes are zero. Thus its tensor augmentation is a quasi-isomorphism.
3. This calculation applies to the given f, not just the projective resolution:
   choose a common K-flat refinement of the two resolutions in the homotopy
   category. The transition quasi-isomorphisms remain quasi-isomorphisms after
   tensoring with B (Tag 06XY, Lemma 15.60.12); their augmentation square commutes
   up to homotopy. Tensor preserves that homotopy, so two-out-of-three gives the
   result for f. This also covers Q=0 and an unbounded K-flat source P. -/
theorem quasiIso_tensor_of_single_support_tor_acyclic
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    (hsupport : ∀ n : ℤ, n ≠ k → IsZero (Q.X n))
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (Q.X k)).obj (ModuleCat.of R B)))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  have : Q.IsStrictlyGE k := (Q.isStrictlyGE_iff k).2
    (fun n hn ↦ hsupport n (by omega))
  have : Q.IsStrictlyLE k := (Q.isStrictlyLE_iff k).2
    (fun n hn ↦ hsupport n (by omega))
  let e := Q.isoSingle k
  obtain ⟨S, g, hg, htg⟩ :=
    exists_tensor_good_single_resolution (Q.X k) (ModuleCat.of R B) k hTor
  let F := ((tensoringRight (ModuleCat R)).obj (ModuleCat.of R B)).mapHomologicalComplex
    (.up ℤ)
  have hg' : QuasiIso (g ≫ e.inv) := by infer_instance
  have htg' : QuasiIso (F.map (g ≫ e.inv)) := by
    rw [F.map_comp]
    infer_instance
  exact tensor_comparison_independent_of_resolution (ModuleCat.of R B) Q S P
    (g ≫ e.inv) f hg' hf htg'

end CochainComplex
