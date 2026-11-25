/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
import WeilConjectures.CategoryTheory.SixFunctors.ConstructibleHomContinuityDevissage
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ConstructibleExtContinuityStratum
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Continuity of Ext from constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/
sk-lem-constructible-ext-continuity/_section.md, statement and proof
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

All derived categories below are ordinary derived categories of internal module objects.
The comparison is induced by a colimit cocone of complexes, hence by the termwise
colimit cocone. Field coefficients use the finite constant-model constructibility
recorded by definition-constructible-sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] localPieceCostalkModelHasZeroMorphisms

local instance extContinuityHasColimit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

/-- The additive functor `K ↦ Hom(C, Q(K)[q])`.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, displayed Hom groups
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def extContinuityTestFunctor
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : DerivedCategory A) (q : ℤ) : CochainComplex A ℤ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory A) q ⋙ preadditiveCoyoneda.obj (op C)

/-- The canonical comparison induced by the arrows of the given colimit cocone.
On the i-th Hom group it sends f to f followed by Q(c.ι_i)[q].
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, displayed natural map
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def extContinuityComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type w} [SmallCategory I]
    (C : DerivedCategory A) (K : I ⥤ CochainComplex A ℤ) (c : Cocone K) (q : ℤ) :
    colimit (K ⋙ extContinuityTestFunctor C q) ⟶
      (extContinuityTestFunctor C q).obj c.pt :=
  colimit.desc _ ((extContinuityTestFunctor C q).mapCocone c)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The sheaves a_!L, expressed by an open immersion into a closed subscheme and
finite locally free pro-etale coefficient modules. All such factorizations are allowed.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, generator paragraph
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def IsExtContinuityStratum (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
    (_ : IsOpenImmersion j) (_ : IsClosedImmersion i)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
    IsLisseCoefficientModule Λ L ∧
      Nonempty (M ≅ (CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj L))

/-- Generators with allowed integer shifts N. Taking N = univ allows every shift;
N = {0} describes the unshifted generators used in the integral sheaf clause.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, finite extension hypothesis
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def extContinuityShiftedStrata (X : Scheme.{u}) (N : Set ℤ) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  fun C ↦ ∃ M, IsExtContinuityStratum Λ X M ∧ ∃ n ∈ N,
    Nonempty (C ≅ ((DerivedCategory.singleFunctor _ 0).obj M)⟦n⟧)

/-- Finite iterated extensions of the indicated generators, up to isomorphism.
Mathlib's extensionProductIter counts n extensions from n+1 factors. Zero is included
because the zero module is locally free of rank zero and is a stratum generator.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, finite extension hypothesis
(blueprint: lemma-continuity-ext-out-constructible-complex--1). -/
def IsExtContinuityGenerated (X : Scheme.{u}) (N : Set ℤ)
    (C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  ∃ n : ℕ, (extContinuityShiftedStrata Λ X N).extensionProductIter n C

private theorem continuity_of_locus
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type w} [SmallCategory I]
    (C : DerivedCategory A) (K : I ⥤ CochainComplex A ℤ) [HasColimit K]
    (c : Cocone K) (hc : IsColimit c)
    (hC : complexHomContinuityLocus A K C) (q : ℤ) :
    IsIso (extContinuityComparison C K c q) := by
  have hp : IsIso (colimit.post K (extContinuityTestFunctor C q)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hC q)
  have hd : IsIso (colimit.desc K c) := by
    change IsIso ((colimit.isColimit K).coconePointUniqueUpToIso hc).hom
    infer_instance
  unfold extContinuityComparison
  rw [← colimit.post_desc]
  infer_instance

private theorem continuity_admissible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ ∨ R = Profinite.padicIntegersCondensedRing ℓ E) :
    CondensedRing.IsAdmissibleCoefficient (coefficientHeartRingObj R) := by
  refine ⟨ℓ, inferInstance, ?_⟩
  rcases hR with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))

private theorem continuity_stratum_locus
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (_hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ ∨ R = Profinite.padicIntegersCondensedRing ℓ E)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) ℤ)
    (b : ℤ) (hb : ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hM : IsExtContinuityStratum (coefficientHeartRingObj R) X M) :
    complexHomContinuityLocus _ K ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨S, Z, j, i, hj, hi, L, hL, ⟨e⟩⟩ := hM
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace S := j.isOpenEmbedding.isInducing.noetherianSpace
  have hgen : complexHomContinuityLocus _ K
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (coefficientHeartRingObj R) i).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj R) j).obj L))) := by
    intro q
    obtain ⟨N, hN, d, v, hleg⟩ := condensed_local_piece_costalk_model X
      (coefficientHeartRingObj R) i j L K ⟨b, hb⟩ q
    let F := shiftFunctor _ q ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (coefficientHeartRingObj R) i).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj R) j).obj L))))
    let G := condensedShiftedHom (coefficientHeartRingObj R) S
      ((DerivedCategory.singleFunctor _ 0).obj L) q
    have : IsIso (colimit.desc (N ⋙ G) (G.mapCocone (colimit.cocone N))) :=
      condensed_finite_free_hom_continuity S (coefficientHeartRingObj R) L
        (lisseRawCover (coefficientHeartRingObj R) L hL) N hN q
    have heq : colimit.post K (DerivedCategory.Q ⋙ F) ≫ v.hom =
        colimMap d.hom ≫ colimit.desc (N ⋙ G) (G.mapCocone (colimit.cocone N)) := by
      apply colimit.hom_ext
      intro t
      dsimp only [G]
      simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_desc]
      exact hleg t
    have : IsIso (colimit.post K (DerivedCategory.Q ⋙ F) ≫ v.hom) := by
      rw [heq]
      infer_instance
    have hstr : IsIso (colimit.post K (DerivedCategory.Q ⋙ F)) :=
      IsIso.of_isIso_comp_right _ v.hom
    change Function.Bijective (colimit.post K
      (extContinuityTestFunctor ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (coefficientHeartRingObj R) i).obj
          ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj R) j).obj L))) q))
    exact (ConcreteCategory.isIso_iff_bijective _).mp hstr
  exact (constructibleHomContinuity_devissage (coefficientHeartRingObj R) X K).2.1
    _ _ ((DerivedCategory.singleFunctor _ 0).mapIso e).symm hgen

/-- Continuity for finite extensions and shifts of locally closed lisse generators.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, displayed comparison
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

Proof:
1. For the fixed diagram, consider objects whose comparisons are isomorphisms in
all degrees. Hom out of a distinguished triangle gives the five-term exact segment
in the node, also after rotating the triangle. Filtered colimits of abelian groups
are exact. The five lemma therefore gives extension closure. Shift identities replace
q by q-n, and precomposition gives invariance under isomorphisms. Zero also belongs.
Rotating a cone triangle gives closure under cones.
2. Noetherianity makes X qcqs and every open quasi-compact. A locally closed
immersion is quasi-compact and factors as an open immersion j followed by a closed
i. Their complementary opens are quasi-compact as well. The stratum continuity
lemma lemma-continuity-ext-out-constructible-complex--1 applies to the finite locally
free L, each of the three coefficient rings, and the common lower bound b. Its
comparison is the map below, since its arrows are the same cocone arrows.
3. Induct on the finite extension expression, applying step 2 to the factors and
step 1 to every shift, isomorphism and extension. -/
theorem constructible_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ ∨ R = Profinite.padicIntegersCondensedRing ℓ E)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)))
    (hC : IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) ℤ)
    (b : ℤ) (hb : ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r))
    (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    IsIso (extContinuityComparison C K c q) := by
  let G : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X))) :=
    fun D ↦ ∃ M, IsExtContinuityStratum (coefficientHeartRingObj R) X M ∧
      D = (DerivedCategory.singleFunctor _ 0).obj M
  have hG : G ≤ complexHomContinuityLocus _ K := by
    rintro D ⟨M, hM, rfl⟩
    exact continuity_stratum_locus ℓ E R hR X K b hb M hM
  have hshift : extContinuityShiftedStrata (coefficientHeartRingObj R) X Set.univ ≤
      G.shiftClosure ℤ := by
    rintro D ⟨M, hM, k, _, ⟨e⟩⟩
    exact ⟨_, k, e, M, hM, rfl⟩
  obtain ⟨n, hn⟩ := hC
  have hD := (constructibleHomContinuity_devissage (coefficientHeartRingObj R) X K).2.2.2
    G hG n C (ObjectProperty.monotone_extensionProductIter hshift n C hn)
  exact continuity_of_locus C K c hc hD q

/-- Every bounded constructible complex with field coefficients has the generator
hypothesis of continuity. Constructibility here means finite constant scalar models.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, clause 1
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

Proof: corollary-coefficient-heart-b--2 expresses every such C by finitely many
cones of shifted a_!L with L lisse, under precisely the Noetherian hypothesis here.
Rotate each cone triangle A → B → Cone → A[1] to B → Cone → A[1] → B[1]. This rewrites
the finite cone expression using extensions, shifts and isomorphisms as required. -/
theorem bounded_constructible_ext_generated
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)))
    (hC : constantModelBoundedConstructible (coefficientHeartRingObj R) X C) :
    IsExtContinuityGenerated (coefficientHeartRingObj R) X Set.univ C := by
  have : IsNoetherian X := ⟨⟩
  have hR' : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ R = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      R = Profinite.padicAlgClCondensedRing ℓ := by
    rcases hR with hR | hR
    · exact Or.inl ⟨E.1, E.2, hR⟩
    · exact Or.inr hR
  let H : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X))) :=
    fun D ↦ ∃ M, IsExtContinuityStratum (coefficientHeartRingObj R) X M ∧
      D = (DerivedCategory.singleFunctor _ 0).obj M
  have hG : extContinuityShiftedStrata (coefficientHeartRingObj R) X Set.univ =
      H.shiftClosure ℤ := by
    ext D
    constructor
    · rintro ⟨M, hM, k, _, ⟨e⟩⟩
      exact ⟨_, k, e, M, hM, rfl⟩
    · rintro ⟨_, k, e, M, hM, rfl⟩
      exact ⟨M, hM, k, Set.mem_univ k, ⟨e⟩⟩
  let G := H.shiftClosure ℤ
  let P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj R) X))) :=
    fun D ↦ ∃ n : ℕ, G.extensionProductIter n D
  have hGn (n : ℕ) : (G.extensionProductIter n).IsClosedUnderIsomorphisms := by
    cases n with
    | zero => change G.IsClosedUnderIsomorphisms; infer_instance
    | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
  have : P.IsClosedUnderIsomorphisms := ⟨by
    rintro D D' e ⟨n, hn⟩
    have := hGn n
    exact ⟨n, (G.extensionProductIter n).prop_of_iso e hn⟩⟩
  have : P.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun k ↦ ⟨by
        rintro D ⟨n, hn⟩
        exact ⟨n, (G.extensionProductIter n).le_shift k D hn⟩⟩ }
  have : P.IsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + 1 + m, ?_⟩
    rw [ObjectProperty.extensionProductIter_add G rfl]
    exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, hn, hm⟩)
  obtain ⟨N, F, hlast, hF⟩ := (coefficientHeart_generation ℓ R hR' X C).mp hC
  have hPF (r : Fin (N + 1)) : P (F r) := by
    induction r using WellFoundedLT.induction with
    | ind r ih =>
      rcases hF r with ⟨S, a, ha, L, n, hL, ⟨e⟩⟩ | ⟨i, j, hi, hj, n, f, g, h, ht⟩
      · have : IsImmersion a := ha
        have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
        refine ⟨0, ?_⟩
        change H.shiftClosure ℤ (F r)
        refine ⟨_, n, e, _, ?_, rfl⟩
        exact ⟨S, a.image, a.toImage, a.imageι, inferInstance, inferInstance,
          L, hL, ⟨Iso.refl _⟩⟩
      · have ht' : P ((F r)⟦n⟧) :=
          P.ext_of_isTriangulatedClosed₂ _
            (Pretriangulated.rot_of_distTriang _ ht) (ih j hj)
            (P.le_shift (1 : ℤ) _ (ih i hi))
        exact (P.prop_shift_iff_of_isStableUnderShift (F r) n).mp ht'
  change ∃ n, (extContinuityShiftedStrata (coefficientHeartRingObj R) X Set.univ
    ).extensionProductIter n C
  rw [hG, ← hlast]
  exact hPF (Fin.last N)

private theorem constant_model_of_iso
    {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hlocal {Y : Scheme.{u}}
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : A ≅ B) (hA : HasFiniteConstantLocalModel Λ Y A) :
      HasFiniteConstantLocalModel Λ Y B := by
    obtain ⟨𝒰, h𝒰⟩ := hA
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstr {Y : Scheme.{u}}
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ Y A) :
      IsFiniteConstantStratified Λ Y B := by
    obtain ⟨S, hS⟩ := hA
    exact ⟨S, fun a ↦ hlocal ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)
      (hS a)⟩
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split at hM
  · rename_i h
    rw [ite_eq_left h]
    exact hstr e hM
  · rename_i h
    rw [ite_eq_right h]
    exact fun U hU ↦ hstr ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem constant_model_of_isZero
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  have hlocal (Y : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (hN : IsZero N) : HasFiniteConstantLocalModel Λ Y N := by
    refine ⟨.singleton (𝟙 Y) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
    · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
    · have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
        pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
      have : PreservesFiniteColimits (upperStarFromPoint Y) := by
        unfold upperStarFromPoint
        infer_instance
      exact ((CondensedRing.upperStar Λ _).map_isZero hN).iso
        (((upperStarFromPoint Y).mapMod Λ).map_isZero (isZero_zero _))
  have hstr (Y : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (hN : IsZero N) : IsFiniteConstantStratified Λ Y N := by
    let S : Scheme.Stratification Y :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
        iUnion_stratum_eq_univ := Set.iUnion_const _
        pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
        domain := fun _ ↦ Y
        immersion := fun _ ↦ 𝟙 Y
        range_immersion := fun _ ↦ Set.range_id' }
    exact ⟨S, fun a ↦ hlocal _ _
      ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hN)⟩
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstr X M hM
  · exact fun U _ ↦ hstr _ _ ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

/-- In particular all integer Ext functors from a constructible field-coefficient
sheaf commute with filtered colimits of module objects.
Source: blueprint lemma-continuity-ext-out-constructible-complex--1, clause 1, in particular
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

Proof: a constructible sheaf in degree zero is bounded constructible. Apply
bounded_constructible_ext_generated, then constructible_ext_continuity to its
degree-zero diagram. This diagram has common lower bound zero, and its termwise
colimit is the degree-zero embedding of the module colimit. The induced cocone is
therefore exactly the Ext comparison of the source. -/
theorem constructible_sheaf_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (c : Cocone M) (hc : IsColimit c) (q : ℤ) :
    IsIso (colimit.desc _
      (((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor _ 0).obj C))).mapCocone c))) := by
  let C' := (DerivedCategory.singleFunctor _ 0).obj C
  have hC' : constantModelBoundedConstructible (coefficientHeartRingObj R) X C' := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst n
      exact constant_model_of_iso _
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app C).symm hC
    · apply constant_model_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  let K := M ⋙ CochainComplex.singleFunctor _ 0
  have hK : ∀ (i : I) (r : ℤ), r < 0 → IsZero ((K.obj i).X r) := by
    intro i r hr
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (M.obj i) r (ne_of_lt hr)
  have : PreservesColimit M (CochainComplex.singleFunctor _ 0) := by
    change PreservesColimit M (HomologicalComplex.single _ (.up ℤ) 0)
    infer_instance
  have hmain := constructible_ext_continuity ℓ E R (hR.imp_right Or.inl) X C'
    (bounded_constructible_ext_generated ℓ E R hR X C' hC') K 0 hK
    ((CochainComplex.singleFunctor _ 0).mapCocone c)
    (isColimitOfPreserves (CochainComplex.singleFunctor _ 0) hc) q
  exact hmain

end AlgebraicGeometry.ProEtale
