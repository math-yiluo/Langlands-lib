/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.SixFunctors.OpenClosed.Vanishing
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Complex

/-!
# The open–closed dévissage of constructible sheaves

Let `(j : U ⟶ X, i : Z ⟶ X)` be a complementary pair: an open immersion and a closed
immersion with complementary ranges. A sheaf `F` on the small étale site of `X` is
constructible if and only if `j^* F` and `i^* F` are
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_upperStar`): one direction is the
pullback stability of `WeilConjectures.ConstructibleSheaf.Pullback`, the other concatenates
stratifications of `U` and `Z` to a stratification of `X`
(`AlgebraicGeometry.Scheme.Stratification.openClosed`). Consequently the pushforward `i_* G`
of a constructible sheaf on `Z` and the extension by zero `j_! G` of a constructible sheaf on
`U` are constructible (`IsConstructibleSheaf.lowerStar_of_isClosedImmersion`,
`IsConstructibleSheaf.openImmersionLowerShriek`): their pullbacks to the other member of the
pair vanish, and a zero sheaf is constructible (`IsConstructibleSheaf.of_isZero`).
(blueprint: `prop:constructible-open-closed`, `lemma:constructible-lowerStar-closed`,
`lemma:constructible-lowerShriek-open`)

When the complement of an open immersion `j` is a finite set of closed points, the range of
`j` and these points form a stratification of `X`
(`AlgebraicGeometry.Scheme.Stratification.ofOpenImmersion`).

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section Zero

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
/-- A zero sheaf is constant. -/
lemma _root_.CategoryTheory.Sheaf.IsConstant.of_isZero {F : Sheaf X.smallEtaleTopology A}
    (hF : IsZero F) : F.IsConstant X.smallEtaleTopology :=
  Sheaf.isConstant_of_iso _
    (hF.iso ((constantSheaf X.smallEtaleTopology A).map_isZero (isZero_zero A)))

/-- A zero sheaf is locally constant, trivialised by the identity cover. -/
lemma IsLocallyConstantSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsLocallyConstantSheaf F := by
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  refine ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  exact Sheaf.IsConstant.of_isZero ((Etale.upperStar A _).map_isZero hF)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

omit [HasSmallSiteSheafify A] in
/-- A zero sheaf is finite: its stalks are zero objects, which are finitely generated. -/
lemma IsFiniteSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsFiniteSheaf F where
  isFinitelyGenerated_sheafFiber _ _ _ s :=
    ConcreteCategory.isFinitelyGenerated_of_isZero ((pointSmallEtale s).sheafFiber.map_isZero hF)

/-- A zero sheaf is finite locally constant. -/
lemma IsFiniteLocallyConstantSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A}
    (hF : IsZero F) : IsFiniteLocallyConstantSheaf F where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_isZero hF
  toIsFiniteSheaf := IsFiniteSheaf.of_isZero hF

/-- The trivial stratification of `X`, with the single stratum `X`. -/
@[simps n stratum domain immersion]
def Stratification.trivial (X : Scheme.{u}) : Stratification X where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  iUnion_stratum_eq_univ := Set.iUnion_const _
  pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim i j)).elim
  isConstructible_stratum _ := Topology.IsConstructible.univ
  domain _ := X
  immersion _ := 𝟙 X
  range_immersion _ := Set.range_id'

/-- A zero sheaf is constructible, with respect to the trivial stratification. -/
lemma IsConstructibleSheaf.of_isZero {F : Sheaf X.smallEtaleTopology A} (hF : IsZero F) :
    IsConstructibleSheaf F :=
  ⟨Stratification.trivial X, fun _ ↦
    IsFiniteLocallyConstantSheaf.of_isZero ((Etale.upperStar A (𝟙 X)).map_isZero hF)⟩

end Zero

section OpenImmersionPoints

variable {U : Scheme.{u}}

/-- If the complement of the range of a quasi-compact open immersion `j` is finite, every
closed point `x` of this complement is a constructible subset: the complement of `{x}` is the
union of the range of `j` and of a finite set, an open retrocompact subset. -/
lemma isConstructible_singleton_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hfin : (Set.range j.base)ᶜ.Finite) {x : X}
    (hx : x ∈ (Set.range j.base)ᶜ) (hcl : IsClosed {x}) : Topology.IsConstructible {x} := by
  have hfin' : IsRetrocompact ((Set.range j.base)ᶜ \ {x}) := fun V _ _ ↦
    ((hfin.sdiff).subset Set.inter_subset_left).isCompact
  have h : ({x} : Set X)ᶜ = Set.range j.base ∪ ((Set.range j.base)ᶜ \ {x}) := by
    ext y
    by_cases hy : y ∈ Set.range j.base
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, hy, true_or,
        iff_true]
      rintro rfl
      exact hx hy
    · simp [hy]
  refine Topology.IsConstructible.of_compl ?_
  rw [h]
  exact ((j.isRetrocompact_range).union hfin').isConstructible
    (h ▸ hcl.isOpen_compl)

/-- The stratification of `X` whose strata are the range of an open immersion `j : U ⟶ X`
and the points of its complement, when that complement is finite and consists of closed
points. The point strata are realized by the closed immersions
`X.fromSpecResidueField x ⟶ X`. -/
@[simps n]
def Stratification.ofOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hfin : (Set.range j.base)ᶜ.Finite) (hcl : ∀ x ∈ (Set.range j.base)ᶜ, IsClosed {x}) :
    Stratification X :=
  haveI := hfin.to_subtype
  let e := (Finite.equivFin ↥(Set.range j.base)ᶜ).symm
  { n := Nat.card ↥(Set.range j.base)ᶜ + 1
    stratum := Fin.cases (Set.range j.base) fun i ↦ {(e i).1}
    isLocallyClosed_stratum := Fin.cases j.isOpenEmbedding.isOpen_range.isLocallyClosed
      fun i ↦ (hcl _ (e i).2).isLocallyClosed
    isConstructible_stratum := Fin.cases (j.isConstructible_range)
      fun i ↦ isConstructible_singleton_of_isOpenImmersion j hfin (e i).2 (hcl _ (e i).2)
    iUnion_stratum_eq_univ := by
      refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
      by_cases hx : x ∈ Set.range j.base
      · exact ⟨0, hx⟩
      · refine ⟨(e.symm ⟨x, hx⟩).succ, ?_⟩
        rw [Fin.cases_succ, Equiv.apply_symm_apply]
        rfl
    pairwise_disjoint_stratum := by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd rfl hab
        | succ b =>
          simp only [Function.onFun, Fin.cases_zero, Fin.cases_succ]
          exact Set.disjoint_singleton_right.mpr (e b).2
      | succ a =>
        induction b using Fin.cases with
        | zero =>
          simp only [Function.onFun, Fin.cases_zero, Fin.cases_succ]
          exact Set.disjoint_singleton_left.mpr (e a).2
        | succ b =>
          have : e a ≠ e b := fun h ↦ hab (by rw [e.injective h])
          simp only [Function.onFun, Fin.cases_succ]
          exact Set.disjoint_singleton.mpr (Subtype.coe_injective.ne this)
    domain := Fin.cases U fun i ↦ Spec (X.residueField (e i).1)
    immersion := Fin.cases j fun i ↦ X.fromSpecResidueField (e i).1
    isImmersion := Fin.cases (inferInstanceAs (IsImmersion j)) fun i ↦
      have := (isClosed_singleton_iff_isClosedImmersion (x := (e i).1)).mp (hcl _ (e i).2)
      inferInstanceAs (IsImmersion (X.fromSpecResidueField (e i).1))
    range_immersion := Fin.cases rfl fun i ↦ Scheme.range_fromSpecResidueField (e i).1 }

end OpenImmersionPoints

section Devissage

variable {U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- Blueprint `prop-constructible-open-closed`, first assertion: stratifications of the members
of a complementary pair `(j, i)` concatenate to a stratification of `X`: the strata are the
images of the strata of `U` and of `Z`. The open immersion `j` is assumed quasi-compact (its
range retrocompact), so that the images of constructible strata are constructible: this is
implicit in the blueprint, whose constructible subsets are meant in the sense of a
quasi-compact quasi-separated (e.g. Noetherian) scheme, where it is automatic. -/
def Stratification.openClosed (SU : Stratification U) (SZ : Stratification Z) :
    Stratification X where
  n := SU.n + SZ.n
  stratum k := Sum.elim (fun l ↦ j.base '' SU.stratum l) (fun l ↦ i.base '' SZ.stratum l)
    (finSumFinEquiv.symm k)
  isLocallyClosed_stratum k := by
    generalize finSumFinEquiv.symm k = s
    rcases s with l | l
    · exact (SU.isLocallyClosed_stratum l).image j.isOpenEmbedding.isInducing
        j.isOpenEmbedding.isOpen_range.isLocallyClosed
    · exact (SZ.isLocallyClosed_stratum l).image i.isEmbedding.isInducing
        i.isLocallyClosed_range
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Set.range j.base
    · obtain ⟨u, rfl⟩ := hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (SU.iUnion_stratum_eq_univ ▸ Set.mem_univ u)
      exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inl l), by simpa using ⟨u, hl, rfl⟩⟩
    · rw [← Set.mem_compl_iff, ← hij] at hx
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (SZ.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
      exact Set.mem_iUnion.mpr ⟨finSumFinEquiv (Sum.inr l), by simpa using ⟨z, hl, rfl⟩⟩
  isConstructible_stratum k := by
    generalize finSumFinEquiv.symm k = s
    rcases s with l | l
    · exact (SU.isConstructible_stratum l).image_of_isOpenEmbedding j.isOpenEmbedding
        (j.isRetrocompact_range)
    · refine (SZ.isConstructible_stratum l).image_of_isClosedEmbedding i.isClosedEmbedding ?_
      rw [hij, compl_compl]
      exact j.isRetrocompact_range
  pairwise_disjoint_stratum k k' hkk' := by
    have hne : finSumFinEquiv.symm k ≠ finSumFinEquiv.symm k' :=
      fun h ↦ hkk' (finSumFinEquiv.symm.injective h)
    have hji : Disjoint (Set.range j.base) (Set.range i.base) := by
      rw [hij]
      exact disjoint_compl_right
    change Disjoint (Sum.elim _ _ (finSumFinEquiv.symm k)) (Sum.elim _ _ (finSumFinEquiv.symm k'))
    generalize finSumFinEquiv.symm k = s at hne ⊢
    generalize finSumFinEquiv.symm k' = s' at hne ⊢
    rcases s with l | l <;> rcases s' with l' | l' <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · exact (Set.disjoint_image_iff j.isOpenEmbedding.injective).mpr
        (SU.pairwise_disjoint_stratum (fun h ↦ hne (by rw [h])))
    · exact hji.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
    · exact hji.symm.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
    · exact (Set.disjoint_image_iff i.isEmbedding.injective).mpr
        (SZ.pairwise_disjoint_stratum (fun h ↦ hne (by rw [h])))
  domain k := Sum.elim SU.domain SZ.domain (finSumFinEquiv.symm k)
  immersion k := Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
    (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i) (finSumFinEquiv.symm k)
  isImmersion k := by
    generalize finSumFinEquiv.symm k = s
    rcases s with l | l
    · exact inferInstanceAs (IsImmersion (SU.immersion l ≫ j))
    · exact inferInstanceAs (IsImmersion (SZ.immersion l ≫ i))
  range_immersion k := by
    generalize finSumFinEquiv.symm k = s
    rcases s with l | l
    · change Set.range (SU.immersion l ≫ j).base = j.base '' SU.stratum l
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, SU.range_immersion]
    · change Set.range (SZ.immersion l ≫ i).base = i.base '' SZ.stratum l
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, SZ.range_immersion]

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

include hij in
/-- Blueprint `prop-constructible-open-closed`: **A sheaf is constructible if and only if its
restrictions to the members of a complementary pair `(j, i)` are**, for `j` quasi-compact (see
`AlgebraicGeometry.Scheme.Stratification.openClosed`). -/
theorem isConstructibleSheaf_iff_upperStar (F : Sheaf X.smallEtaleTopology A) :
    IsConstructibleSheaf F ↔
      IsConstructibleSheaf ((Etale.upperStar A j).obj F) ∧
        IsConstructibleSheaf ((Etale.upperStar A i).obj F) := by
  refine ⟨fun _ ↦ ⟨IsConstructibleSheaf.upperStar j F, IsConstructibleSheaf.upperStar i F⟩,
    fun ⟨hU, hZ⟩ ↦ ?_⟩
  obtain ⟨SU, hSU⟩ := hU.exists_stratification
  obtain ⟨SZ, hSZ⟩ := hZ.exists_stratification
  refine ⟨Stratification.openClosed j i hij SU SZ, fun k ↦ ?_⟩
  change IsFiniteLocallyConstantSheaf ((Etale.upperStar A
    (Sum.rec (motive := fun s ↦ Sum.elim SU.domain SZ.domain s ⟶ X)
      (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i) (finSumFinEquiv.symm k))).obj F)
  generalize finSumFinEquiv.symm k = s
  rcases s with l | l
  · have := hSU l
    exact IsFiniteLocallyConstantSheaf.of_iso (F := (Etale.upperStar A (SU.immersion l)).obj
      ((Etale.upperStar A j).obj F))
      ((Etale.upperStarComp A (SU.immersion l) j).app F).symm
  · have := hSZ l
    exact IsFiniteLocallyConstantSheaf.of_iso (F := (Etale.upperStar A (SZ.immersion l)).obj
      ((Etale.upperStar A i).obj F))
      ((Etale.upperStarComp A (SZ.immersion l) i).app F).symm

include hij in
/-- **The extension by zero of a constructible sheaf along an open immersion is
constructible**: its restriction to `U` is the sheaf itself, and its restriction to the
complement `Z` vanishes. (blueprint: `lemma:constructible-lowerShriek-open`) -/
theorem IsConstructibleSheaf.openImmersionLowerShriek (G : Sheaf U.smallEtaleTopology A)
    [IsConstructibleSheaf G] : IsConstructibleSheaf ((j)_!open[A].obj G) := by
  rw [isConstructibleSheaf_iff_upperStar j i hij]
  have hji : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  refine ⟨?_, IsConstructibleSheaf.of_isZero
    (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i hji G)⟩
  exact IsConstructibleSheaf.of_iso (F := G)
    (asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app G))

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hij hJ in
/-- **The pushforward of a constructible sheaf along a closed immersion is constructible**:
its restriction to `Z` is the sheaf itself, and its restriction to the complement `U`
vanishes. (blueprint: `lemma:constructible-lowerStar-closed`) -/
theorem IsConstructibleSheaf.lowerStar_of_isClosedImmersion (G : Sheaf Z.smallEtaleTopology A)
    [IsConstructibleSheaf G] : IsConstructibleSheaf ((i)_*[A].obj G) := by
  rw [isConstructibleSheaf_iff_upperStar j i hij]
  have hji : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [hij]
    exact disjoint_compl_right
  refine ⟨IsConstructibleSheaf.of_isZero
    (Etale.isZero_upperStar_lowerStar_of_disjoint_range A j i hji G), ?_⟩
  exact IsConstructibleSheaf.of_iso (F := G)
    (asIso ((Etale.upperStarLowerStarAdjunction A i).counit.app G)).symm

end Devissage

end AlgebraicGeometry.Scheme

end
