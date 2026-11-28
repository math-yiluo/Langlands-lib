import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.General.LocalFieldGLRationalFunctorsProof

/-! # Exact Grothendieck transport for the local-field GL operator -/

noncomputable section

set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.AlgebraicGeometry.PointTopology
open GroupScheme SmoothRep FiniteLengthGrothendieckGroup

section ExactTransport

variable {A B C D : Type u} [Group A] [Group B] [Group C] [Group D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

private theorem matrixMap_of_pullbackSquare
    {Φ : SmoothRep.{0, u, max (u + 1) v} ℂ A ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ B}
    {Ψ : SmoothRep.{0, u, max (u + 1) v} ℂ C ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ D}
    (eA : C ≃ₜ* A) (eB : D ≃ₜ* B)
    (cmp : Φ ⋙ pullbackFunctor eB ≅ pullbackFunctor eA ⋙ Ψ)
    (hl : PreservesFiniteLength Ψ) (hx : PreservesFiniteLengthShortExact Ψ) :
    ∃ (hl' : PreservesFiniteLength Φ) (hx' : PreservesFiniteLengthShortExact Φ),
      (FiniteLengthGrothendieckGroup.pullback eB).comp (map Φ hl' hx') =
        (map Ψ hl hx).comp (FiniteLengthGrothendieckGroup.pullback eA) := by
  have hA := pullbackFunctor_preservesFiniteLength.{u, u, max (u + 1) v} eA
  have hAx := pullbackFunctor_preservesShortExact.{u, u, max (u + 1) v} eA
  have hB := pullbackFunctor_preservesFiniteLength.{u, u, max (u + 1) v} eB
  have hBx := pullbackFunctor_preservesShortExact.{u, u, max (u + 1) v} eB
  have hlp := (hA.comp hl).of_iso cmp.symm
  have hxp := (PreservesFiniteLengthShortExact.comp hA hAx hx).of_iso cmp.symm
  have hl' : PreservesFiniteLength Φ := fun X hX =>
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff (Φ.obj X).representation
      eB.toMonoidHom eB.surjective).mpr (hlp X hX)
  have hx' : PreservesFiniteLengthShortExact Φ :=
    fun _ _ _ f g hX hY hZ hfg => hxp f g hX hY hZ hfg
  refine ⟨hl', hx', ?_⟩
  calc
    _ = map _ hlp hxp := (map_comp _ _ hl' hx' hB hBx _ _).symm
    _ = map _ (hA.comp hl) (PreservesFiniteLengthShortExact.comp hA hAx hx) :=
      map_eq_of_iso cmp _ _ _ _
    _ = _ := map_comp _ _ hA hAx hl hx _ _

private theorem matrixTerm_of_pullbackSquares
    {i₁ : SmoothRep.{0, u, max (u + 1) v} ℂ A ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ B}
    {r₁ : SmoothRep.{0, u, max (u + 1) v} ℂ B ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ A}
    {i₂ : SmoothRep.{0, u, max (u + 1) v} ℂ C ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ D}
    {r₂ : SmoothRep.{0, u, max (u + 1) v} ℂ D ⥤ SmoothRep.{0, u, max (u + 1) v} ℂ C}
    (eA : C ≃ₜ* A) (eB : D ≃ₜ* B)
    (α : i₁ ⋙ pullbackFunctor eB ≅ pullbackFunctor eA ⋙ i₂)
    (β : r₁ ⋙ pullbackFunctor eA ≅ pullbackFunctor eB ⋙ r₂)
    (hi : PreservesFiniteLength i₂) (hix : PreservesFiniteLengthShortExact i₂)
    (hr : PreservesFiniteLength r₂) (hrx : PreservesFiniteLengthShortExact r₂) :
    ∃ (hi' : PreservesFiniteLength i₁) (hix' : PreservesFiniteLengthShortExact i₁)
      (hr' : PreservesFiniteLength r₁) (hrx' : PreservesFiniteLengthShortExact r₁),
      let p := FiniteLengthGrothendieckGroup.pullback eB
      p.comp ((map i₁ hi' hix').comp (map r₁ hr' hrx')) =
        ((map i₂ hi hix).comp (map r₂ hr hrx)).comp p := by
  obtain ⟨hi', hix', hI⟩ := matrixMap_of_pullbackSquare eA eB α hi hix
  obtain ⟨hr', hrx', hR⟩ := matrixMap_of_pullbackSquare eB eA β hr hrx
  refine ⟨hi', hix', hr', hrx', ?_⟩
  dsimp only
  rw [← LinearMap.comp_assoc, hI, LinearMap.comp_assoc, hR, LinearMap.comp_assoc]

end ExactTransport

private theorem reindexed_signed_sum
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module ℤ X] [Module ℤ Y]
    {Index₁ Index₂ : Type*} [Fintype Index₁] [Fintype Index₂] (idx : Index₁ ≃ Index₂)
    (p : X →ₗ[ℤ] Y) (a : Index₁ → X →ₗ[ℤ] X) (b : Index₂ → Y →ₗ[ℤ] Y)
    (s : Index₁ → ℤ) (t : Index₂ → ℤ)
    (h : ∀ i, p.comp (a i) = (b (idx i)).comp p)
    (hs : ∀ i, s i = t (idx i)) :
    p.comp (∑ i, s i • a i) = (∑ j, t j • b j).comp p := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.sum_apply]
  refine Fintype.sum_equiv idx _ _ fun i => ?_
  change p (s i • a i x) = t (idx i) • b (idx i) (p x)
  rw [map_zsmul, hs]
  exact congrArg (t (idx i) • ·) (LinearMap.congr_fun (h i) x)

private theorem matrixOperator_of_pullbackSquares
    {F : Type u} [Field F] (T : LocalFieldData F) (n : ℕ)
    {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {Root : Type u} [Fintype Root]
    (P M U : Finset Root → Subgroup H)
    (dec : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
    (hU : ∀ J, IsClosed (U J : Set H))
    (hfl : ∀ J, ParabolicFiniteLength.{u, max (u + 1) v} (dec J) (hU J))
    (idx : Langlands.GeneralLinear.BlockShape n ≃ Finset Root)
    (hSign : ∀ B, (-1 : ℤ) ^ (idx B).card = (-1 : ℤ) ^ (n - B.length))
    (hmod : Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement.{u}) :
    letI := T.topology
    ∀ (e : H ≃ₜ* Langlands.GeneralLinear n F),
      (∀ B x, x ∈ P (idx B) ↔ e x ∈ B.parabolic F) →
      (∀ B x, x ∈ M (idx B) ↔ e x ∈ B.leviSubgroup F) →
      (∀ B x, x ∈ U (idx B) ↔ e x ∈ B.unipotentSubgroup F) →
      LocalFieldMatrixParabolicExactLength.{u, v} T n ∧
        ∀ h : LocalFieldMatrixParabolicExactLength.{u, v} T n,
          let p := FiniteLengthGrothendieckGroup.pullback.{u, u, max (u + 1) v} e
          p.comp (localFieldMatrixAlternatingOperator T n h) =
            (alternatingOperator.{u, u, max (u + 1) v} P M U dec hU hfl).comp p := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : Fintype (Langlands.GeneralLinear.BlockShape n) := Fintype.ofFinite _
  intro e hP hM hR
  let term := alternatingTerm.{u, u, max (u + 1) v}
    P M U dec hU hfl
  let p := FiniteLengthGrothendieckGroup.pullback.{u, u, max (u + 1) v} e
  have blockSquare (B : Langlands.GeneralLinear.BlockShape n) :
      ∃ (hlI : PreservesFiniteLength (T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B))
        (hxI : PreservesFiniteLengthShortExact (T.normalizedParabolicInductionFunctor B))
        (hlR : PreservesFiniteLength (T.normalizedJacquetFunctor.{u, max (u + 1) v} B))
        (hxR : PreservesFiniteLengthShortExact (T.normalizedJacquetFunctor B)),
      p.comp ((map (T.normalizedParabolicInductionFunctor B) hlI hxI).comp
        (map (T.normalizedJacquetFunctor B) hlR hxR)) = (term (idx B)).comp p := by
    obtain ⟨⟨α, _⟩, ⟨β, _⟩⟩ :=
      localFieldGLFunctors_of_subgroupEquiv.{u, v} T B (dec (idx B)) (hU (idx B))
        hmod e (hP B) (hM B) (hR B)
    let hLen := hfl (idx B)
    exact matrixTerm_of_pullbackSquares _ e α β hLen.1 hLen.2.1 hLen.2.2.1 hLen.2.2.2
  choose hlI hxI hlR hxR hterm using blockSquare
  refine ⟨fun B => ⟨hlI B, hxI B, hlR B, hxR B⟩, ?_⟩
  intro h
  change p.comp (localFieldMatrixAlternatingOperator T n h) =
    (alternatingOperator.{u, u, max (u + 1) v} P M U dec hU hfl).comp p
  unfold localFieldMatrixAlternatingOperator alternatingOperator
  exact reindexed_signed_sum idx p _ term _ _ hterm
    (fun B => (hSign B).symm)

theorem localFieldGLRationalOperatorComparison :
    LocalFieldGLRationalOperatorComparisonStatement.{u, v} := by
  intro F _ T n ν hν hiFl hrFl
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv n F
  let : IsTopologicalGroup (RationalPoint F G.X) :=
    GroupScheme.GeneralLinear.rationalPoints_isTopologicalGroup n F
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let : LocallyCompactSpace (RationalPoint F G.X) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : NonarchimedeanGroup (RationalPoint F G.X) :=
    NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMonoidHom
      e.symm.toHomeomorph.isOpenEmbedding
  let : T2Space (RationalPoint F G.X) := e.toHomeomorph.isEmbedding.t2Space
  let iD := GroupScheme.GeneralLinear.diagonalTorus (Fin n) (CommRingCat.of F)
  let hG := isConnectedReductive_generalLinear F (Fin n)
  let hi := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin n) F
  let hgen := (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mpr
    hν.injective
  let := simpleRelativeRootFintype iD
    (relativeRootSystem F G hG _ iD hi) hi.isSplitSubtorus.1 ν
  let idx := blockRootSubsetEquiv F ν hν
  let dec := isSemidirectDecomposition_of_standardCocharacterStatement iD ν
    standardCocharacter.{u} hG hi hgen
  let hU := canonicalStandardUnipotent_isClosed hG iD ν hi hgen
  let hfl := canonicalStandardParabolicFiniteLength.{u, v} hG iD ν hi hgen hiFl hrFl
  exact matrixOperator_of_pullbackSquares T n (parabolic iD ν) (levi iD ν)
    (unipotent iD ν) dec hU hfl idx (blockRootSubsetEquiv_sign F ν hν)
    Parabolic.localFieldGeneralLinearModulusCompatibility e
    (fun B x => SetLike.ext_iff.mp (parabolic_blockRootSubsetEquiv F ν hν B) x)
    (fun B x => SetLike.ext_iff.mp (levi_blockRootSubsetEquiv F ν hν B) x)
    (fun B x => SetLike.ext_iff.mp (unipotent_blockRootSubsetEquiv F ν hν B) x)

end Langlands.Aubert.General.RationalPointFamily.GL
