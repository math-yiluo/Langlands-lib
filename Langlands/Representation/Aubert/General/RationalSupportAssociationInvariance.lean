import Langlands.Representation.Aubert.General.RationalSupportAssociationStructure
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.GroupScheme.Rational.RootFiniteness

noncomputable section

set_option maxHeartbeats 1600000

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.GroupTransport

private theorem pullback_subsingleton
    {H H' : Type u} [Group H] [Group H']
    [TopologicalSpace H] [TopologicalSpace H']
    (e : H' ≃ₜ* H) (A : SmoothRep.{0, u, v} ℂ H)
    (hA : Subsingleton A) :
    Subsingleton ((SmoothRep.pullbackFunctor e).obj A) := hA

private theorem subsingleton_of_iso
    {H : Type u} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, u, v} ℂ H} (e : A ≅ B)
    (hA : Subsingleton A) : Subsingleton B := by
  let := hA
  exact (SmoothRep.equivOfIso e).symm.injective.subsingleton

private theorem jacquet_subsingleton_transport
    {H H' : Type u} [Group H] [Group H']
    [TopologicalSpace H] [TopologicalSpace H']
    [LocallyCompactSpace H] [LocallyCompactSpace H']
    [NonarchimedeanGroup H] [NonarchimedeanGroup H']
    {P M U : Subgroup H} {P' M' U' : Subgroup H'}
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H' ≃ₜ* H)
    (hMM' : ∀ x : H', x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H', x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set H)) (hU' : IsClosed (U' : Set H'))
    (A : SmoothRep.{0, u, v} ℂ H)
    (hA : Subsingleton ((jacquetFunctor h hU).obj A)) :
    Subsingleton ((jacquetFunctor h' hU').obj ((SmoothRep.pullbackFunctor e).obj A)) := by
  exact subsingleton_of_iso
    (H := M')
    (A := (SmoothRep.pullbackFunctor (subgroupEquiv e hMM')).obj
      ((jacquetFunctor h hU).obj A))
    (B := (jacquetFunctor h' hU').obj ((SmoothRep.pullbackFunctor e).obj A))
    (jacquetIsoApp h h' e hMM' hUU' hU hU' A)
    (pullback_subsingleton (subgroupEquiv e hMM') ((jacquetFunctor h hU).obj A) hA)

end Langlands.Aubert.General.GroupTransport

namespace Langlands.Aubert.General

private theorem conjugation_composite_membership
    {H : Type u} [Group H] {M N L : Subgroup H} (n m : H)
    (hn : ∀ x : H, x ∈ N ↔ n⁻¹ * x * n ∈ M)
    (hm : ∀ x : H, x ∈ L ↔ m⁻¹ * x * m ∈ M) :
    ∀ x : H, x ∈ L ↔ (m * n⁻¹)⁻¹ * x * (m * n⁻¹) ∈ N := by
  intro x
  rw [hn]
  have heq : n⁻¹ * ((m * n⁻¹)⁻¹ * x * (m * n⁻¹)) * n = m⁻¹ * x * m := by group
  rw [heq]
  exact hm x

/-- Successive conjugations by `n` and `m n⁻¹` recover conjugation by `m`. -/
private def conjugationCancelIso
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {M N L : Subgroup H} (n m : H)
    (hn : ∀ x : H, x ∈ N ↔ n⁻¹ * x * n ∈ M)
    (hm : ∀ x : H, x ∈ L ↔ m⁻¹ * x * m ∈ M)
    (hp : ∀ x : H, x ∈ L ↔ (m * n⁻¹)⁻¹ * x * (m * n⁻¹) ∈ N)
    (σ : SmoothRep.{0, u, v} ℂ M) :
    (conjugationFunctor m hm).obj σ ≅
      (conjugationFunctor (m * n⁻¹) hp).obj ((conjugationFunctor n hn).obj σ) :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun x => by
    ext v
    change σ.representation (conjugationEquiv m hm x) v =
      σ.representation (conjugationEquiv n hn (conjugationEquiv (m * n⁻¹) hp x)) v
    apply congrArg (fun y : M => σ.representation y v)
    apply Subtype.ext
    change m⁻¹ * (x : H) * m =
      n⁻¹ * ((m * n⁻¹)⁻¹ * (x : H) * (m * n⁻¹)) * n
    group))

/-- Transport all defining induction witnesses through a fixed conjugation. -/
private theorem supportCategory_conjugation
    {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {R : Type w} (P M U : Finset R → Subgroup H)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set H)) (hM : ∀ I, IsClosed (M I : Set H))
    (hL : ∀ (I : Finset R) (K : Finset I),
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
    (IsAssociate : Finset R → Finset R → H → Prop)
    {I I' : Finset R} {n : H}
    (hn : ∀ x : H, x ∈ M I' ↔ n⁻¹ * x * n ∈ M I)
    (ha : ∀ (J : Finset R) (m : H), IsAssociate I J m → IsAssociate I' J (m * n⁻¹))
    (hc : ∀ σ : SmoothRep.{0, u, max u v} ℂ (M I),
      IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU I' (hM I') (hL I') ((conjugationFunctor n hn).obj σ))
    (E : SmoothRep.{0, u, max u v} ℂ H)
    (hE : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) E) :
    IsInSupportCategory P M U h hU IsAssociate I' (hM I') (hL I') E := by
  intro π hπ hπE
  obtain ⟨J, m, hm, hIJ, σ, hσ, hσc, hπσ⟩ := hE π hπ hπE
  let hp := conjugation_composite_membership n m hn hm
  refine ⟨J, m * n⁻¹, hp, ha J m hIJ, (conjugationFunctor n hn).obj σ, ?_, hc σ hσc, ?_⟩
  · exact (isIrreducible_comp_continuousMulEquiv_iff σ.representation
      (conjugationEquiv n hn)).mpr hσ
  · exact hπσ.of_iso_right
      ((normalizedInductionFunctor (h J) (hU J)).mapIso (conjugationCancelIso n m hn hm hp σ))

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

section Cuspidality

variable [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Conjugation preserves the actual proper-standard inside-Levi vanishing
predicate, using the given standard cocharacters and intersection data. -/
theorem isLeviCuspidal_conjugation
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
    {I J : Finset (SimpleRoot i ν)} {n : RationalPoint k G.X}
    (hn : ∀ x, x ∈ levi i ν J ↔ n⁻¹ * x * n ∈ levi i ν I)
    (hIJ : rootAssociation i ν hN hZ I J n)
    (σ : SmoothRep.{0, u, v} ℂ (levi i ν I))
    (hc : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ) :
    IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J)
      ((conjugationFunctor n hn).obj σ) := by
  let := (hM I).locallyCompactSpace
  let := (hM J).locallyCompactSpace
  intro K'
  obtain ⟨K, hK, hKK'⟩ :=
    exists_associated_nested_subset i ν hN hZ hIJ K'.val K'.property
  have hMM' (x : levi i ν J) :
      x ∈ (levi i ν (leviIndex J K'.val)).subgroupOf (levi i ν J) ↔
        conjugationEquiv n hn x ∈
          (levi i ν (leviIndex I K)).subgroupOf (levi i ν I) :=
    rootAssociation_levi_membership i ν hN hZ hG hi hν hStandard hKK' x
  have hUU' (x : levi i ν J) :
      x ∈ (unipotent i ν (leviIndex J K'.val)).subgroupOf (levi i ν J) ↔
        conjugationEquiv n hn x ∈
          (unipotent i ν (leviIndex I K)).subgroupOf (levi i ν I) :=
    rootAssociation_nested_unipotent_membership i ν hN hZ hG hi hν hStandard
      (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) hIJ hKK' x x.property
  exact GroupTransport.jacquet_subsingleton_transport
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I K)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K'.val)
    (conjugationEquiv n hn) hMM' hUU'
    ((hU (leviIndex I K)).preimage continuous_subtype_val)
    ((hU (leviIndex J K'.val)).preimage continuous_subtype_val) σ (hc ⟨K, hK⟩)

end Cuspidality

/-- The actual full smooth support category is invariant under association. -/
theorem rationalSupportCategoryAssociationInvariance :
    RationalSupportCategoryAssociationInvarianceStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro I I' n hII' hn E hE
  exact supportCategory_conjugation
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (rootAssociation i ν hN hZ) hn
    (fun J m hIJ => rootAssociation_mul i ν hN hZ
      (rootAssociation_inv i ν hN hZ hII') hIJ)
    (fun σ hc => isLeviCuspidal_conjugation i ν hG hi hν hStandard hInter hRoots hN hZ
      hU hM hn hII' σ hc) E hE

end Langlands.Aubert.General.RationalPointFamily
