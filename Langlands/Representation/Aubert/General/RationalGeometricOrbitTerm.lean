import Langlands.Representation.Aubert.General.RationalGeometricOrbitSource
import Langlands.Representation.Aubert.General.RationalGeometricCommonLeviRefinements
import Langlands.Representation.Aubert.General.SemidirectQuotientCompactness
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-!
# Orbit grades of `r_I ∘ i_J` as actual normalized geometric terms

For the actual rational standard family, every Jacquet support grade of
`r_I ∘ i_J` at an orbit `P_J n⁻¹ P_I` is naturally the published normalized
geometric term `geometricTermFunctor … I J n`, provided the two original
epsilon corrections cancel.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General

section TrivialTwist

variable {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]

/-- Twisting by a smooth character with trivial underlying homomorphism is
naturally the identity, with identity linear maps. -/
def twistFunctorIsoOfEqOne (χ : Induction.SmoothCharacter R H) (h : χ.toMonoidHom = 1) :
    χ.twistFunctor.{_, _, uV} ≅ 𝟭 (Rep.{uV} R H) :=
  NatIso.ofComponents
    (fun A => Rep.mkIso
      { toLinearEquiv := LinearEquiv.refl R A
        isIntertwining' := fun g => by
          apply LinearMap.ext
          intro v
          change (χ.toMonoidHom g : R) • A.ρ g v = A.ρ g v
          rw [h, MonoidHom.one_apply, Units.val_one, one_smul] })
    (fun _ => rfl)

end TrivialTwist

section SemidirectInf

variable {A : Type*} [Group A] {P M U : Subgroup A}

/-- In an actual semidirect decomposition the Levi and the radical meet trivially. -/
theorem IsSemidirectDecomposition.eq_one_of_mem_levi_of_mem_unipotent
    (h : IsSemidirectDecomposition P M U) {x : A} (hM : x ∈ M) (hU : x ∈ U) : x = 1 := by
  have h1 := h.projection_levi ⟨x, hM⟩
  have h2 := h.projection_unipotent ⟨x, hU⟩
  have h3 : (⟨x, h.levi_le hM⟩ : P) = ⟨x, h.unipotent_le hU⟩ := rfl
  rw [h3, h2] at h1
  exact congrArg Subtype.val h1.symm

/-- A refinement parabolic `(M_I ∩ Q) · U_I`, read inside `M_I`, is the literal
`M_I ∩ Q`. -/
theorem refinementParabolic_subgroupOf_levi
    {PI MI UI Q : Subgroup A} (dI : IsSemidirectDecomposition PI MI UI)
    (Pψ : Subgroup A)
    (hP : (Pψ : Set A) = (↑(MI ⊓ Q) : Set A) * (UI : Set A)) :
    Pψ.subgroupOf MI = (MI ⊓ Q).subgroupOf MI := by
  ext m
  change (m : A) ∈ Pψ ↔ (m : A) ∈ MI ⊓ Q
  constructor
  · intro hm
    have hm' : (m : A) ∈ (Pψ : Set A) := hm
    rw [hP] at hm'
    obtain ⟨a, ha, u, hu, hau⟩ := hm'
    have huM : u ∈ MI := by
      have : u = a⁻¹ * (m : A) := by rw [← hau]; group
      rw [this]
      exact MI.mul_mem (MI.inv_mem ha.1) m.2
    have hu1 := dI.eq_one_of_mem_levi_of_mem_unipotent huM hu
    have ham : a * 1 = (m : A) := by rw [← hu1]; exact hau
    rw [mul_one] at ham
    rw [← ham]
    exact ha
  · intro hm
    have : (m : A) ∈ (Pψ : Set A) := by
      rw [hP]
      exact ⟨m, hm, 1, UI.one_mem, mul_one _⟩
    exact this

end SemidirectInf

namespace RationalPointFamily

open GroupScheme Induction
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

local notation "A" => RationalPoint k G.X

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The literal target-intersection parabolic `M_I ∩ n P_J n⁻¹` has compact
coset space in `M_I`. -/
theorem compactSpace_leftQuotient_geometricTarget
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I)) :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [IsTopologicalGroup (RationalPoint k G.X)]
      [WeaklyLocallyCompactSpace (RationalPoint k G.X)],
      IsClosed (parabolic i ν I : Set (RationalPoint k G.X)) →
      Continuous dI.projection →
      CompactSpace (Induction.LeftQuotient
        ((geometricTargetIntersection (levi i ν I) (parabolic i ν J)
          (n : RationalPoint k G.X)).subgroupOf (levi i ν I))) := by
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ hPI hprojI
  obtain ⟨ψ, θ, hψ, -, -, -⟩ :=
    exists_geometric_common_levi_refinements i ν hStandard hG hi hν hN I J n
  obtain ⟨hle, -, hUle, -, hprod⟩ := hψ
  have hcpt : CompactSpace (Induction.LeftQuotient
      ((Dynamic.parabolic ψ).carrier (Over.mk (𝟙 _)))) :=
    (BruhatTits.dynamicParabolicQuotientCompact k G hG ψ).2
  have hUQ : unipotent i ν I ≤ (Dynamic.parabolic ψ).rationalPoints := by
    intro u hu
    have : u ∈ ((Dynamic.parabolic ψ).rationalPoints : Set (RationalPoint k G.X)) := by
      rw [hprod]
      exact ⟨1, Subgroup.one_mem _, u, hu, one_mul u⟩
    exact this
  have hc := IsSemidirectDecomposition.compactSpace_leftQuotient_subgroupOf_levi
    (Q := (Dynamic.parabolic ψ).rationalPoints) dI hPI hprojI hle hUQ
  rw [refinementParabolic_subgroupOf_levi dI _ hprod] at hc
  exact hc

section Grade

local instance orbitTermPointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hM : ∀ H, IsClosed (levi i ν H : Set (RationalPoint k G.X)))
  (hU : ∀ H, IsClosed (unipotent i ν H : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection)
  (hUIc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

include hStandard hG hi hν hN hpI in
/-- Once the two original epsilon corrections cancel, the epsilon-twisted
compact geometric term is the published normalized geometric term. -/
def geometricEpsilonCompactTermIso
    (hε : geometricEpsilonOne i ν I J dI dJ n (hU J) hPI *
      geometricEpsilonTwo i ν I J dI dJ n (hU I) hPJ = 1) :
    geometricTermEpsilonCompactFunctor.{u, max u uV}
        i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ ⋙ SmoothRep.toRep ≅
      geometricTermFunctor.{u, u, uV} (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
        (n : RationalPoint k G.X) hSource hTarget ⋙ SmoothRep.toRep := by
  haveI := compactSpace_leftQuotient_geometricTarget i ν I J n hStandard hG hi hν hN dI hPI hpI
  have hε' : (geometricInflatedEpsilonProductSmoothCharacter
      i ν I J dI dJ n hU hTarget hPJ hPI hpJ).toMonoidHom = 1 := by
    change MonoidHom.comp (_ * _) hTarget.projection = 1
    rw [hε, MonoidHom.one_comp]
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (twistFunctorIsoOfEqOne _ hε') _ ≪≫ Functor.leftUnitor _) ≪≫
      Functor.isoWhiskerLeft _ (compactSmoothIso _)) SmoothRep.toRep

include hStandard hG hi hν hN hpI hUIc hUJc in
/-- At an orbit `P_J n⁻¹ P_I` of an ordered orbit cover, the Jacquet support
grade of `r_I ∘ i_J` is naturally the published normalized geometric term,
once the two original epsilon corrections cancel. -/
def jacquetSupportGeometricTermIso
    (hε : geometricEpsilonOne i ν I J dI dJ n (hU J) hPI *
      geometricEpsilonTwo i ν I J dI dJ n (hU I) hPJ = 1)
    {m : ℕ} (s : Geometric.OrderedDoubleCosets (parabolic i ν J) (parabolic i ν I) m)
    (q : Fin m) (hq : s.representative q = (n : RationalPoint k G.X)) :
    (jacquetSupportFiltration.{u, max u uV} dJ (hU J) dI (hU I) s).graded q ≅
      geometricTermFunctor.{u, u, uV} (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J
        (n : RationalPoint k G.X) hSource hTarget ⋙ SmoothRep.toRep := by
  haveI := reductiveRationalPoint_secondCountable k G hG
  haveI := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν J
  have hVc := isLimitOfCompactSubgroups_subgroupOf (unipotent i ν I) (parabolic i ν I) hPI hUIc
  refine jacquetSupportOrbitIso dJ (hU J) hpJ dI (hU I) hPJ hPI hVc s q ≪≫ ?_
  rw [hq]
  exact orbitPieceCoinvariantsIso dI dJ (n : RationalPoint k G.X) (hU I) (hU J) hpJ hUJc ≪≫
    (geometricNormalizedCompactSourceRepIso i ν I J dI dJ n (hU I) (hU J) hPJ hSource hTarget
      hPI (hM I) (hM J) hUIc hStandard hG hi hν hN hpI hpJ).symm ≪≫
    Functor.isoWhiskerRight (geometricNormalizedCompactActualNatIso
      i ν I J dI dJ n hM hU hSource hTarget hPJ hPI hpJ hStandard hG hi hν hN hUJc hpI hUIc)
      SmoothRep.toRep ≪≫
    geometricEpsilonCompactTermIso i ν I J n hStandard hG hi hν hN dI dJ hM hU hPI hPJ hpI hpJ
      hSource hTarget hε

end Grade

end RationalPointFamily

end Langlands.Aubert.General
