import Langlands.Representation.Aubert.General.ParabolicSupportFiltration
import Langlands.Representation.Aubert.General.RationalGeometricNormalizedActualCompact
import Langlands.Representation.Jacquet.NormalCoinvariantLocalization

/-!
# The parabolic orbit piece as the actual normalized compact orbit source

The support filtration of `ParabolicSupportFiltration` has graded pieces
`smoothParabolicInducingFunctor ⋙ orbitPiece ⋙ parabolicCoinvariantsFunctor`.
This module identifies that composite, naturally, with compact induction from
the literal target intersection followed by Mathlib's normal coinvariants of
the kernel of the Levi projection. For the actual rational standard family the
latter is, by definition, the published `geometricNormalizedCompactSourceFunctor`.
-/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General

open Induction

section SubgroupTransport

variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact induction from equal subgroups with pointwise equal coefficient
actions; the underlying functions are unchanged. -/
def compactInducedSubgroupEqEquiv {S H : Subgroup Q} (hSH : S = H)
    (ρA : Representation ℂ S V) (ρB : Representation ℂ H V)
    (hρ : ∀ (x : Q) (hS : x ∈ S) (hH : x ∈ H), ρA ⟨x, hS⟩ = ρB ⟨x, hH⟩) :
    (compactInduced S ρA).Equiv (compactInduced H ρB) := by
  subst hSH
  have h : ρA = ρB := MonoidHom.ext fun x => hρ x.1 x.2 x.2
  subst h
  exact Representation.Equiv.refl _

@[simp]
theorem compactInducedSubgroupEqEquiv_eval {S H : Subgroup Q} (hSH : S = H)
    (ρA : Representation ℂ S V) (ρB : Representation ℂ H V)
    (hρ : ∀ (x : Q) (hS : x ∈ S) (hH : x ∈ H), ρA ⟨x, hS⟩ = ρB ⟨x, hH⟩)
    (F : CompactFunctions S ρA) (g : Q) :
    eval H ρB (compactInducedSubgroupEqEquiv hSH ρA ρB hρ F).val g =
      eval S ρA F.val g := by
  subst hSH
  obtain rfl : ρA = ρB := MonoidHom.ext fun x => hρ x.1 x.2 x.2
  rfl

/-- The subgroup-equality transport commutes with compact induction of
intertwining maps having the same underlying linear map. -/
theorem compactInducedSubgroupEqEquiv_map {S H : Subgroup Q} (hSH : S = H)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρA : Representation ℂ S V) (ρB : Representation ℂ H V)
    (ρA' : Representation ℂ S W) (ρB' : Representation ℂ H W)
    (hρ : ∀ (x : Q) (hS : x ∈ S) (hH : x ∈ H), ρA ⟨x, hS⟩ = ρB ⟨x, hH⟩)
    (hρ' : ∀ (x : Q) (hS : x ∈ S) (hH : x ∈ H), ρA' ⟨x, hS⟩ = ρB' ⟨x, hH⟩)
    (TA : ρA.IntertwiningMap ρA') (TB : ρB.IntertwiningMap ρB')
    (hT : TA.toLinearMap = TB.toLinearMap) (F : CompactFunctions S ρA) :
    compactInducedSubgroupEqEquiv hSH ρA' ρB' hρ' (compactInducedMap S TA F) =
      compactInducedMap H TB (compactInducedSubgroupEqEquiv hSH ρA ρB hρ F) := by
  subst hSH
  obtain rfl : ρA = ρB := MonoidHom.ext fun x => hρ x.1 x.2 x.2
  obtain rfl : ρA' = ρB' := MonoidHom.ext fun x => hρ' x.1 x.2 x.2
  obtain rfl : TA = TB := Representation.IntertwiningMap.ext hT
  rfl

end SubgroupTransport

section NormalCoinvariants

variable {G : Type u} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {Q L V : Subgroup G}
  (dQ : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The kernel of the actual Levi projection is the radical, read inside `Q`. -/
theorem IsSemidirectDecomposition.ker_projection_eq :
    dQ.projection.ker = V.subgroupOf Q := by
  ext q
  exact dQ.projection_eq_one_iff q

/-- Mathlib's native normal coinvariants of the kernel of the Levi projection,
restricted to the Levi and twisted by the inverse half character of `V`. -/
def normalParabolicCoinvariantsFunctor : Rep.{uV} ℂ Q ⥤ Rep.{uV} ℂ L where
  obj π := Rep.of (twist (HaarModulus.closedInverseHalfCharacter V hV L dQ.levi_le_normalizer)
    ((π.ρ.toCoinvariants dQ.projection.ker).comp (Subgroup.inclusion dQ.levi_le)))
  map T := Rep.ofHom (twistIntertwining
    (HaarModulus.closedInverseHalfCharacter V hV L dQ.levi_le_normalizer)
    (restrictAlongMap (Subgroup.inclusion dQ.levi_le)
      (normalCoinvariantsMap dQ.projection.ker T.hom)))
  map_id π := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    induction z using Representation.Coinvariants.induction_on
    rfl
  map_comp T T' := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    induction z using Representation.Coinvariants.induction_on
    rfl

/-- The character-one localization of `V.subgroupOf Q`, used by
`parabolicCoinvariantsFunctor`, is naturally Mathlib's normal coinvariant
quotient of the kernel of the Levi projection. -/
def parabolicCoinvariantsNormalIso :
    parabolicCoinvariantsFunctor.{u, uV} dQ hV ≅ normalParabolicCoinvariantsFunctor dQ hV := by
  letI : (V.subgroupOf Q).Normal := dQ.normal
  have hTop : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (V.subgroupOf Q : Set Q) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  refine NatIso.ofComponents (fun π => Rep.mkIso (twistEquiv
    (HaarModulus.closedInverseHalfCharacter V hV L dQ.levi_le_normalizer)
    ((restrictAlongEquiv (leviToTopParabolic dQ)
      (Jacquet.Localization.Coefficient.normalCoinvariantsLocalizationEquiv
        (V.subgroupOf Q) ⊤ hTop π.ρ).symm).trans
      (restrictAlongEquiv (Subgroup.inclusion dQ.levi_le)
        (normalCoinvariantsCongr π.ρ (dQ.ker_projection_eq).symm))))) ?_
  intro π π' T
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective π.ρ (V.subgroupOf Q) 1 z
  change normalCoinvariantsCongr π'.ρ (dQ.ker_projection_eq).symm
      (Representation.Coinvariants.mk _ (T.hom x)) =
    normalCoinvariantsMap dQ.projection.ker T.hom
      (normalCoinvariantsCongr π.ρ (dQ.ker_projection_eq).symm
        (Representation.Coinvariants.mk _ x))
  rw [normalCoinvariantsCongr_mk, normalCoinvariantsCongr_mk]
  rfl

end NormalCoinvariants

section OrbitSource

variable {A : Type u} [Group A] [TopologicalSpace A] [LocallyCompactSpace A]
  [NonarchimedeanGroup A] {PI MI UI PJ MJ UJ : Subgroup A}
  (dI : IsSemidirectDecomposition PI MI UI) (dJ : IsSemidirectDecomposition PJ MJ UJ)
  (n : A) (hUI : IsClosed (UI : Set A)) (hUJ : IsClosed (UJ : Set A))

omit [TopologicalSpace A] [LocallyCompactSpace A] [NonarchimedeanGroup A] in
/-- The stabilizer of the orbit of `P_J n⁻¹` under `P_I` is the literal
target-intersection parabolic `P_I ∩ n P_J n⁻¹`, read inside `P_I`. -/
theorem orbitStabilizer_eq_geometricTarget :
    Geometric.orbitStabilizer PJ PI n = (geometricTargetIntersection PI PJ n).subgroupOf PI := by
  ext q
  change n⁻¹ * (q : A) * n⁻¹⁻¹ ∈ PJ ↔ (q : A) ∈ geometricTargetIntersection PI PJ n
  rw [mem_geometricTargetIntersection, inv_inv]
  exact ⟨fun h => ⟨q.2, h⟩, fun h => h.2⟩

local notation "H" => Subgroup.subgroupOf (geometricTargetIntersection PI PJ n) PI
local notation "f" => geometricCoefficientProjection PI PJ MJ UJ dJ n
local notation "χ" => HaarModulus.closedHalfCharacter UJ hUJ MJ dJ.levi_le_normalizer

/-- Compact induction from the literal target-intersection parabolic of the
positive `U_J` half on `M_J` and the coefficient projection `x ↦ pr_J(n⁻¹ x n)`. -/
def geometricCompactInducingFunctor :
    SmoothRep.{0, u, uV} ℂ MJ ⥤ Rep.{max u uV} ℂ PI where
  obj σ := Rep.of (compactInduced H ((twist χ σ.representation).comp f))
  map a := Rep.ofHom (compactInducedMap H (restrictAlongMap f (twistIntertwining χ
    (SmoothRep.hom a))))
  map_id σ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro F
    rfl
  map_comp a b := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro F
    rfl

variable (hprojJ : Continuous dJ.projection)
  (hUJc : Jacquet.Localization.IsLimitOfCompactSubgroups UJ)

include hUJc in
/-- On the orbit stabilizer, the inducing covariance of normalized induction
agrees with the coefficient of `geometricCompactInducingFunctor`: the positive
`U_J` half on `P_J` factors through the Levi projection because `U_J` is
unimodular. -/
theorem orbitPiece_coefficient_eq (σ : SmoothRep.{0, u, uV} ℂ MJ) (x : PI)
    (hS : x ∈ Geometric.orbitStabilizer PJ PI n) (hH : x ∈ H) :
    (((parabolicInducingFunctor dJ hUJ).obj σ).ρ.comp
        (Geometric.stabilizerToInducing PJ PI n)) ⟨x, hS⟩ =
      ((twist χ σ.representation).comp f) ⟨x, hH⟩ := by
  have hδ := isUnimodularModulus_of_isLimitOfCompactSubgroups UJ hUJ hUJc
  have hproj : dJ.projection (Geometric.stabilizerToInducing PJ PI n ⟨x, hS⟩) =
      f ⟨x, hH⟩ := by
    rw [geometricCoefficientProjection_apply]
    apply congrArg dJ.projection
    apply Subtype.ext
    exact Geometric.stabilizerToInducing_apply _ _ _ _
  apply LinearMap.ext
  intro v
  change ((HaarModulus.closedHalfCharacter UJ hUJ PJ dJ.le_normalizer
      (Geometric.stabilizerToInducing PJ PI n ⟨x, hS⟩) : ℂˣ) : ℂ) •
      σ.representation (dJ.projection (Geometric.stabilizerToInducing PJ PI n ⟨x, hS⟩)) v =
    ((χ (f ⟨x, hH⟩) : ℂˣ) : ℂ) • σ.representation (f ⟨x, hH⟩) v
  rw [closedHalfCharacter_eq_comp_projection dJ hUJ hδ, MonoidHom.comp_apply, hproj]

include hUJc in
/-- The parabolic orbit piece of the inducing covariance is naturally compact
induction from the literal target intersection, with the same functions. -/
def orbitPieceInducingIso :
    smoothParabolicInducingFunctor.{u, uV} dJ hUJ hprojJ ⋙
        Geometric.orbitPiece.{0, u, uV} PJ PI n ≅
      geometricCompactInducingFunctor dJ n hUJ :=
  NatIso.ofComponents
    (fun σ => Rep.mkIso (compactInducedSubgroupEqEquiv
      (orbitStabilizer_eq_geometricTarget n) _ _
      (orbitPiece_coefficient_eq dJ n hUJ hUJc σ)))
    (by
      intro σ τ a
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro F
      exact compactInducedSubgroupEqEquiv_map (orbitStabilizer_eq_geometricTarget n) _ _ _ _
        (orbitPiece_coefficient_eq dJ n hUJ hUJc σ) (orbitPiece_coefficient_eq dJ n hUJ hUJc τ)
        _ _ rfl F)

include hUJc in
/-- The Jacquet support grade of an orbit is naturally the normal coinvariants
of compact induction from the literal target intersection. -/
def orbitPieceCoinvariantsIso :
    smoothParabolicInducingFunctor.{u, uV} dJ hUJ hprojJ ⋙
        Geometric.orbitPiece.{0, u, uV} PJ PI n ⋙ parabolicCoinvariantsFunctor dI hUI ≅
      geometricCompactInducingFunctor dJ n hUJ ⋙ normalParabolicCoinvariantsFunctor dI hUI :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (orbitPieceInducingIso dJ n hUJ hprojJ hUJc) _ ≪≫
    Functor.isoWhiskerLeft _ (parabolicCoinvariantsNormalIso dI hUI)

end OrbitSource

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  [T2Space (RationalPoint k G.X)]
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)

/-- The published normalized compact orbit source is, on the nose, normal
coinvariants of compact induction from the literal target intersection. -/
def geometricNormalizedCompactSourceRepIso :
    geometricNormalizedCompactSourceFunctor i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        hPI hMI hMJ hUc hStandard hG hi hν hN hprojI hprojJ ⋙ SmoothRep.toRep ≅
      geometricCompactInducingFunctor.{u, uV} dJ (n : RationalPoint k G.X) hUJ ⋙
        normalParabolicCoinvariantsFunctor dI hUI :=
  NatIso.ofComponents (fun σ => Iso.refl _) (by
    intro σ τ a
    rfl)

end RationalPointFamily

end Langlands.Aubert.General
