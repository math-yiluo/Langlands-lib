import Langlands.GroupScheme.IntegralModel.KernelCentralizerReflectionLift
import Langlands.GroupScheme.IntegralModel.KernelCentralizerRootLifting
import Langlands.GroupScheme.IntegralModel.ReflectionCellLifting
import Langlands.GroupScheme.IntegralModel.PrescribedOppositeFactors

/-! # Opposite factors from an actual component quotient -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.KernelCentralizerData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)
    [Mono (M.genericHom i).hom.hom.left]

local notation "b" => (Spec.algebraMap R K)
local notation "b₀" => (residueBaseMap R)
set_option quotPrecheck false in
local notation "iK" => (M.genericHom i :
  ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T).toGrp ⟶ G)
local notation "aK" => (characterLattice.baseChange b T a)
local notation "νK" => (cocharacterLattice.baseChange b T ν)
local notation "χC" => (CommGroupScheme.groupHom ν ≫ D.torus hT)
local notation "χA" => (CommGroupScheme.groupHom ν ≫ i)
local notation "f" => (D.componentHom ≫ D.fullHom)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
local instance : IsAffineHom D.componentGroup.X.hom := D.model.affine
local instance : IsAffine D.componentGroup.X.left :=
  isAffine_of_isAffineHom D.componentGroup.X.hom
local instance : Smooth D.model.group.X.hom := D.componentSmooth
local instance : GeometricallyConnected D.model.specialFibre.X.hom :=
  inferInstanceAs (GeometricallyConnected
    (CategoryTheory.Limits.pullback.snd D.componentGroup.X.hom b₀))
local instance : ConnectedSpace D.model.specialFibre.X.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton D.model.specialFibre.X.hom

variable {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    [IsAffineHom Q.X.hom]
    (q : D.model.specialFibre ⟶ Q) (hQ : IsConnectedReductive Q)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    [ConnectedSpace (kernel q).X.left] (hN : IsUnipotent (kernel q))
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((baseChange (residueBaseMap R)).map (D.torus hT) ≫ q))
    [Mono ((baseChange (residueBaseMap R)).map (D.torus hT) ≫ q).hom.hom.left]
    (e : AutomorphicAction
      (Gm (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))).toGrp Q)
    (he : e.restrict (CommGroupScheme.groupHom
        (characterLattice.baseChange (residueBaseMap R) T a)) =
      AutomorphicAction.conjugation ((baseChange (residueBaseMap R)).map (D.torus hT) ≫ q))

local notation "χq" => (Dynamic.baseChangeCocharacter b₀ χC ≫ q)

include hpos hQ hqs hqsurj hN hi he in
/-- Nonidentity reduction in an actual component quotient makes both
prescribed ambient opposite factors integral. -/
theorem integral_oppositeFactors_of_componentQuotient
    (hroot : HasRelativeRootSystem (T := (CommGroupScheme.baseChange b).obj T) iK)
    (ha : aK ∈ relativeRoots (T := (CommGroupScheme.baseChange b).obj T) iK)
    (y : rationalPoints (Dynamic.Affine.unipotentScheme χC))
    (x : M.integralSections)
    (hyx : rationalPoints.map
      (Dynamic.Affine.unipotentHom χC ≫ f) y = x)
    (hy1 : rationalPoints.map q
      (D.model.reduction (rationalPoints.map (Dynamic.Affine.unipotentHom χC) y)) ≠ 1)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).carrier
        (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair (T := (CommGroupScheme.baseChange b).obj T)
      iK aK (M.integralPointMap x) p) :
    p.1 ∈ M.integralPoints ∧ p.2 ∈ M.integralPoints := by
  let xC : D.model.integralSections :=
    rationalPoints.map (Dynamic.Affine.unipotentHom χC) y
  have hxC : rationalPoints.map f xC = x := by
    exact hyx
  have hyq : rationalPoints.map q (D.model.reduction xC) ∈
      (Dynamic.unipotent χq).carrier (Over.mk (𝟙 _)) := by
    have hrep := (Dynamic.Affine.isRepresentedBy_unipotentHom χC).baseChange b₀
    rw [← Dynamic.unipotent_baseChange] at hrep
    have hyC : D.model.reduction xC ∈
        (Dynamic.unipotent (Dynamic.baseChangeCocharacter b₀ χC)).carrier
          (Over.mk (𝟙 _)) := by
      rw [← hrep.2]
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨baseChangeSectionHom b₀ (Dynamic.Affine.unipotentScheme χC) y, ?_⟩
      exact (baseChangeSectionHom_naturality b₀
        (Dynamic.Affine.unipotentHom χC) y).symm
    exact Dynamic.unipotent_le_comap
      (Dynamic.baseChangeCocharacter b₀ χC) q _ hyC
  have hne : Dynamic.unipotent χq ≠ ⊥ := by
    intro h
    rw [h] at hyq
    exact hy1 (by simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hyq)
  let m := D.model.henselianReflectionCellLift (D.torus hT) hT a ν hpos
    q hQ hqs hqsurj hN hi e he hne
  obtain ⟨c, hc⟩ := m.property.2.2 xC hyq hy1
  have hyqinv : rationalPoints.map q (D.model.reduction xC⁻¹) ∈
      (Dynamic.unipotent χq).carrier (Over.mk (𝟙 _)) := by
    simpa only [map_inv] using Subgroup.inv_mem _ hyq
  have hyinv1 : rationalPoints.map q (D.model.reduction xC⁻¹) ≠ 1 := by
    simpa only [map_inv, inv_ne_one] using hy1
  obtain ⟨d, hd⟩ := m.property.2.2 xC⁻¹ hyqinv hyinv1
  let jA := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χA)
  let rA := Dynamic.Affine.parabolicHom χA
  have hχCA : χC ≫ f = χA := by
    rw [Category.assoc, D.torus_comp_ambient hT]
  have hjA : (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (χC ≫ f))).IsRepresentedBy jA := by
    rw [hχCA]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom _
  have hrA : (Dynamic.parabolic (χC ≫ f)).IsRepresentedBy rA := by
    rw [hχCA]
    exact Dynamic.Affine.isRepresentedBy_parabolicHom _
  obtain ⟨cA, hcA⟩ := Dynamic.exists_oppositeCellPoint_image χC f
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χC))
    (Dynamic.Affine.parabolicHom χC)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    jA rA hjA hrA c
  obtain ⟨dA, hdA⟩ := Dynamic.exists_oppositeCellPoint_image χC f
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χC))
    (Dynamic.Affine.parabolicHom χC)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    jA rA hjA hrA d
  let mA := rationalPoints.map f m.val.1
  have hcA' : cA ≫ SubgroupFunctor.cellMultiplication jA rA = x * mA⁻¹ := by
    rw [hcA, ← Category.assoc, hc]
    change rationalPoints.map f (xC * m.val.1⁻¹) = _
    rw [map_mul, map_inv, hxC]
  have hdA' : dA ≫ SubgroupFunctor.cellMultiplication jA rA = x⁻¹ * mA⁻¹ := by
    rw [hdA, ← Category.assoc, hd]
    change rationalPoints.map f (xC⁻¹ * m.val.1⁻¹) = _
    rw [map_mul, map_inv, map_inv, hxC]
  let n := D.ambientGenericNormalizer hT m.val.1 m.val.2 m.property.1
  have hn : IsRelativeReflection
      (T := (CommGroupScheme.baseChange b).obj T) iK aK (QuotientGroup.mk n) :=
    D.ambientGenericNormalizer_isRelativeReflection hT ha
      m.val.1 m.val.2 m.property.1 m.property.2.1
  have hχ : Dynamic.baseChangeCocharacter b χA ≫ M.genericIso.hom =
      CommGroupScheme.groupHom νK ≫ iK := by
    simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
    rfl
  have hposK : 0 < latticePairing ((CommGroupScheme.baseChange b).obj T) aK νK := by
    simpa only [latticePairing_baseChange] using hpos
  exact M.integral_oppositeFactors_of_cell_lifts
    (T := (CommGroupScheme.baseChange b).obj T)
    iK (hT.baseChange b) hroot aK ha νK hposK χA hχ
    jA rA (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    mA n rfl hn x hx hx1 p hp cA dA hcA' hdA'

/-- Choose actual integral lifts of the same prescribed factors. -/
def componentQuotientOppositeFactorLift
    (hroot : HasRelativeRootSystem (T := (CommGroupScheme.baseChange b).obj T) iK)
    (ha : aK ∈ relativeRoots (T := (CommGroupScheme.baseChange b).obj T) iK)
    (y : rationalPoints (Dynamic.Affine.unipotentScheme χC))
    (x : M.integralSections)
    (hyx : rationalPoints.map
      (Dynamic.Affine.unipotentHom χC ≫ f) y = x)
    (hy1 : rationalPoints.map q
      (D.model.reduction (rationalPoints.map (Dynamic.Affine.unipotentHom χC) y)) ≠ 1)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (S := (CommGroupScheme.baseChange b).obj T) iK aK).carrier
        (Over.mk (𝟙 _)))
    (hx1 : M.integralPointMap x ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair (T := (CommGroupScheme.baseChange b).obj T)
      iK aK (M.integralPointMap x) p) :
    {z : M.integralSections × M.integralSections //
      M.integralPointMap z.1 = p.1 ∧ M.integralPointMap z.2 = p.2} := by
  have h := D.integral_oppositeFactors_of_componentQuotient hT ν hpos
    q hQ hqs hqsurj hN hi e he hroot ha y x hyx hy1 hx hx1 p hp
  exact ⟨(Classical.choose h.1, Classical.choose h.2),
    Classical.choose_spec h.1, Classical.choose_spec h.2⟩

end Langlands.GroupScheme.IntegralModel.KernelCentralizerData
