import Langlands.GroupScheme.Rational.DynamicReflectionCell
import Langlands.GroupScheme.Torus.HenselianRootNormalizerLifting
import Langlands.GroupScheme.IntegralModel.UnipotentQuotientCell

/-! # Integral translates into a dynamic opposite cell -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

/-- For a torus cocharacter, the opposite dynamic cocharacter is its
negative in the actual cocharacter lattice. -/
theorem oppositeCocharacter_torus {S : Scheme.{u}} {T : CommGroupScheme S}
    {G : GroupScheme S} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) =
      CommGroupScheme.groupHom (-ν) ≫ i := by
  rw [oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom (Gm.powerHom S (-1) ≫ ν) ≫ i = _
  have hν : Gm.powerHom S (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [hν]

end Dynamic

namespace IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [HenselianLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [PerfectField (IsLocalRing.ResidueField A)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of A))}
    (i : T.toGrp ⟶ M.group) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν)
    {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    [IsAffineHom Q.X.hom]
    (q : M.specialFibre ⟶ Q) (hQ : IsConnectedReductive Q)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    [ConnectedSpace (kernel q).X.left] (hN : IsUnipotent (kernel q))
    (hi : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap A)).obj T)
      ((baseChange (residueBaseMap A)).map i ≫ q))
    [Mono ((baseChange (residueBaseMap A)).map i ≫ q).hom.hom.left]
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))).toGrp Q)
    (he : e.restrict (CommGroupScheme.groupHom
        (characterLattice.baseChange (residueBaseMap A) T a)) =
      AutomorphicAction.conjugation ((baseChange (residueBaseMap A)).map i ≫ q))

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
local instance : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom

local notation "χ" => (CommGroupScheme.groupHom ν ≫ i)
local notation "χq" => (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q)

/-- One integral character-negating normalizer puts every integral section
with nonidentity positive quotient reduction into an actual integral
opposite-unipotent/parabolic cell after right translation. -/
def henselianReflectionCellLift
    (hne : Dynamic.unipotent χq ≠ ⊥) :
    {m : M.integralSections × (T ≅ T) //
      IsNormalizingPoint i m.1 m.2 ∧ characterAut m.2 a = -a ∧
        ∀ (x : M.integralSections),
          rationalPoints.map q (M.reduction x) ∈
            (Dynamic.unipotent χq).carrier (Over.mk (𝟙 _)) →
          rationalPoints.map q (M.reduction x) ≠ 1 →
          ∃ c : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
              (Dynamic.Affine.unipotentScheme (Dynamic.oppositeCocharacter χ)).X ⊗
                (Dynamic.Affine.parabolicScheme χ).X,
            c ≫ SubgroupFunctor.cellMultiplication
              (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ))
              (Dynamic.Affine.parabolicHom χ) = x * m.1⁻¹} := by
  let b := residueBaseMap A
  let i₀ : ((CommGroupScheme.baseChange b).obj T).toGrp ⟶ M.specialFibre :=
    (baseChange b).map i
  let a₀ := characterLattice.baseChange b T a
  let ν₀ := cocharacterLattice.baseChange b T ν
  have hχq : χq = CommGroupScheme.groupHom ν₀ ≫ (i₀ ≫ q) := by
    simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
    rfl
  have hp₀ : 0 < latticePairing ((CommGroupScheme.baseChange b).obj T) a₀ ν₀ := by
    simpa only [a₀, ν₀, latticePairing_baseChange] using hpos
  have hne₀ : Dynamic.unipotent
      (CommGroupScheme.groupHom ν₀ ≫ (i₀ ≫ q)) ≠ ⊥ := by
    rwa [← hχq]
  let : Smooth Q.X.hom := hQ.smooth
  let : ConnectedSpace Q.X.left := hQ.connectedSpace
  let : Smooth M.specialFibre.X.hom :=
    inferInstanceAs (Smooth (pullback.snd M.group.X.hom b))
  let : IsAffineHom M.specialFibre.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom b))
  let : Smooth q.hom.hom.left := hqs
  let : Smooth (kernel q).X.hom := SubgroupFunctor.KernelCell.smooth_kernel q
  have hk : IsClosedSubgroup (kernelι q) :=
    inferInstanceAs (IsClosedImmersion (kernelι q).hom.hom.left)
  have hquot : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q :=
    ⟨inferInstance, hqsurj, inferInstance, rfl⟩
  let m₀ := RelativeRoot.dynamicReflectionCellNormalizerLift (kernelι q) hk hN q hquot
    i₀ (hT.baseChange b).isTorus hQ hi a₀ e he ν₀ hp₀ hne₀
  let m := henselianRootNormalizerLift i hT (inferInstance : Smooth M.group.X.hom)
    (IsLocalRing.residue_surjective (R := A)) a m₀.val.1 m₀.val.2
    m₀.property.1 m₀.property.2.1
  have hrec : M.reduction m.val.1 = m₀.val.1 := m.property.2.1
  refine ⟨m.val, m.property.1, m.property.2.2.2, ?_⟩
  intro x hx hx1
  have hx₀ : rationalPoints.map q (M.reduction x) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν₀ ≫ (i₀ ≫ q))).carrier
        (Over.mk (𝟙 _)) := by
    rwa [← hχq]
  obtain ⟨y, hy, v, hv, hprod⟩ := m₀.property.2.2 _ hx₀ hx1
  have hy' : y ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χq)).carrier
      (Over.mk (𝟙 _)) := by
    rw [hχq, Dynamic.oppositeCocharacter_torus]
    exact hy
  have hv' : v ∈ (Dynamic.parabolic χq).carrier (Over.mk (𝟙 _)) := by
    rwa [hχq]
  let j := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χq)
  let r := Dynamic.Affine.parabolicHom χq
  have hj := Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χq)
  have hr := Dynamic.Affine.isRepresentedBy_parabolicHom χq
  have hyRange : y ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
    rw [hj.2]
    exact hy'
  have hvRange : v ∈ (SubgroupFunctor.range r).carrier (Over.mk (𝟙 _)) := by
    rw [hr.2]
    exact hv'
  obtain ⟨y₀, hy₀⟩ := SubgroupFunctor.mem_range.mp hyRange
  obtain ⟨v₀, hv₀⟩ := SubgroupFunctor.mem_range.mp hvRange
  have hc : lift y₀ v₀ ≫ SubgroupFunctor.cellMultiplication j r =
      M.reduction (x * m.val.1⁻¹) ≫ q.hom.hom := by
    rw [SubgroupFunctor.lift_cellMultiplication, hy₀, hv₀, ← hprod,
      map_mul, map_inv, hrec]
    simp only [rationalPoints.map_apply, MonObj.mul_comp, GrpObj.inv_comp]
  exact (M.oppositeCell_section_lifts_iff_quotient_reduction χ
    (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ))
    (Dynamic.Affine.parabolicHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    q hqs hqsurj hN j r hj hr (x * m.val.1⁻¹)).mpr ⟨lift y₀ v₀, hc⟩

end IntegralModel
end Langlands.GroupScheme
