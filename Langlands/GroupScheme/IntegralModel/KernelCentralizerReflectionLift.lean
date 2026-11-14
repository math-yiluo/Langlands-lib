import Langlands.GroupScheme.IntegralModel.KernelCentralizerTorus
import Langlands.GroupScheme.Torus.HenselianRootNormalizerLifting
import Langlands.GroupScheme.Rational.DynamicReflectionCell
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Rational.KernelCentralizerRelativeReflection
import Langlands.GroupScheme.Rational.CrossTorusKernelCentralizer

/-! # Ambient reflections from an integral kernel-centralizer component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {H G U P V Q : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)
    (j : U ⟶ H) (r : P ⟶ H)
    (hj : (unipotent (oppositeCocharacter χ)).IsRepresentedBy j)
    (hr : (parabolic χ).IsRepresentedBy r)
    (j' : V ⟶ G) (r' : Q ⟶ G)
    (hj' : (unipotent (oppositeCocharacter (χ ≫ f))).IsRepresentedBy j')
    (hr' : (parabolic (χ ≫ f)).IsRepresentedBy r')

include hj hr hj' hr' in
/-- A point of a dynamic opposite cell maps to an actual point of any
representing opposite cell in the target group. -/
theorem exists_oppositeCellPoint_image {X : Over S} (c : X ⟶ U.X ⊗ P.X) :
    ∃ d : X ⟶ V.X ⊗ Q.X,
      d ≫ SubgroupFunctor.cellMultiplication j' r' =
        c ≫ SubgroupFunctor.cellMultiplication j r ≫ f.hom.hom := by
  have hu : (c ≫ fst U.X P.X) ≫ j.hom.hom ∈
      (unipotent (oppositeCocharacter χ)).carrier X := by
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.mpr ⟨c ≫ fst U.X P.X, rfl⟩
  have hv : (c ≫ snd U.X P.X) ≫ r.hom.hom ∈ (parabolic χ).carrier X := by
    rw [← hr.2]
    exact SubgroupFunctor.mem_range.mpr ⟨c ≫ snd U.X P.X, rfl⟩
  have huf : ((c ≫ fst U.X P.X) ≫ j.hom.hom) ≫ f.hom.hom ∈
      (unipotent (oppositeCocharacter (χ ≫ f))).carrier X := by
    have h := unipotent_le_comap (oppositeCocharacter χ) f X hu
    simpa only [SubgroupFunctor.mem_comap, oppositeCocharacter, Category.assoc] using h
  have hvf : ((c ≫ snd U.X P.X) ≫ r.hom.hom) ≫ f.hom.hom ∈
      (parabolic (χ ≫ f)).carrier X :=
    parabolic_le_comap χ f X hv
  rw [← hj'.2] at huf
  rw [← hr'.2] at hvf
  obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp huf
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hvf
  refine ⟨lift u v, ?_⟩
  rw [SubgroupFunctor.lift_cellMultiplication, hu, hv]
  simp only [SubgroupFunctor.cellMultiplication, MonObj.comp_mul,
    MonObj.mul_comp, Category.assoc]

end Dynamic

namespace IntegralModel.KernelCentralizerData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a) (hT : IsSplitTorus T.toGrp)

local notation "b" => (Spec.algebraMap R K)
set_option quotPrecheck false in
local notation "iK" => (M.genericHom i :
  ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T).toGrp ⟶ G)
local notation "aK" => (characterLattice.baseChange b T a)
local notation "f" => (D.componentHom ≫ D.fullHom)

/-- An actual integral component normalizer gives the original model's
generic normalizer, with its specified base-changed torus automorphism. -/
def ambientGenericNormalizer
    (m : rationalPoints D.componentGroup) (σ : T ≅ T)
    (hm : IsNormalizingPoint (D.torus hT) m σ) :
    normalizerPoints (T := (CommGroupScheme.baseChange b).obj T) iK := by
  let n := rationalPoints.map f m
  have hn : IsNormalizingPoint i n σ := by
    simpa only [n, rationalPoints.map_apply, D.torus_comp_ambient hT] using hm.comp_hom f
  have hnK := hn.baseChangeBasePoint b
  refine ⟨M.integralPointMap n,
    ⟨(CommGroupScheme.baseChange b).mapIso σ, ?_⟩⟩
  exact hnK.comp_hom M.genericIso.hom

@[simp]
theorem ambientGenericNormalizer_val
    (m : rationalPoints D.componentGroup) (σ : T ≅ T)
    (hm : IsNormalizingPoint (D.torus hT) m σ) :
    (D.ambientGenericNormalizer hT m σ hm).val =
      M.integralPointMap (rationalPoints.map f m) := rfl

variable [IsAffineHom G.X.hom] [Mono (M.genericHom i).hom.hom.left]

/-- A component normalizer negating the integral character represents the
actual ambient relative reflection on the rational root span. -/
theorem ambientGenericNormalizer_isRelativeReflection
    (ha : aK ∈ relativeRoots iK)
    (m : rationalPoints D.componentGroup) (σ : T ≅ T)
    (hm : IsNormalizingPoint (D.torus hT) m σ)
    (hσ : characterAut σ a = -a) :
    IsRelativeReflection (T := (CommGroupScheme.baseChange b).obj T) iK aK
      (QuotientGroup.mk (D.ambientGenericNormalizer hT m σ hm)) := by
  let n := D.ambientGenericNormalizer hT m σ hm
  have hnorm : IsNormalizingPoint i (rationalPoints.map f m) σ := by
    simpa only [rationalPoints.map_apply, D.torus_comp_ambient hT] using hm.comp_hom f
  have hnormK := rootNormalizer_fieldBaseChange (K := K) i
    (rationalPoints.map f m) σ a hnorm hσ
  have hn : IsNormalizingPoint iK n.val
      ((CommGroupScheme.baseChange b).mapIso σ) :=
    hnormK.1.comp_hom M.genericIso.hom
  have hflip : weylAction (T := (CommGroupScheme.baseChange b).obj T) iK n aK =
      -aK := by
    rw [weylAction_eq (T := (CommGroupScheme.baseChange b).obj T) iK hn aK]
    exact hnormK.2
  have hfull : baseChangeSectionHom b D.componentGroup m ≫
      ((baseChange b).map f).hom.hom ∈
      (RelativeRoot.kernelCentralizer ((baseChange b).map i) aK).carrier
        (Over.mk (𝟙 _)) := by
    rw [← D.fullGenericRepresents.2]
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨baseChangeSectionHom b D.componentGroup m ≫
      ((baseChange b).map D.componentHom).hom.hom, ?_⟩
    simp only [Functor.map_comp, Grp.comp_hom_hom, Category.assoc]
  have hc : n.val ∈ (RelativeRoot.kernelCentralizer iK aK).carrier
      (Over.mk (𝟙 _)) := by
    have h := RelativeRoot.comp_mem_kernelCentralizer_of_transport
      (i := (baseChange b).map i) (j := iK)
      (Iso.refl ((CommGroupScheme.baseChange b).obj T)) M.genericIso.hom
      (by change iK = (𝟙 _) ≫ iK; exact (Category.id_comp _).symm) aK hfull
    simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp,
      ← baseChangeSectionHom_naturality, n, ambientGenericNormalizer_val,
      IntegralModel.integralPointMap, MonoidHom.comp_apply, rationalPoints.map_apply] using h
  exact IsSplitTorus.isRelativeReflection_of_mem_kernelCentralizer
    (T := (CommGroupScheme.baseChange b).obj T)
    iK (hT.baseChange b) aK ha n hflip hc

end IntegralModel.KernelCentralizerData
end Langlands.GroupScheme
