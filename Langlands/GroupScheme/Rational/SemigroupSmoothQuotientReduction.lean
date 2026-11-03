import Langlands.GroupScheme.Rational.SemigroupComparisonStatement
import Langlands.GroupScheme.Rational.SmoothTangentWeights
import Langlands.GroupScheme.Lie.SurjectiveDifferentialStatement
import Langlands.GroupScheme.SmoothProducts

/-! # Smooth quotient reduction for actual semigroup subgroup representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- Any representative of a smooth connected closed all-test subgroup has the
same geometric properties as its defining representative. -/
theorem IsSmoothConnectedClosed.representative_properties
    {G H : GroupScheme (Spec (CommRingCat.of k))} {F : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) (j : H ⟶ G) (hj : F.IsRepresentedBy j) :
    IsClosedSubgroup j ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left := by
  obtain ⟨H', j', hj', hc, hs, hconn⟩ := hF
  let e : H ≅ H' := hj.isoOfIsRepresentedBy hj'
  refine ⟨?_, smooth_of_over_iso ((Grp.forget _).mapIso e) hs, ?_⟩
  · rw [← hj.isoOfIsRepresentedBy_hom_comp hj']
    exact hc.iso_comp e
  · exact (Scheme.homeoOfIso
      ((Over.forget _).mapIso ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hconn

section InducedMap

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
    (f : H ⟶ G) (A : AddSubsemigroup (characterLattice S))
    (hmap : (semigroupSubgroup c A).map f ≤ semigroupSubgroup b A)

/-- Postcomposition on the actual semigroup subgroup points whenever
functorial containment has been established. -/
def semigroupPointsMapOfMapLe (T : Over (Spec (CommRingCat.of k))) :
    (semigroupSubgroup c A).carrier T →* (semigroupSubgroup b A).carrier T where
  toFun x := ⟨x.val ≫ f.hom.hom, hmap T ⟨x.val, x.property, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

variable {Hₐ Gₐ : GroupScheme (Spec (CommRingCat.of k))}
    (j : Hₐ ⟶ H) (l : Gₐ ⟶ G)
    (hj : (semigroupSubgroup c A).IsRepresentedBy j)
    (hl : (semigroupSubgroup b A).IsRepresentedBy l)

/-- The actual homomorphism between any two representatives induced by
functorial containment of semigroup subgroup functors. -/
def semigroupHomOfMapLe : Hₐ ⟶ Gₐ :=
  hj.lift hl (semigroupPointsMapOfMapLe c b f A hmap)
    (fun a x => Category.assoc a x.val f.hom.hom)

/-- The induced homomorphism has the prescribed ambient composite. -/
theorem semigroupHomOfMapLe_comp :
    semigroupHomOfMapLe c b f A hmap j l hj hl ≫ l = j ≫ f :=
  hj.lift_comp_eq hl (semigroupPointsMapOfMapLe c b f A hmap)
    (fun a x => Category.assoc a x.val f.hom.hom)
    (fun _ x => (Category.assoc x j.hom.hom f.hom.hom).symm)

/-- Surjectivity on the full selected weight spans yields surjectivity of
the differential of the induced homomorphism. -/
theorem semigroupHomOfMapLe_differential_surjective
    [IsAffineHom Hₐ.X.hom] [IsAffineHom Gₐ.X.hom]
    (hLieH : HasLieImage (semigroupSubgroup c A) (semigroupWeightSpan c A))
    (hLieG : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    (hspan : (semigroupWeightSpan c A).map (Lie.targetMapLinear f k) =
      semigroupWeightSpan b A) :
    Function.Surjective
      (Lie.targetMapLinear (semigroupHomOfMapLe c b f A hmap j l hj hl) k) := by
  have : Mono l.hom.hom := hl.1
  have hrH : semigroupWeightSpan c A = LinearMap.range (Lie.targetMapLinear j k) :=
    hLieH.unique (hasLieImage_of_isRepresentedBy j hj)
  have hrG : semigroupWeightSpan b A = LinearMap.range (Lie.targetMapLinear l k) :=
    hLieG.unique (hasLieImage_of_isRepresentedBy l hl)
  intro X
  have hX : Lie.targetMapLinear l k X ∈
      (semigroupWeightSpan c A).map (Lie.targetMapLinear f k) := by
    rw [hspan, hrG]
    exact ⟨X, rfl⟩
  obtain ⟨Y, hY, hYX⟩ := hX
  rw [hrH] at hY
  obtain ⟨Z, rfl⟩ := hY
  refine ⟨Z, Lie.targetMapLinear_injective l k ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  have hval := congrArg
    (fun V : Additive (lieKernel G k) => V.toMul.val) hYX
  simpa only [lieKernelTargetLinear_val, Category.assoc,
    ← Grp.comp_hom_hom, semigroupHomOfMapLe_comp] using hval

end InducedMap

/-- Semigroup realization and functoriality, together with the general
geometric differential criterion, imply the exact smooth quotient target. -/
theorem semigroupSmoothQuotient_of_realization_functoriality_differential
    (hReal : SemigroupRealizationStatement.{u})
    (hFun : SemigroupFunctorialityStatement.{u})
    (hDiff : Lie.SmoothSurjectiveOfSurjectiveDifferentialStatement.{u}) :
    SemigroupSmoothQuotientStatement.{u} := by
  intro k _ H G hH hG hAffH hAffG S hS c b f hfs _hfurj heq
  let _ := hAffH
  let _ := hAffG
  let _ := hH
  let _ := hG
  intro A Hₐ Gₐ j l hj hl
  have hRH := hReal k H hH hAffH S hS c A
  have hRG := hReal k G hG hAffG S hS b A
  obtain ⟨hjc, hjs, _⟩ := hRH.1.representative_properties j hj
  obtain ⟨hlc, hls, hlconn⟩ := hRG.1.representative_properties l hl
  let _ := hjc.isAffineHom
  let _ := hlc.isAffineHom
  have hmap := hFun k H G hH hG hAffH hAffG S hS c b f heq A
  let p := semigroupHomOfMapLe c b f A hmap j l hj hl
  have hpd : Function.Surjective (Lie.targetMapLinear p k) :=
    semigroupHomOfMapLe_differential_surjective c b f A hmap j l hj hl
      hRH.2.2.1 hRG.2.2.1
      (map_semigroupWeightSpan_eq_of_smooth c b hS f heq hfs A)
  obtain ⟨hps, hpsurj⟩ := hDiff k Hₐ Gₐ hjs hls
    inferInstance inferInstance hlconn p hpd
  exact ⟨p, (semigroupHomOfMapLe_comp c b f A hmap j l hj hl).symm,
    hps, hpsurj⟩

end Langlands.GroupScheme.RelativeRoot
