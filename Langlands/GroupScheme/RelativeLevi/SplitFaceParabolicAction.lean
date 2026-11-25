import Langlands.GroupScheme.RelativeUnipotent.RootWeightAmbientIntrinsic
import Langlands.GroupScheme.Rational.CyclicConjugationNormality
import Langlands.GroupScheme.RelativeLevi.SplitFaceCocharacterRealization

/-! # Full original parabolic actions on canonical face-weight terms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
  (χ : (Gm S).toGrp ⟶ G) (F : SubgroupFunctor G)

/-- Normalization by the contracting group and centralizer implies
normalization by the full actual parabolic via its limit decomposition. -/
theorem isNormalizedBy_parabolic_of_unipotent_centralizer
    (hU : F.IsNormalizedBy (unipotent χ)) (hZ : F.IsNormalizedBy (centralizer χ)) :
    F.IsNormalizedBy (parabolic χ) := by
  intro T z x hz hx
  let p : (parabolic χ).carrier T := ⟨z, hz⟩
  have hc := hU T (z * (limit χ p)⁻¹) ((limit χ p) * x * (limit χ p)⁻¹)
    (mul_inv_limit_mem_unipotent χ p) (hZ T _ x (limit_mem_centralizer χ p) hx)
  convert hc using 1 <;> group

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Corepresented AffineCorepresentation

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))} [IsSeparated G.X.hom]
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)
  {B : CommAlgCat.{u} (CommRingCat.of R)}
  (ψ : (algSpec (CommRingCat.of R)).obj (op B) ≅ G.X)
  (hj : IsClosedSubgroup j) (v : I → ℤ) (q : ℕ) (hq : 0 < q)
  (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)
  (hrep : (Dynamic.unipotent (AffineRegularBorel.cocharacter t v)).IsRepresentedBy
    (W.ambientInclusion j 0))

include hrep in
/-- Actual contracting points normalize every ambient root-weight term. -/
theorem range_ambientInclusion_isNormalizedBy_unipotent (d : ℕ) :
    (SubgroupFunctor.range (W.ambientInclusion j d)).IsNormalizedBy
      (Dynamic.unipotent (AffineRegularBorel.cocharacter t v)) := by
  intro T z x hz hx
  rw [← hrep.2] at hz
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hx' : x ≫ (W.inclusion d).hom.hom ∈ (W.subgroup d).carrier T := by
    rw [← (W.isRepresentedBy_inclusion d).2]
    exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  have hc := W.isNormal_subgroup d T (z ≫ (W.inclusion 0).hom.hom)
    (x ≫ (W.inclusion d).hom.hom) (Subgroup.mem_top _) hx'
  rw [← (W.isRepresentedBy_inclusion d).2] at hc
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hc
  refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
  change y ≫ (W.inclusion d ≫ j).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, hy, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  rfl

include hroot hu ψ hj hq hw hrep in
/-- Realized face weights give full actual parabolic normalization, with the
original root weights and all scheme tests retained. -/
theorem range_ambientInclusion_isNormalizedBy_parabolic (d : ℕ) :
    (SubgroupFunctor.range (W.ambientInclusion j d)).IsNormalizedBy
      (Dynamic.parabolic (AffineRegularBorel.cocharacter t v)) := by
  apply Dynamic.isNormalizedBy_parabolic_of_unipotent_centralizer
  · exact W.range_ambientInclusion_isNormalizedBy_unipotent j v hrep d
  · rw [W.range_ambientInclusion_eq_cutoff j hroot hu ψ hj v q hq hw hrep d]
    exact cyclicConjugationCutoff_isNormalizedBy_centralizer ψ _ _

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

include hG hmax hP hfam in
/-- Every original unscaled face-weight term is normalized by the ORIGINAL
actual parabolic on every scheme test. -/
theorem range_inclusion_isNormalizedBy_originalParabolic (d : ℕ) :
    (SubgroupFunctor.range (C.weights.ambientInclusion
      (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)) d)).IsNormalizedBy
        (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)) := by
  obtain ⟨B, ⟨ψ⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let : Mono j.hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hw (k : Fin C.chart.dimension) :
      coPairing (P.root (C.index k)) C.faceCocharacter =
        C.faceMultiplier * C.weights.weight k := by
    rw [C.facePairing, C.weight_eq]
  have he := C.weights.range_ambientInclusion_isNormalizedBy_parabolic j C.root_comp
    (fun a T s x => (hfam a).equivariant T s x) ψ
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _) C.faceCocharacter
    C.faceMultiplier C.faceMultiplier_pos hw
    (C.isRepresentedBy_faceCocharacter hG hmax hP hfam) d
  rwa [C.parabolic_faceCocharacter hG hmax hP hfam] at he

/-- The full original actual parabolic acts on every represented unscaled
face-weight term, compatibly with its actual ambient inclusion. -/
def originalParabolicAction (d : ℕ) :
    AutomorphicAction (AffineRegularBorel.borel i wt) (C.weights.groupScheme d) := by
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let f := C.weights.ambientInclusion j d
  let b := AutomorphicAction.conjugation (AffineRegularBorel.inclusion i wt)
  have hmono : Mono f.hom.hom := by
    let : Mono j.hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
    let : Mono (C.weights.inclusion d).hom.hom := (C.weights.isRepresentedBy_inclusion d).1
    change Mono ((C.weights.inclusion d).hom.hom ≫ j.hom.hom)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hs : b.IsStable (SubgroupFunctor.range f) := by
    intro T p x hx
    have hp : p ≫ (AffineRegularBorel.inclusion i wt).hom.hom ∈
        (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).carrier T := by
      rw [← (Dynamic.Affine.isRepresentedBy_parabolicHom _).2]
      exact SubgroupFunctor.mem_range.mpr ⟨p, rfl⟩
    dsimp only [b]
    rw [AutomorphicAction.conjugation_act]
    exact C.range_inclusion_isNormalizedBy_originalParabolic hG hmax hP hfam d T _ x hp hx
  exact b.onRepresentedSubgroup f ⟨hmono, rfl⟩ hs

end Langlands.GroupScheme.SplitParabolicFaceChart
