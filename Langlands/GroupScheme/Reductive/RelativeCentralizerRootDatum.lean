import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers

/-! # Full coordinate root data for relative cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra

section Field

variable {k : Type u} [Field k] {I J : Type u} [Fintype I]
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom Z.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsRootDatumOf i (CoordinateRootDatum.fieldRealization k P))
  (v : I → ℤ) (z : Z ⟶ G)
  (hrep : (Dynamic.centralizer
    (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v) ≫ i)).IsRepresentedBy z)
  (t : splitTorus (Spec (CommRingCat.of k)) I ⟶ Z) (ht : t ≫ z = i)

include hP hrep ht in
/-- The coordinate restriction has the actual full root datum of the supplied
cocharacter centralizer over a field, with all central lattice directions kept. -/
theorem IsRootDatumOf.coordinateCentralizer :
    IsRootDatumOf t (CoordinateRootDatum.fieldRealization k (Langlands.LinearAlgebra.orthogonalRootPairing P v)) := by
  let ν := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I v
  have ht' : t = Dynamic.torusFactor (T := splitTorus.commGroupScheme _ I)
      i (CommGroupScheme.groupHom ν) hrep := by
    apply Grp.hom_ext
    have : Mono z.hom.hom := hrep.1
    apply (cancel_mono z.hom.hom).1
    change (t ≫ z).hom.hom =
      (Dynamic.torusFactor (T := splitTorus.commGroupScheme _ I) i (CommGroupScheme.groupHom ν) hrep ≫ z).hom.hom
    rw [ht, Dynamic.torusFactor_comp]
  have hroots : roots t = {α | α ∈ roots i ∧
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) α ν = 0} := by
    rw [ht']
    ext α
    exact Dynamic.mem_roots_torusFactor_iff (T := splitTorus.commGroupScheme _ I) i ν hrep α
  have hzero (a : orthogonalIndices P v) :
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        ((CoordinateRootDatum.fieldRealization k P).root a.val) ν = 0 := by
    rw [← hP.1, CoordinateRootDatum.fieldRealization_root]
    exact (CoordinateRootDatum.fieldRealization_pairing k P (P.root a.val) v).trans a.property
  refine ⟨hP.1, ?_, ?_⟩
  · rw [hroots]
    ext α
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨hP.2.1 ▸ ⟨a.val, rfl⟩, ?_⟩
      exact hzero a
    · rintro ⟨hα, hαν⟩
      rw [← hP.2.1] at hα
      obtain ⟨a, rfl⟩ := hα
      have ha : a ∈ orthogonalIndices P v := by
        change P.toLinearMap (P.root a) v = 0
        rw [← CoordinateRootDatum.fieldRealization_pairing k P (P.root a) v, hP.1]
        simpa only [CoordinateRootDatum.fieldRealization_root, ν] using hαν
      exact ⟨⟨a, ha⟩, rfl⟩
  · intro a
    obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 a.val
    have hfix := LeviGluing.cocharacter_comp_eq_of_reflection hP hσ (hzero a)
    have hmem := LeviGluing.constantPoint_mem_centralizer hn hfix
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    rw [constantPoint_self, ← hrep.2] at hmem
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hmem
    have : Mono z.hom.hom := hrep.1
    refine ⟨m, σ, ?_, hσ⟩
    apply IsNormalizingPoint.of_comp z
    rw [ht, hm]
    exact hn

end Field

section Relative

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (v : I → ℤ)

include hP in
/-- The full orthogonal coordinate root datum is the actual fibrewise root
datum of the supplied relative cocharacter centralizer over an arbitrary ring. -/
theorem IsFibrewiseRootDatumOf.coordinateCentralizer :
    IsFibrewiseRootDatumOf I
      (splitTorus.RelativeCocharacterCentralizer.groupScheme I G i v)
      (splitTorus.RelativeCocharacterCentralizer.torusHom I G i v)
      (Langlands.LinearAlgebra.orthogonalRootPairing P v) := by
  classical
  letI : Finite J := hP.finite
  letI : P.IsReduced := hP.isReduced
  refine ⟨inferInstance, ⟨fun a b h => ?_⟩, ?_⟩
  · exact RootPairing.IsReduced.eq_or_eq_neg (P := P) a.val b.val h
  · intro k _ _
    let δ := algebraBaseMap R k
    let L := splitTorus.RelativeCocharacterCentralizer.groupScheme I G i v
    let z := splitTorus.RelativeCocharacterCentralizer.inclusion I G i v
    let t := splitTorus.RelativeCocharacterCentralizer.torusHom I G i v
    let GA := (baseChange δ).obj G
    let LA := (baseChange δ).obj L
    let zA := (baseChange δ).map z
    let iA := splitTorus.baseChangeHom (K := k) G I i
    let tA := splitTorus.baseChangeHom (K := k) L I t
    letI : IsAffineHom GA.X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom δ))
    letI : IsAffineHom LA.X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd L.X.hom δ))
    letI : LocallyOfFinitePresentation GA.X.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd G.X.hom δ))
    have hrep : (Dynamic.centralizer
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v) ≫ iA)).IsRepresentedBy zA :=
      splitTorus.RelativeCocharacterCentralizer.isRepresentedBy_baseChangeInclusion I G i v δ
    have htA : tA ≫ zA = iA := by
      change ((splitTorus.baseChangeIso δ I).inv ≫ (baseChange δ).map t) ≫
        (baseChange δ).map z = _
      rw [Category.assoc, ← Functor.map_comp]
      change (splitTorus.baseChangeIso δ I).inv ≫
        (baseChange δ).map (splitTorus.RelativeCocharacterCentralizer.torusHom I G i v ≫
          splitTorus.RelativeCocharacterCentralizer.inclusion I G i v) = _
      rw [splitTorus.RelativeCocharacterCentralizer.torusHom_comp]
      rfl
    exact (hP.field k).coordinateCentralizer v zA hrep tA htA

/-- An explicit full coordinate root datum with its actual fibrewise
centralizer certificate, retaining the entire character and cocharacter lattices. -/
def centralizerRootDatumData :
    {Q : RootDatum (orthogonalIndices P v) (I → ℤ) (I → ℤ) //
      IsFibrewiseRootDatumOf I
        (splitTorus.RelativeCocharacterCentralizer.groupScheme I G i v)
        (splitTorus.RelativeCocharacterCentralizer.torusHom I G i v) Q} :=
  ⟨Langlands.LinearAlgebra.orthogonalRootPairing P v, hP.coordinateCentralizer v⟩

end Relative

end Langlands.GroupScheme
