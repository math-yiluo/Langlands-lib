import Langlands.GroupScheme.Rational.TorusVectorExtensionSplit
import Langlands.GroupScheme.Rational.SplitSeriesBaseChange
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.GroupScheme.Descent.ComponentCoverLifts
import Langlands.GroupScheme.Descent.FpqcHomDescent

/-! # Unique torus-valued homomorphisms and descent of retractions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusVectorExtension

open RelativeRoot

variable {k : Type u} [Field k]

/-- A torus-valued homomorphism is determined on the kernel of a unipotent quotient. -/
theorem hom_ext_of_unipotent_quotient
    {E Z Q T : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom Q.X.hom]
    (z : Z ⟶ E) [Mono z.hom.hom]
    (p : E ⟶ Q) [QuasiCompact p.hom.hom.left]
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p)
    (hQ : IsUnipotent Q) (hT : IsTorus T)
    (f g : E ⟶ T) (hfg : z ≫ f = z ≫ g) : f = g := by
  let : IsCommMonObj T.X := hT.isCommMonObj
  let : Flat p.hom.hom.left := hq.1
  let : Surjective p.hom.hom.left := hq.2.1
  have hz : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨inferInstance, rfl⟩
  let e := hq.kernelIso hz
  have he : e.hom ≫ kernelι p = z := hq.kernelIso_hom_comp hz
  have hkill : kernelι p ≫ (f / g) = 0 := by
    apply (cancel_epi e.hom).mp
    rw [comp_zero, ← Category.assoc]
    rw [he]
    change z ≫ (f / g) = 1
    rw [GrpObj.comp_div, hfg, div_self']
  let d := FpqcHomDescent.hom p (f / g) hkill
  have hd : d = 0 := hQ.hom_eq_zero_of_isTorus hT d
  have hh : f / g = 1 := by
    calc
      f / g = p ≫ d := (FpqcHomDescent.fac p (f / g) hkill).symm
      _ = 0 := by rw [hd, comp_zero]
      _ = 1 := rfl
  exact div_eq_one.mp hh

/-- Unipotence after an arbitrary map of field spectra. -/
theorem unipotent_baseChange {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom Q.X.hom]
    (hQ : IsUnipotent Q) : IsUnipotent ((baseChange b).obj Q) := by
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    using hQ.baseChange (K := K)

/-- The torus predicate after an arbitrary map of field spectra. -/
theorem torus_baseChange {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    IsTorus ((baseChange b).obj T) := by
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    using hT.baseChange (K := K)

open Descent in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Uniqueness on field components forces a torus retraction to respect descent. -/
theorem compatible_retraction_onFieldComponents
    {B : Scheme.{u}} {b : Spec (CommRingCat.of k) ⟶ B}
    {E Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsAffineHom Q.X.hom]
    (z : Z ⟶ E) [Mono z.hom.hom] (p : E ⟶ Q)
    (hq : IsFppfQuotient (SubgroupFunctor.range z) p)
    (hQ : IsUnipotent Q) (hZ : IsTorus Z)
    {D : Datum b Z} {F : Datum b E} (hz : Compatible D F z)
    (a : E ⟶ Z) (ha : z ≫ a = 𝟙 Z)
    {I : Type} [Finite I] {L : I → Type u} [∀ i, Field (L i)]
    (r : ∀ i, Spec (CommRingCat.of (L i)) ⟶ Overlap b)
    [IsIso (Sigma.desc r)] : Compatible F D a := by
  apply FiniteComponents.pullHom_ext r
  intro i
  let f := r i ≫ fst b
  let g := r i ≫ snd b
  let eZ := pullIso (r i) rfl rfl D.overlap
  let eE := pullIso (r i) rfl rfl F.overlap
  have hz' : (baseChange f).map z ≫ eE.hom = eZ.hom ≫ (baseChange g).map z := by
    have h := congrArg (pullHom (r i) rfl rfl) hz
    simpa only [f, g, eZ, eE, pullHom_comp (r i) rfl rfl rfl,
      pullHom_map, pullIso_hom] using h
  have haf : (baseChange f).map z ≫ (baseChange f).map a = 𝟙 _ := by
    rw [← Functor.map_comp, ha, CategoryTheory.Functor.map_id]
  have hag : (baseChange g).map z ≫ (baseChange g).map a = 𝟙 _ := by
    rw [← Functor.map_comp, ha, CategoryTheory.Functor.map_id]
  have hqf : IsFppfQuotient (SubgroupFunctor.range ((baseChange f).map z))
      ((baseChange f).map p) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange f
  have : IsAffineHom ((baseChange f).obj Q).X.hom := inferInstanceAs
    (IsAffineHom (pullback.snd Q.X.hom f))
  have : Mono ((baseChange f).map z).hom.hom := by
    change Mono ((Over.pullback f).map z.hom.hom)
    infer_instance
  have : IsAffineHom ((baseChange f).obj E).X.hom := inferInstanceAs
    (IsAffineHom (pullback.snd E.X.hom f))
  have : QuasiCompact ((baseChange f).map p).hom.hom.left := by
    have : IsAffine ((baseChange f).obj E).X.left :=
      isAffine_of_isAffineHom ((baseChange f).obj E).X.hom
    have : IsAffine ((baseChange f).obj Q).X.left :=
      isAffine_of_isAffineHom ((baseChange f).obj Q).X.hom
    infer_instance
  rw [pullHom_comp (r i) rfl rfl rfl, pullHom_comp (r i) rfl rfl rfl,
    pullHom_map, pullHom_map]
  apply hom_ext_of_unipotent_quotient ((baseChange f).map z)
    ((baseChange f).map p) hqf (unipotent_baseChange f hQ) (torus_baseChange g hZ)
  change (baseChange f).map z ≫ ((baseChange f).map a ≫ eZ.hom) =
    (baseChange f).map z ≫ (eE.hom ≫ (baseChange g).map a)
  rw [← Category.assoc, haf, Category.id_comp, ← Category.assoc, hz',
    Category.assoc, hag, Category.comp_id]

open Descent in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A central torus with vector quotient admits a retraction over the original field. -/
theorem exists_retraction_of_vector_quotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] {n : ℕ}
    (hZ : IsTorus Z) (hV : IsVectorGroupOfDimension Q n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    ∃ r : E ⟶ Z, z ≫ r = 𝟙 Z := by
  classical
  obtain ⟨L, hL, aL, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k Z hZ
  let : Field L := hL
  let : Algebra k L := aL
  let : FiniteDimensional k L := hfin
  let : IsGalois k L := hgal
  let b := fieldMap k L
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  have : IsAffineHom ((baseChange b).obj E).X.hom := inferInstanceAs
    (IsAffineHom (pullback.snd E.X.hom b))
  have : IsAffine ((baseChange b).obj E).X.left :=
    isAffine_of_isAffineHom ((baseChange b).obj E).X.hom
  have hVL : IsVectorGroupOfDimension ((baseChange b).obj Q) n := hV.baseChange L
  have : IsAffineHom ((baseChange b).obj Q).X.hom := hVL.isAffineHom
  have hzL := hz.baseChange b
  have : IsClosedImmersion ((baseChange b).map z).hom.hom.left := hzL
  have : Mono ((baseChange b).map z).hom.hom := Over.mono_of_mono_left _
  have hqL : IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map z))
      ((baseChange b).map p) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  obtain ⟨J, hJ, ⟨eZ⟩⟩ := hsplit
  let : Finite J := hJ
  obtain ⟨a, ha⟩ := CentralExtensionHopfSpec.exists_retraction_of_split_vector_quotient
    eZ hVL.iso ((baseChange b).map z) hzL (hc.baseChange b) ((baseChange b).map p) hqL
  have hcompat : Compatible (canonicalDatum b E) (canonicalDatum b Z) a :=
    compatible_retraction_onFieldComponents ((baseChange b).map z)
      ((baseChange b).map p) hqL hVL.isUnipotent (hZ.baseChange (K := L))
      (canonicalDatum_compatible b z) a ha (finiteGaloisComponent k L)
  let r := Descent.FpqcHomDescent.hom b a hcompat
  refine ⟨r, ?_⟩
  apply (baseChange b).map_injective
  rw [Functor.map_comp, CategoryTheory.Functor.map_id]
  change (baseChange b).map z ≫ (baseChange b).map
    (Descent.FpqcHomDescent.hom b a hcompat) = 𝟙 _
  rw [Descent.FpqcHomDescent.baseChange_hom, ha]

/-- A chosen actual retraction for a central torus with vector quotient. -/
def retractionOfVectorQuotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] {n : ℕ}
    (hZ : IsTorus Z) (hV : IsVectorGroupOfDimension Q n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) : E ⟶ Z :=
  Classical.choose (exists_retraction_of_vector_quotient hZ hV z hz hc p hq)

@[reassoc]
theorem comp_retractionOfVectorQuotient
    {E Z Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] {n : ℕ}
    (hZ : IsTorus Z) (hV : IsVectorGroupOfDimension Q n)
    (z : Z ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p) :
    z ≫ retractionOfVectorQuotient hZ hV z hz hc p hq = 𝟙 Z :=
  Classical.choose_spec (exists_retraction_of_vector_quotient hZ hV z hz hc p hq)

end Langlands.GroupScheme.TorusVectorExtension
