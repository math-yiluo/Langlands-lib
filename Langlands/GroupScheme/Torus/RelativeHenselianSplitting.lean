import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitDescent
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.RingTheory.Etale.Field

/-! # Field and strictly Henselian comparisons for relative tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeTorus

/-- A relative torus is split over a Henselian local ring whenever a field
quotient of the ring is separably closed. -/
theorem IsTorus.isSplitTorus_of_henselian
    {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [IsSepClosed k]
    (hk : Function.Surjective (algebraMap R k))
    {T : GroupScheme (Spec (CommRingCat.of R))} (hT : IsTorus T) :
    IsSplitTorus T := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  let c := Spec.map (CommRingCat.ofHom (algebraMap R k))
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (c default)
  let : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨b, hb, -⟩ :=
    Scheme.exists_fac_of_etale_of_isSepClosed (𝒰.f i) c y hy
  obtain ⟨σ, hσ, -⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk (𝒰.f i) b hb
  exact (h𝒰 i).of_baseChange_of_section (𝒰.f i) σ hσ

end RelativeTorus

/-- Finite Galois splitting identifies field tori with relative tori. -/
theorem IsTorus.relativeTorus {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    RelativeTorus.IsTorus T := by
  obtain ⟨K, hK, aK, hfin, hgal, hs⟩ := torusFiniteGaloisSplitting k T hT
  let : Field K := hK
  let : Algebra k K := aK
  let : FiniteDimensional k K := hfin
  let : IsGalois k K := hgal
  let c := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hc : Etale c := by
    let : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
    let : Algebra.FinitePresentation k K :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale k K := {}
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hsurj : Surjective c := TorusExistence.surjective_algebraBaseMap K
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of k)) :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => Spec (CommRingCat.of K)) (fun _ => c)
      (fun x => by obtain ⟨y, hy⟩ := hsurj.surj x; exact ⟨PUnit.unit, y, hy⟩)
      (fun _ => hc)
  exact ⟨𝒰, fun _ => hs⟩

/-- The two torus predicates agree over fields. -/
theorem relativeTorus_iff_isTorus {k : Type u} [Field k]
    (T : GroupScheme (Spec (CommRingCat.of k))) :
    RelativeTorus.IsTorus T ↔ IsTorus T :=
  ⟨RelativeTorus.IsTorus.isTorus, IsTorus.relativeTorus⟩

/-- An actual finite split-torus presentation of a group scheme. -/
structure RelativeTorus.SplittingData {S : Scheme.{u}} (T : GroupScheme S) where
  index : Type u
  finite : Finite index
  iso : T ≅ @splitTorus S index finite

attribute [instance] RelativeTorus.SplittingData.finite

/-- Choose an actual splitting of a relative torus over a Henselian local ring
with a separably closed field quotient. -/
def RelativeTorus.henselianSplitting
    {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] [IsSepClosed k]
    (hk : Function.Surjective (algebraMap R k))
    {T : GroupScheme (Spec (CommRingCat.of R))} (hT : RelativeTorus.IsTorus T) :
    RelativeTorus.SplittingData T :=
  let hs := hT.isSplitTorus_of_henselian hk
  ⟨hs.choose, hs.choose_spec.choose, hs.choose_spec.choose_spec.some⟩

end Langlands.GroupScheme
