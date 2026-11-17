import Langlands.GroupScheme.SmoothDvrGenericAffinenessStatement
import Langlands.CommutativeAlgebra.StrictHenselianDvrExtension
import Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent

/-! # Reduction of smooth DVR affineness to strictly henselian DVRs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The smooth generic-affineness criterion restricted to henselian DVRs with
separably closed residue field, retaining an arbitrary specified fraction field. -/
def StrictHenselianSmoothDvrGenericAffinenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Smooth G.X.hom → QuasiCompact G.X.hom → IsSeparated G.X.hom →
    IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom →
    IsAffineHom G.X.hom

namespace SmoothDvrGenericAffinenessDescent

/-- Affineness of the original generic fibre is preserved by extension to the fraction
field of any faithfully flat domain algebra, on the actual iterated base change. -/
theorem isAffine_generic_baseChange
    {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.FaithfullyFlat R A]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (hη : IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom) :
    IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj G)).X.hom := by
  let L := FractionRing A
  let α : R →+* L := (algebraMap A L).comp (algebraMap R A)
  have hα : Function.Injective α :=
    (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective R A)
  let φ : K →+* L := IsFractionRing.lift hα
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let k := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let l := Spec.map (CommRingCat.ofHom (algebraMap A L))
  let e := Spec.map (CommRingCat.ofHom φ)
  have he : l ≫ a = e ≫ k := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change algebraMap A L (algebraMap R A r) = φ (algebraMap R K r)
    exact (IsFractionRing.lift_algebraMap (K := K) hα r).symm
  have : IsAffineHom ((baseChange k).obj G).X.hom := hη
  have : IsAffine ((Over.pullback k).obj G.X).left :=
    isAffine_of_isAffineHom ((baseChange k).obj G).X.hom
  have hinner : IsAffine ((Over.pullback e).obj ((Over.pullback k).obj G.X)).left :=
    inferInstanceAs (IsAffine (pullback ((baseChange k).obj G).X.hom e))
  let ek : ((Over.pullback (e ≫ k)).obj G.X).left ≅
      ((Over.pullback e).obj ((Over.pullback k).obj G.X)).left :=
    (Over.forget _).mapIso ((Over.pullbackComp e k).app G.X)
  have houter : IsAffine ((Over.pullback (e ≫ k)).obj G.X).left :=
    IsAffine.of_isIso ek.hom (h := hinner)
  have houterA : IsAffine ((Over.pullback (l ≫ a)).obj G.X).left := by
    rw [he]
    exact houter
  let ea : ((Over.pullback (l ≫ a)).obj G.X).left ≅
      ((Over.pullback l).obj ((Over.pullback a).obj G.X)).left :=
    (Over.forget _).mapIso ((Over.pullbackComp l a).app G.X)
  have hinnerA : IsAffine ((Over.pullback l).obj ((Over.pullback a).obj G.X)).left :=
    IsAffine.of_isIso ea.inv (h := houterA)
  have : IsAffine (pullback (pullback.snd G.X.hom a) l) := hinnerA
  change IsAffineHom (pullback.snd (pullback.snd G.X.hom a) l)
  exact isAffineHom_of_isAffine _

/-- Faithfully flat strictly henselian extension and descent remove the two additional
local-base assumptions from the smooth DVR affineness criterion. -/
theorem smoothDvrGenericAffineness_of_strictHenselian
    (h : StrictHenselianSmoothDvrGenericAffinenessStatement.{u}) :
    SmoothDvrGenericAffinenessStatement.{u} := by
  intro R _ _ _ K _ _ _ G hsm hqc hsep hη
  let := hsm
  let := hqc
  let := hsep
  obtain ⟨A, hA, hdA, hvA, hhA, hsA, haA, hff⟩ :=
    Langlands.CommutativeAlgebra.strictHenselianDvrExtension R
  let := hA
  let := hdA
  let := hvA
  let := hhA
  let := hsA
  let := haA
  let := hff
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let GA := (baseChange a).obj G
  have hsmA : Smooth GA.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom a))
  have hqcA : QuasiCompact GA.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom a))
  have hsepA : IsSeparated GA.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom a))
  have hηA : IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))))).obj GA).X.hom :=
    isAffine_generic_baseChange K G hη
  have hGA : IsAffineHom GA.X.hom := h A (FractionRing A) GA hsmA hqcA hsepA hηA
  have := hGA
  have : IsAffine GA.X.left := isAffine_of_isAffineHom GA.X.hom
  have : IsAffine (pullback G.X.hom a) := inferInstanceAs (IsAffine GA.X.left)
  have haff : (CommRingCat.ofHom (algebraMap R A)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have : Flat a := ((flat_and_surjective_SpecMap_iff _).mpr haff).1
  have : Surjective a := ((flat_and_surjective_SpecMap_iff _).mpr haff).2
  have : IsAffine G.X.left :=
    Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent.isAffine_of_isPullback
      (IsPullback.of_hasPullback G.X.hom a)
  exact isAffineHom_of_isAffine _

end SmoothDvrGenericAffinenessDescent

end Langlands.GroupScheme
