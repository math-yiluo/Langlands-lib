import Langlands.GroupScheme.Torus.CompleteLocalSplittingExtension
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementProof

/-! # Local finite étale splitting covers over a complete local base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A finite étale local cover over which the supplied group is diagonalizable. -/
structure LocalSplittingData (A : Type u) [CommRing A] [IsLocalRing A]
    (H : GroupScheme (Spec (CommRingCat.of A))) where
  Carrier : Type u
  [commRing : CommRing Carrier]
  [isLocalRing : IsLocalRing Carrier]
  [algebra : Algebra A Carrier]
  etale : Algebra.Etale A Carrier
  finite : Module.Finite A Carrier
  localHom : IsLocalHom (algebraMap A Carrier)
  split : RelativeMultiplicativeType.IsDiagonalizable
    ((GroupScheme.baseChange (Spec.algebraMap A Carrier)).obj H)

attribute [instance] LocalSplittingData.commRing LocalSplittingData.isLocalRing
  LocalSplittingData.algebra LocalSplittingData.etale LocalSplittingData.finite
  LocalSplittingData.localHom

namespace LocalSplittingData

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {H : GroupScheme (Spec (CommRingCat.of A))} (d : LocalSplittingData A H)

/-- The local cover also carries its canonical residue-field quotient. -/
def residueData : ResidueExtensionData A (IsLocalRing.ResidueField d.Carrier) where
  Carrier := d.Carrier
  etale := d.etale
  finite := d.finite
  localHom := d.localHom
  cover := IsScalarTower.toAlgHom A d.Carrier (IsLocalRing.ResidueField d.Carrier)
  cover_surjective := IsLocalRing.residue_surjective

instance free : Module.Free A d.Carrier := d.residueData.free
instance faithfullyFlat : Module.FaithfullyFlat A d.Carrier := d.residueData.faithfullyFlat
instance specFinite : IsFinite (Spec.algebraMap A d.Carrier) := d.residueData.specFinite
instance specEtale : Etale (Spec.algebraMap A d.Carrier) := d.residueData.specEtale
instance specSurjective : Surjective (Spec.algebraMap A d.Carrier) := d.residueData.specSurjective

instance noetherian [IsNoetherianRing A] : IsNoetherianRing d.Carrier :=
  IsNoetherianRing.of_finite A d.Carrier

instance complete [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsAdicComplete (IsLocalRing.maximalIdeal d.Carrier) d.Carrier :=
  d.residueData.complete

end LocalSplittingData

/-- A finite étale splitting cover over a Henselian local ring can be refined
by a finite étale local splitting cover. -/
def localSplitting (A : Type u) [CommRing A] [HenselianLocalRing A]
    (H : GroupScheme (Spec (CommRingCat.of A)))
    (hH : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H)) :
    LocalSplittingData A H := by
  classical
  apply Classical.choice
  obtain ⟨S', p, hfin, het, hsurj, hdiag⟩ := hH
  let : IsFinite p := hfin
  let : Etale p := het
  let : Surjective p := hsurj
  let : IsAffine S' := isAffine_of_isAffineHom p
  let f := S'.isoSpec.inv ≫ p
  have hf : Etale f := inferInstance
  have : Surjective f := inferInstance
  have hx : IsLocalRing.closedPoint A ∈ Set.range f :=
    f.surjective _
  obtain ⟨B, hB, hloc, aB, hetB, hfinB, g, hg⟩ :=
    Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement A Γ(S', ⊤) f hf hx
  let : CommRing B := hB
  let : IsLocalRing B := hloc
  let : Algebra A B := aB
  let : Algebra.Etale A B := hetB
  let : Module.Finite A B := hfinB
  let : Module.Free A B := Module.free_of_flat_of_isLocalRing
  let : FaithfulSMul A B := inferInstance
  have hlocalMap : IsLocalHom (algebraMap A B) := inferInstance
  let b := g ≫ S'.isoSpec.inv
  have hb : b ≫ p = Spec.algebraMap A B := by
    simpa only [b, f, Category.assoc] using hg
  have hd : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (b ≫ p)).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso (baseChangeCompIso p b H)
      (hdiag.baseChange b)
  rw [hb] at hd
  exact ⟨{
    Carrier := B
    etale := hetB
    finite := hfinB
    localHom := hlocalMap
    split := hd }⟩

/-- A complete local ring is Henselian for the local-ring convention. -/
theorem henselianLocalRing_of_complete (A : Type u) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : HenselianLocalRing A where
  is_henselian f hf a ha hu :=
    HenselianRing.is_henselian f hf a ha (hu.map (IsLocalRing.residue A))

/-- Special fibres commute with base change along a local algebra map. -/
def specialFibreBaseChangeIso {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (G : GroupScheme (Spec (CommRingCat.of A))) :
    (GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G) ≅
      (GroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G) := by
  have hc : Spec.algebraMap B (IsLocalRing.ResidueField B) ≫ Spec.algebraMap A B =
      Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ≫
        Spec.algebraMap A (IsLocalRing.ResidueField A) := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  exact (baseChangeCompIso (Spec.algebraMap A B)
    (Spec.algebraMap B (IsLocalRing.ResidueField B)) G).symm ≪≫
      eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj G) hc) ≪≫
      baseChangeCompIso (Spec.algebraMap A (IsLocalRing.ResidueField A))
        (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) G

/-- One finite étale local cover splits the source and the special fibre of
the target. -/
structure SimultaneousSplittingData (A : Type u) [CommRing A] [IsLocalRing A]
    (G H : GroupScheme (Spec (CommRingCat.of A))) where
  source : LocalSplittingData A H
  targetSpecial : RelativeMultiplicativeType.IsDiagonalizable
    ((GroupScheme.baseChange
      (Spec.algebraMap source.Carrier (IsLocalRing.ResidueField source.Carrier))).obj
      ((GroupScheme.baseChange (Spec.algebraMap A source.Carrier)).obj G))

/-- Simultaneously split the source and the special fibre of the target after
a finite étale local extension of a complete local noetherian base. -/
def simultaneousSplitting (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (G H : GroupScheme (Spec (CommRingCat.of A)))
    (hH : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H))
    (hG : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)) :
    SimultaneousSplittingData A G H := by
  let : HenselianLocalRing A := henselianLocalRing_of_complete A
  let dH := localSplitting A H hH
  let B := dH.Carrier
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let c := Spec.algebraMap A B
  have hGB : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap B (IsLocalRing.ResidueField B))).obj
        ((GroupScheme.baseChange c).obj G)) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_iso (specialFibreBaseChangeIso G)
      (hG.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)))
  let dG := specialFibreSplitting B ((GroupScheme.baseChange c).obj G) hGB
  let C := dG.lift.Carrier
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B C := .of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale A C := Algebra.Etale.comp A B C
  let : Module.Finite A C := Module.Finite.trans B C
  have hlocal : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance
  have hc : Spec.algebraMap A C = Spec.algebraMap B C ≫ c := by
    rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have hdH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap A C)).obj H) := by
    rw [hc]
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso c (Spec.algebraMap B C) H)
      (dH.split.baseChange (Spec.algebraMap B C))
  let eG : (GroupScheme.baseChange (Spec.algebraMap A C)).obj G ≅
      (GroupScheme.baseChange (Spec.algebraMap B C)).obj ((GroupScheme.baseChange c).obj G) :=
    eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj G) hc) ≪≫
      baseChangeCompIso c (Spec.algebraMap B C) G
  exact {
    source := {
      Carrier := C
      etale := inferInstance
      finite := inferInstance
      localHom := hlocal
      split := hdH }
    targetSpecial := RelativeMultiplicativeType.IsDiagonalizable.of_iso
      ((GroupScheme.baseChange (Spec.algebraMap C (IsLocalRing.ResidueField C))).mapIso eG)
      dG.specialFibre_isDiagonalizable }

end Langlands.GroupScheme.CompleteLocalDeformation
