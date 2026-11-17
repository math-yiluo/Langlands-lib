import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleCover
import Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # Finite étale local extensions for splitting special fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- An fppf-local diagonalizable model supplies a diagonalizable model over a field
extension when the base is a field. -/
theorem isFieldMultiplicativeType {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : RelativeMultiplicativeType.IsMultiplicativeType G) :
    Langlands.GroupScheme.IsMultiplicativeType G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨a, y, _hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint k)
  let K := (𝒰.X a).residueField y
  let b := (𝒰.X a).fromSpecResidueField y ≫ 𝒰.f a
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hd : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange b).obj G) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso (𝒰.f a) ((𝒰.X a).fromSpecResidueField y) G)
      ((h𝒰 a).baseChange _)
  obtain ⟨N, hN, hfg, ⟨e⟩⟩ := hd
  refine ⟨K, inferInstance, inferInstance, N, hN, hfg, ?_⟩
  change Nonempty (((GroupScheme.baseChange (Spec.map (Spec.preimage b))).obj G) ≅
    (Diagonalizable.groupScheme (CommRingCat.of K) N).toGrp)
  rw [Spec.map_preimage]
  exact ⟨e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of K) N).symm⟩

/-- A finite étale local algebra with a specified field quotient over the base. -/
structure ResidueExtensionData (A K : Type u) [CommRing A] [IsLocalRing A]
    [Field K] [Algebra A K] where
  Carrier : Type u
  [commRing : CommRing Carrier]
  [isLocalRing : IsLocalRing Carrier]
  [algebra : Algebra A Carrier]
  etale : Algebra.Etale A Carrier
  finite : Module.Finite A Carrier
  localHom : IsLocalHom (algebraMap A Carrier)
  cover : Carrier →ₐ[A] K
  cover_surjective : Function.Surjective cover

attribute [instance] ResidueExtensionData.commRing ResidueExtensionData.isLocalRing
  ResidueExtensionData.algebra ResidueExtensionData.etale ResidueExtensionData.finite
  ResidueExtensionData.localHom

namespace ResidueExtensionData

variable {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
  (d : ResidueExtensionData A K)

instance free : Module.Free A d.Carrier :=
  Module.free_of_flat_of_isLocalRing

instance faithfullyFlat : Module.FaithfullyFlat A d.Carrier :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

instance specFinite : IsFinite (Spec.algebraMap A d.Carrier) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr d.finite)

instance specEtale : Etale (Spec.algebraMap A d.Carrier) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr d.etale)

instance specSurjective : Surjective (Spec.algebraMap A d.Carrier) :=
  ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr d.faithfullyFlat)).2

/-- The specified field quotient is the residue field of the lifted algebra. -/
def residueFieldEquiv : IsLocalRing.ResidueField d.Carrier ≃+* K := by
  let : Algebra d.Carrier K := d.cover.toRingHom.toAlgebra
  exact (Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison.residueCoverEquiv
    d.cover_surjective).toRingEquiv

@[simp]
theorem residueFieldEquiv_residue (x : d.Carrier) :
    d.residueFieldEquiv (IsLocalRing.residue d.Carrier x) = d.cover x := by
  let : Algebra d.Carrier K := d.cover.toRingHom.toAlgebra
  exact (Langlands.CommutativeAlgebra.HenselianFiniteEtaleResidueComparison.residueCoverEquiv
    d.cover_surjective).commutes x

/-- The maximal ideal of the lifted local algebra is the extended maximal ideal. -/
theorem map_maximalIdeal :
    (IsLocalRing.maximalIdeal A).map (algebraMap A d.Carrier) =
      IsLocalRing.maximalIdeal d.Carrier :=
  Algebra.FormallyUnramified.map_maximalIdeal

instance complete [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsAdicComplete (IsLocalRing.maximalIdeal d.Carrier) d.Carrier := by
  rw [← d.map_maximalIdeal]
  exact (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal A) d.Carrier).mpr
    (IsAdicComplete.of_finite_of_isNoetherianRing (IsLocalRing.maximalIdeal A) d.Carrier)

end ResidueExtensionData

/-- Lift a finite separable residue extension to a finite étale local algebra.
No Henselian or completeness assumption on the base is required for the lift. -/
def residueExtension (A K : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [Algebra A K]
    [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [FiniteDimensional (IsLocalRing.ResidueField A) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) K] :
    ResidueExtensionData A K := by
  classical
  apply Classical.choice
  have : Module.Finite A K :=
    Module.Finite.trans (IsLocalRing.ResidueField A) K
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField A) K :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyUnramified A K :=
    Algebra.FormallyUnramified.comp A (IsLocalRing.ResidueField A) K
  have : IsLocalHom (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalHom.of_surjective _ IsLocalRing.residue_surjective
  have hloc : IsLocalHom (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A (IsLocalRing.ResidueField A) K]
    infer_instance
  obtain ⟨L, _, _, hL, hfin, het, π, hπ⟩ :=
    Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal.exists_etaleCover
      (R := A) (B := K)
  let : IsLocalRing L := hL
  have hloc' : IsLocalHom (algebraMap A L) := by
    have hcomp : π.toRingHom.comp (algebraMap A L) = algebraMap A K := by
      ext r
      exact π.commutes r
    have : IsLocalHom (π.toRingHom.comp (algebraMap A L)) := by
      rw [hcomp]
      exact hloc
    exact isLocalHom_of_comp (algebraMap A L) π.toRingHom
  exact ⟨{
    Carrier := L
    etale := het
    finite := hfin
    localHom := hloc'
    cover := π
    cover_surjective := hπ }⟩

/-- A finite Galois field splitting of a special fibre, together with a finite
étale local lift of that field quotient to the original base. -/
structure SpecialFibreSplittingData (A : Type u) [CommRing A] [IsLocalRing A]
    (G : GroupScheme (Spec (CommRingCat.of A))) where
  Field : Type u
  [field : _root_.Field Field]
  [residueAlgebra : Algebra (IsLocalRing.ResidueField A) Field]
  [baseAlgebra : Algebra A Field]
  [tower : IsScalarTower A (IsLocalRing.ResidueField A) Field]
  finite : FiniteDimensional (IsLocalRing.ResidueField A) Field
  galois : IsGalois (IsLocalRing.ResidueField A) Field
  lift : ResidueExtensionData A Field
  Characters : Type u
  [addCommGroup : AddCommGroup Characters]
  fg : AddGroup.FG Characters
  iso : (GroupScheme.baseChange (Spec.algebraMap A Field)).obj G ≅
    (Diagonalizable.groupScheme (CommRingCat.of Field) Characters).toGrp

attribute [instance] SpecialFibreSplittingData.field SpecialFibreSplittingData.residueAlgebra
  SpecialFibreSplittingData.baseAlgebra SpecialFibreSplittingData.tower
  SpecialFibreSplittingData.finite SpecialFibreSplittingData.galois
  SpecialFibreSplittingData.addCommGroup SpecialFibreSplittingData.fg

/-- A multiplicative-type special fibre has a diagonalizable presentation over
the residue field of a finite étale local algebra over the original base. -/
def specialFibreSplitting (A : Type u) [CommRing A] [IsLocalRing A]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    (hG : RelativeMultiplicativeType.IsMultiplicativeType
      ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)) :
    SpecialFibreSplittingData A G := by
  classical
  apply Classical.choice
  let k := IsLocalRing.ResidueField A
  let sp := Spec.algebraMap A k
  obtain ⟨K, hK, aK, hfin, hgal, N, hN, hfg, ⟨e⟩⟩ :=
    multiplicativeTypeFiniteGaloisSplitting k ((GroupScheme.baseChange sp).obj G)
      (isFieldMultiplicativeType hG)
  let : _root_.Field K := hK
  let : Algebra k K := aK
  let : FiniteDimensional k K := hfin
  let : IsGalois k K := hgal
  let : AddCommGroup N := hN
  let : AddGroup.FG N := hfg
  let : Algebra A K := ((algebraMap k K).comp (algebraMap A k)).toAlgebra
  let : IsScalarTower A k K := .of_algebraMap_eq fun _ => rfl
  have hc : Spec.algebraMap A K = Spec.algebraMap k K ≫ sp := by
    rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have he : Nonempty ((GroupScheme.baseChange (Spec.algebraMap A K)).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) N).toGrp) := by
    rw [hc]
    exact ⟨baseChangeCompIso sp (Spec.algebraMap k K) G ≪≫ e⟩
  exact ⟨{
    Field := K
    finite := hfin
    galois := hgal
    lift := residueExtension A K
    Characters := N
    fg := hfg
    iso := he.some }⟩

namespace SpecialFibreSplittingData

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {G : GroupScheme (Spec (CommRingCat.of A))} (d : SpecialFibreSplittingData A G)

/-- The splitting presentation after pulling the lifted group back to its
specified residue-field quotient. -/
def coverFibreIso :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom d.lift.cover.toRingHom))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A d.lift.Carrier)).obj G) ≅
      (Diagonalizable.groupScheme (CommRingCat.of d.Field) d.Characters).toGrp := by
  have hc : Spec.map (CommRingCat.ofHom d.lift.cover.toRingHom) ≫
      Spec.algebraMap A d.lift.Carrier = Spec.algebraMap A d.Field := by
    rw [Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext a
    exact d.lift.cover.commutes a
  have he : (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom d.lift.cover.toRingHom) ≫
          Spec.algebraMap A d.lift.Carrier)).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of d.Field) d.Characters).toGrp := by
    rw [hc]
    exact d.iso
  exact (baseChangeCompIso (Spec.algebraMap A d.lift.Carrier)
    (Spec.map (CommRingCat.ofHom d.lift.cover.toRingHom)) G).symm ≪≫ he

/-- The actual special fibre of the lifted group is diagonalizable. -/
theorem specialFibre_isDiagonalizable :
    RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap d.lift.Carrier (IsLocalRing.ResidueField d.lift.Carrier))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A d.lift.Carrier)).obj G)) := by
  let H := (GroupScheme.baseChange (Spec.algebraMap A d.lift.Carrier)).obj G
  let b := Spec.map (CommRingCat.ofHom d.lift.cover.toRingHom)
  let q := Spec.map (CommRingCat.ofHom d.lift.residueFieldEquiv.symm.toRingHom)
  have hq : q ≫ b =
      Spec.algebraMap d.lift.Carrier (IsLocalRing.ResidueField d.lift.Carrier) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    change d.lift.residueFieldEquiv.symm (d.lift.cover x) = _
    rw [← d.lift.residueFieldEquiv_residue x, RingEquiv.symm_apply_apply]
    rfl
  have hd : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange b).obj H) :=
    ⟨d.Characters, inferInstance, d.fg,
      ⟨d.coverFibreIso ≪≫ Diagonalizable.relativeModelIso _ _⟩⟩
  have hs : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (q ≫ b)).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso (baseChangeCompIso b q H)
      (hd.baseChange q)
  rwa [hq] at hs

end SpecialFibreSplittingData

end Langlands.GroupScheme.CompleteLocalDeformation
