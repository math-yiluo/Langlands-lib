import Langlands.AllFieldBZ.Representation.Classification.RegularCuspidalProductSocleStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.AllFieldBZ.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.AllFieldBZ.Representation.Derivative.ProductVanishing
import Langlands.Representation.Category.RenardFinitenessProof
import Langlands.Representation.Classification.MultiplicityOneConstituentProof
import Langlands.Representation.CuspidalSupport.LeviAssociation
import Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof

/-! A unique inducing tensor in the upper Jacquet module detects the socle. -/

noncomputable section

set_option maxHeartbeats 1200000

namespace Langlands.AllFieldBZ.Classification

open CategoryTheory Representation
open Langlands.GeneralLinear Langlands.CuspidalSupport Langlands.Geometric
open LocalFieldPackage.TopologicalData

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

private theorem distinctTensor_stabilizer_count {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
    (hA : letI := T.topology
      Function.Injective
        (fun i => (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV, uF} T))) :
    letI := T.topology
    let ρ := FiniteTensor.external (fun i => (A i).obj.representation)
    Nat.card (AssociatingPermutations B B ρ ρ) = 1 := by
  let := T.topology
  let ρ := FiniteTensor.external (fun i => (A i).obj.representation)
  have hmin : IsMinimalRepresentative B B 1 :=
    ⟨fun i => index_strictMono B i, fun i => index_strictMono B i⟩
  let one : AssociatingPermutations B B ρ ρ :=
    ⟨⟨⟨1, hmin⟩, conjugatesLevi_one B⟩, by
      rw [transport_one]
      exact ⟨Representation.Equiv.refl ρ⟩⟩
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨one, fun w => ?_⟩
  let v := w.val.val.val
  let d (i : Fin B.length) : CuspidalDatum.{uV, uF} T :=
    ⟨B.size i, B.positive i, (A i).isoClass⟩
  have hw : ConjugatesLevi (F := F.Carrier) B B v := w.val.property
  obtain ⟨E⟩ := w.property
  have : ∀ i, Nontrivial (A i).obj := fun i =>
    nontrivial_of_isIrreducible (A i).obj.representation (hρ := (A i).property.1)
  have hfix (i : Fin B.length) : blockMap B B v i = i := by
    obtain ⟨e⟩ : Nonempty (Representation.Equiv
        ((A i).obj.representation.comp (factorHom hw i))
        (A (blockMap B B v i)).obj.representation) := by
      refine nonempty_equiv_of_factor_actions (V := fun i => (A i).obj)
        (W := fun j => (A j).obj)
        (hρ := isIrreducible_comp_of_surjective (A i).obj.representation
          (hρ := (A i).property.1) (factorHom hw i) (factorHom_surjective hw i))
        (hσ := (A (blockMap B B v i)).property.1)
        ?_ ?_ (equivComp E (MonoidHom.mulSingle _ (blockMap B B v i)))
      · intro g x
        exact external_leviConjugation_symm_mulSingle
          (fun i => (A i).obj.representation) hw i g x
      · intro g x
        exact external_mulSingle_tprod (fun i => (A i).obj.representation)
          (blockMap B B v i) g x
    have hd := CuspidalSupport.cuspidalDatum_eq_of_equiv (T := T)
      (ρ₁ := d i) (ρ₂ := d (blockMap B B v i))
      (A i) (A (blockMap B B v i)) rfl rfl
      (blockPositionEquiv hw i) (factorHom hw i)
      (fun g x y => factorHom_apply_entry hw i g x y) e
    exact (hA hd).symm
  have hv : v ∈ blockWeyl B := by
    intro a
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    change blockIndex B (v (B.index i x)) = blockIndex B (B.index i x)
    rw [blockIndex_image hw i x, hfix, blockIndex_index]
  have hcoset : weylDoubleCoset B B w.val.val = weylDoubleCoset B B ⟨1, hmin⟩ :=
    DoubleCoset.eq.mpr
      ⟨v⁻¹, (blockWeyl B).inv_mem hv, 1, (blockWeyl B).one_mem, by simp [v]⟩
  exact Subtype.ext (Subtype.ext (weylDoubleCoset_injective B B hcoset))

private def upperJacquetToRep {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      Rep.{uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  {
    obj := fun X => Rep.of (T.normalizedJacquet B X.representation)
    map := fun f => Rep.ofHom (T.normalizedJacquetMap B (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl
  }

private instance upperJacquetToRep_additive {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    (upperJacquetToRep.{uF, uV} T B).Additive := by
  let := T.topology
  constructor
  intro X Y f g
  ext x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective X.representation x
  change B.jacquetMk Y.representation
    (SmoothRep.hom f v + SmoothRep.hom g v) = _
  exact map_add (B.jacquetMk Y.representation) _ _

private instance upperJacquetToRep_preservesMonomorphisms {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    (upperJacquetToRep.{uF, uV} T B).PreservesMonomorphisms := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine ⟨?_⟩
  intro X Y f hf
  apply (Rep.mono_iff_injective _).mpr
  change Function.Injective (T.normalizedJacquetMap B (SmoothRep.hom f)).toLinearMap
  rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
  exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T B)
    _ ((SmoothRep.mono_iff_injective f).mp hf)
    (Parabolic.isSmooth_radical F T B Y.representation Y.isSmooth)

/-- The unique irreducible submodule in the actual normalized induction. -/
theorem regularCuspidalProductSocle : RegularCuspidalProductSocleStatement.{uF, uV} F T := by
  let := T.topology
  intro n hn B A hA
  let := T.generalLinearTopologicalGroup n
  let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
  let I := (T.normalizedParabolicInductionFunctor B).obj σ
  let J := upperJacquetToRep.{uF, max uF uV} T B
  have hσ := CuspidalSupport.glCuspidalTensor F T n hn B A
  have hassoc : LevisAssociated (F := F.Carrier) B B := LevisAssociated.refl B
  obtain ⟨_, m, e, s, hs⟩ :=
    CuspidalSupport.associatedJacquetFiltration.{uF, uV} F T n B B σ hσ.2.2 hassoc
  let family (w : MinimalConjugatingPermutations (F := F.Carrier) B B) :
      Rep.{uV} ℂ (B.Levi F.Carrier) :=
    Rep.of (transport B B w.val.val w.property σ.representation)
  have hf (w : MinimalConjugatingPermutations (F := F.Carrier) B B) :
      (family w).ρ.IsIrreducible :=
    CuspidalSupport.JacquetLength.isIrreducible_transport w.val.val w.property hσ.1
  have hcount := (finiteFamilyFiltrationMultiplicity ℂ (B.Levi F.Carrier)
    (MinimalConjugatingPermutations (F := F.Carrier) B B) (J.obj I) family hf m e s hs).2
    σ.obj 1
  have hI : HasJordanHolderMultiplicity (J.obj I) σ.obj 1 :=
    hcount.mpr (distinctTensor_stabilizer_count T B A hA).symm
  have hlength : I.HasFiniteLength :=
    (CuspidalSupport.cuspidalInductionLength F T n B σ hσ.1 hσ.2).1
  have hb : 0 < B.length := by
    by_contra! hz
    have he : B.length = 0 := Nat.eq_zero_of_le_zero hz
    have hempty : IsEmpty (Fin B.length) := ⟨fun i => Fin.elim0 (Fin.cast he i)⟩
    exact hn.ne' (B.sum_eq.symm.trans (Finset.sum_of_isEmpty _))
  let : Nontrivial I := Derivative.ProductVanishing.nontrivial_normalizedProduct T B
    (fun i => (A i).obj)
    (fun i => nontrivial_of_isIrreducible (A i).obj.representation (hρ := (A i).property.1))
    ⟨0, hb⟩
  obtain ⟨P, hP, j, hj⟩ :=
    SmoothRep.RenardIrreducibleExistence.exists_irreducible_subrepresentation_of_finiteLength I
      ((SmoothRep.renardFiniteLength_iff I).mpr hlength)
  apply Langlands.Classification.multiplicityOneSocleCore J I σ.obj hI ⟨P, hP, j, hj⟩
  intro Q hQ i hi
  let : Nontrivial Q :=
    nontrivial_of_isIrreducible Q.representation (hρ := hQ)
  have hi0 : SmoothRep.hom i ≠ 0 := by
    intro hz
    exact LinearMap.ne_zero_of_injective hi
      (congrArg Representation.IntertwiningMap.toLinearMap hz)
  let : Mono i := (SmoothRep.mono_iff_injective i).mpr hi
  have hmono : Function.Injective (J.map i).hom := (Rep.mono_iff_injective _).mp inferInstance
  have hdet := CuspidalSupport.exists_ne_zero_normalizedJacquet_hom T B
    (SmoothRep.hom i) hi0
  obtain ⟨k, hk, hkpos, _⟩ := jordanHolderSubobjectSimpleMapDetection
    ℂ (B.Levi F.Carrier) (J.obj I) (J.obj Q) σ.obj hσ.1 (J.map i).hom hmono 1 hI
    (Or.inr hdet)
  exact ⟨k, hk, hkpos⟩

end Langlands.AllFieldBZ.Classification
