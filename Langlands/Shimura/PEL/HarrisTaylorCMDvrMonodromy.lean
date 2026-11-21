import Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-! # Generic monodromy over a discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped PreGaloisCategory FintypeCatDiscrete

noncomputable section

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.FiniteEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- These categorical connectedness comparisons use the same argument as
-- `HarrisTaylorCMArtinianLevel` for finite étale covers.
private theorem cover_notInitial_of_nonempty {S : Scheme.{u}} (Y : Cover S)
    [Nonempty Y.obj.left] (h : IsInitial Y) : False := by
  have hEmpty := isInitial_iff_isEmpty.mp ⟨h.isInitialObj (coverToScheme S) _⟩
  exact hEmpty.false (Classical.choice ‹Nonempty Y.obj.left›)

private def cover_initial_of_empty {S : Scheme.{u}} (Y : Cover S)
    [IsEmpty Y.obj.left] : IsInitial Y := by
  let i : (⊥_ (Cover S)) ⟶ Y := initial.to Y
  have : IsEmpty ((coverToScheme S).obj Y) := ‹IsEmpty Y.obj.left›
  have : IsIso ((coverToScheme S).map i) :=
    AlgebraicGeometry.isIso_of_isEmpty _
  have : IsIso i := isIso_of_reflects_iso i (coverToScheme S)
  exact initialIsInitial.ofIso (asIso i)

private theorem cover_connectedSpace {S : Scheme.{u}} (Y : Cover S)
    [PreGaloisCategory.IsConnected Y] : ConnectedSpace Y.obj.left := by
  have hNonempty : Nonempty Y.obj.left := by
    by_contra h
    have : IsEmpty Y.obj.left := not_nonempty_iff.mp h
    exact PreGaloisCategory.IsConnected.notInitial (cover_initial_of_empty Y)
  refine connectedSpace_iff_clopen.mpr ⟨hNonempty, ?_⟩
  intro s hs
  by_cases he : s = ∅
  · exact Or.inl he
  let V : Y.obj.left.Opens := ⟨s, hs.2⟩
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hs.1)
  let Z : Cover S := cover (V.ι ≫ Y.obj.hom)
  let i : Z ⟶ Y := ObjectProperty.homMk (Over.homMk V.ι)
  have : Mono i := (coverToScheme S).mono_of_mono_map (f := i)
    (inferInstanceAs (Mono V.ι))
  have : Nonempty Z.obj.left := (Set.nonempty_iff_ne_empty.mpr he).to_subtype
  have : IsIso i := PreGaloisCategory.IsConnected.noTrivialComponent Z i
    (cover_notInitial_of_nonempty Z)
  have : IsIso V.ι := inferInstanceAs (IsIso ((coverToScheme S).map i))
  have hV := range_eq_univ V.ι
  rw [Scheme.Opens.range_ι] at hV
  exact Or.inr hV

private theorem cover_isConnected_of_connectedSpace {S : Scheme.{u}} (Y : Cover S)
    [ConnectedSpace Y.obj.left] : PreGaloisCategory.IsConnected Y where
  notInitial := cover_notInitial_of_nonempty Y
  noTrivialComponent Z i _ h := by
    have hNonempty : Nonempty Z.obj.left := by
      by_contra hEmpty
      have : IsEmpty Z.obj.left := not_nonempty_iff.mp hEmpty
      exact h (cover_initial_of_empty Z)
    have hfe : finiteEtale i.hom.left :=
      finiteEtale.of_postcomp (W' := finiteEtale) i.hom.left Y.obj.hom Y.property (by
        rw [Over.w]
        exact Z.property)
    have : IsFinite i.hom.left := hfe.1
    have : Etale i.hom.left := hfe.2
    have : Mono i.hom := preserves_mono_of_preservesLimit (inclusion S) i
    have : Mono i.hom.left := inferInstance
    have : IsClosedImmersion i.hom.left :=
      (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩
    have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
    have hr := (connectedSpace_iff_clopen.mp ‹ConnectedSpace Y.obj.left›).2
      (Set.range i.hom.left)
      ⟨i.hom.left.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range i.hom.left⟩
    have hsurj : Surjective i.hom.left := ⟨Set.range_eq_univ.mp
      (hr.resolve_left (Set.range_nonempty i.hom.left).ne_empty)⟩
    exact (isIso_iff_of_reflects_iso i (coverToScheme S)).mp
      ((isIso_iff_isOpenImmersion_and_surjective i.hom.left).mpr ⟨inferInstance, hsurj⟩)

variable (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of K))
  (ht : ∀ Y : Cover (Spec (.of K)), Finite (Fiber t Y))
  (hs : ∀ Y : Cover (Spec (.of V)), Finite (Fiber (t ≫ Spec.algebraMap V K) Y))

local notation "j" => Spec.algebraMap V K

private theorem specStalk_isDomain_isIntegrallyClosed (x : Spec (.of V)) :
    IsDomain ((Spec (.of V)).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec (.of V)).presheaf.stalk x) := by
  have hprime : x.asIdeal.IsPrime := x.isPrime
  have hclosed : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors
  exact EtaleNormalLocallyIrreducible.isDomain_isIntegrallyClosed_of_ringEquiv
    (Spec.stalkIso (.of V) x).commRingCatIsoToRingEquiv.symm ⟨inferInstance, hclosed⟩

/-- The specified fraction-field morphism induces a surjection on the actual
pointed fundamental groups. -/
theorem dvrGenericMonodromy_surjective :
    Function.Surjective (fundamentalGroupMap j t (t ≫ j) rfl ht hs) := by
  let b := j
  let : IsOpenImmersion b := isOpenImmersion_spec_fractionRing_of_dvr V K
  obtain ⟨hGS, hFS⟩ := geometricGaloisFiberFunctor (t ≫ b) hs
  obtain ⟨hGT, hFT⟩ := geometricGaloisFiberFunctor t ht
  let F := fiberFunctor (t ≫ b) hs
  let G := FundamentalGroup t ht
  let α := fundamentalGroupMap b t (t ≫ b) rfl ht hs
  let (Y : Cover (Spec (.of V))) : MulAction G (F.obj Y) := MulAction.compHom (F.obj Y) α
  let : PreGaloisCategory.IsNaturalSMul F G := {
    naturality g _ _ f x := (smul_naturality (t ≫ b) hs f (α g) x).symm
  }
  let (Y : Cover (Spec (.of V))) : ContinuousSMul G (F.obj Y) :=
    MulAction.continuousSMul_compHom (continuous_fundamentalGroupMap b t (t ≫ b) rfl ht hs)
  have htrans (Y : Cover (Spec (.of V))) [PreGaloisCategory.IsGalois Y] :
      MulAction.IsPretransitive G (F.obj Y) := by
    let : ConnectedSpace Y.obj.left := cover_connectedSpace Y
    let : IsFinite Y.obj.hom := Y.property.1
    let : Etale Y.obj.hom := Y.property.2
    let : IrreducibleSpace Y.obj.left :=
      EtaleNormalLocallyIrreducible.irreducibleSpace_of_etale Y.obj.hom
        (specStalk_isDomain_isIntegrallyClosed V)
    let : Surjective Y.obj.hom :=
      ⟨EtaleNormalLocallyIrreducible.surjective_of_isFinite_of_etale Y.obj.hom⟩
    let p := pullback.fst Y.obj.hom b
    let q := pullback.snd Y.obj.hom b
    let : Surjective q := inferInstanceAs (Surjective (pullback.snd Y.obj.hom b))
    let X : Scheme.{u} := pullback Y.obj.hom b
    let : Nonempty X := by
      obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
      obtain ⟨y, -⟩ := q.surjective x
      exact ⟨y⟩
    let : IrreducibleSpace X := p.isOpenEmbedding.irreducibleSpace
    let : ConnectedSpace ((pullbackFunctor b).obj Y).obj.left :=
      inferInstanceAs (ConnectedSpace X)
    let : PreGaloisCategory.IsConnected ((pullbackFunctor b).obj Y) :=
      cover_isConnected_of_connectedSpace _
    have hOrbit := PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected
      (fiberFunctor t ht) ((pullbackFunctor b).obj Y)
    let eY := pullbackFiberEquiv b t (t ≫ b) rfl Y
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := hOrbit.exists_smul_eq (eY x) (eY y)
    refine ⟨g, eY.injective ?_⟩
    exact (pullbackFiberEquiv_smul b t (t ≫ b) rfl ht hs g Y x).trans hg
  have hα : PreGaloisCategory.toAut F G = α := by
    ext g : 1
    exact fundamentalGroup_ext (fun _ _ => rfl)
  change Function.Surjective α
  rw [← hα]
  exact PreGaloisCategory.toAut_surjective_of_isPretransitive F G htrans

/-- A lift of an element of monodromy over the DVR to monodromy over its
fraction field, for the same geometric point. -/
def dvrGenericMonodromyLift (g : FundamentalGroup (t ≫ j) hs) : FundamentalGroup t ht :=
  Function.surjInv (dvrGenericMonodromy_surjective V K t ht hs) g

@[simp]
theorem fundamentalGroupMap_dvrGenericMonodromyLift (g : FundamentalGroup (t ≫ j) hs) :
    fundamentalGroupMap j t (t ≫ j) rfl ht hs (dvrGenericMonodromyLift V K t ht hs g) = g :=
  Function.surjInv_eq (dvrGenericMonodromy_surjective V K t ht hs) g

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
