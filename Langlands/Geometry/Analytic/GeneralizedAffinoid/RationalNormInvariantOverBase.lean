import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantRestriction
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Continuous weighted rational diagrams over the actual ambient spectrum -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- The original norm-continuous base action restricted to the common subgroup. -/
def normRestrictedBaseAction (H : OpenSubgroup G) : NormContinuousAction K H :=
  (NormContinuousAction.restrict
    { toMonoidHom := H.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }).obj
    (NormContinuousAction.ofAut A ρ hρ)

omit [IsTopologicalGroup G] in
@[simp]
theorem normRestrictedBaseAction_actionAut (H : OpenSubgroup G) :
    (normRestrictedBaseAction ρ hρ H).actionAut = ρ.comp H.toSubgroup.subtype := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  rfl

/-- Joint continuity on the unchanged ambient spectrum is derived from its
actual quotient-norm continuous algebra action. -/
def normRestrictedBaseSpectrum (H : OpenSubgroup G) : ContAction TopCat.{u} H :=
  NormContinuousAction.spectrum (normRestrictedBaseAction ρ hρ H)

@[simp]
theorem normRestrictedBaseSpectrum_apply (H : OpenSubgroup G) (g : H)
    (x : BanachSpectrum A) (a : A) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((normRestrictedBaseSpectrum ρ hρ H).obj.ρ g) x) a =
        x ((ρ g.val).inv.toAlgHom a) := by
  change x (((normRestrictedBaseAction ρ hρ H).actionAut g).inv.toAlgHom a) = _
  rw [normRestrictedBaseAction_actionAut]
  rfl

/-- The actual locus inclusion is continuous and equivariant over the base. -/
def normInvariantLocusToBase (H : OpenSubgroup G) (d : NormInvariantChart ρ hρ H) :
    (normInvariantLocusFunctor ρ hρ H).obj d ⟶ normRestrictedBaseSpectrum ρ hρ H :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        { toFun := fun x => (x : BanachSpectrum A)
          continuous_toFun := continuous_subtype_val }
      comm := fun g => by
        apply TopCat.ext
        intro x
        change BanachSpectrum.comap (ρ g.val).inv.toBoundedRingHom
            (show d.obj.locus from x).val =
          BanachSpectrum.comap
            ((normRestrictedBaseAction ρ hρ H).actionAut g).inv.toBoundedRingHom
              (show d.obj.locus from x).val
        rw [normRestrictedBaseAction_actionAut]
        rfl }

@[simp]
theorem normInvariantLocusToBase_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (x : d.obj.locus) :
    (normInvariantLocusToBase ρ hρ H d).hom.hom x = (x : BanachSpectrum A) := rfl

theorem normInvariantLocusToBase_naturality (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) :
    (normInvariantLocusFunctor ρ hρ H).map f ≫ normInvariantLocusToBase ρ hρ H e =
      normInvariantLocusToBase ρ hρ H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

def normInvariantLocusToBaseNat (H : OpenSubgroup G) :
    normInvariantLocusFunctor ρ hρ H ⟶
      (Functor.const (NormInvariantChart ρ hρ H)).obj
        (normRestrictedBaseSpectrum ρ hρ H) where
  app d := normInvariantLocusToBase ρ hρ H d
  naturality _ _ f := by
    change (normInvariantLocusFunctor ρ hρ H).map f ≫
      normInvariantLocusToBase ρ hρ H _ =
        normInvariantLocusToBase ρ hρ H _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact normInvariantLocusToBase_naturality ρ hρ H f

/-- The unchanged locus diagram now retains its actual maps to the base. -/
def normInvariantLocusOverFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ Over (normRestrictedBaseSpectrum ρ hρ H) :=
  Over.lift (normInvariantLocusFunctor ρ hρ H) (normInvariantLocusToBaseNat ρ hρ H)

@[simp]
theorem normInvariantLocusOverFunctor_obj_hom (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    ((normInvariantLocusOverFunctor ρ hρ H).obj d).hom =
      normInvariantLocusToBase ρ hρ H d := rfl

@[simp]
theorem normInvariantLocusOverFunctor_map_left (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) :
    ((normInvariantLocusOverFunctor ρ hρ H).map f).left =
      (normInvariantLocusFunctor ρ hρ H).map f := rfl

@[simp]
theorem normInvariantLocusOverFunctor_forget (H : OpenSubgroup G) :
    normInvariantLocusOverFunctor ρ hρ H ⋙
        Over.forget (normRestrictedBaseSpectrum ρ hρ H) =
      normInvariantLocusFunctor ρ hρ H := rfl

/-- A finite family in any universe has a common open stabilizer inside U. -/
def finiteNormFamilyOpenSubgroup (U : OpenSubgroup G)
    {I : Type w} [Finite I] (d : I → RationalChart K A) : OpenSubgroup G :=
  U ⊓ OpenSubgroup.iInfOfFinite (fun i => normOpenStabilizer ρ hρ (d i))

@[simp]
theorem mem_finiteNormFamilyOpenSubgroup (U : OpenSubgroup G)
    {I : Type w} [Finite I] (d : I → RationalChart K A) (g : G) :
    g ∈ finiteNormFamilyOpenSubgroup ρ hρ U d ↔
      g ∈ U ∧ ∀ i, g ∈ normOpenStabilizer ρ hρ (d i) := by
  change (g ∈ U ∧ g ∈ (⨅ i, (normOpenStabilizer ρ hρ (d i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf, OpenSubgroup.mem_toSubgroup]

theorem finiteNormFamilyOpenSubgroup_le (U : OpenSubgroup G)
    {I : Type w} [Finite I] (d : I → RationalChart K A) :
    finiteNormFamilyOpenSubgroup ρ hρ U d ≤ U := inf_le_left

theorem finiteNormFamilyOpenSubgroup_le_stabilizer (U : OpenSubgroup G)
    {I : Type w} [Finite I] (d : I → RationalChart K A) (i : I) :
    finiteNormFamilyOpenSubgroup ρ hρ U d ≤ normOpenStabilizer ρ hρ (d i) :=
  inf_le_right.trans (OpenSubgroup.iInfOfFinite_le _ i)

/-- This is the largest subgroup of U preserving every locus of the family. -/
theorem le_finiteNormFamilyOpenSubgroup_iff (U V : OpenSubgroup G)
    {I : Type w} [Finite I] (d : I → RationalChart K A) :
    V ≤ finiteNormFamilyOpenSubgroup ρ hρ U d ↔
      V ≤ U ∧ ∀ i, V ≤ normOpenStabilizer ρ hρ (d i) := by
  constructor
  · intro h
    exact ⟨h.trans (finiteNormFamilyOpenSubgroup_le ρ hρ U d),
      fun i => h.trans (finiteNormFamilyOpenSubgroup_le_stabilizer ρ hρ U d i)⟩
  · rintro ⟨hU, hd⟩ g hg
    exact (mem_finiteNormFamilyOpenSubgroup ρ hρ U d g).mpr
      ⟨hU hg, fun i => hd i hg⟩

@[simp]
theorem finiteNormFamilyOpenSubgroup_empty (U : OpenSubgroup G)
    {I : Type w} [Finite I] [IsEmpty I] (d : I → RationalChart K A) :
    finiteNormFamilyOpenSubgroup ρ hρ U d = U := by
  ext g
  simp

/-- The type-indexed construction extends the existing finite-set construction. -/
@[simp]
theorem finiteNormFamilyOpenSubgroup_finset (U : OpenSubgroup G)
    (s : Finset (RationalChart K A)) :
    finiteNormFamilyOpenSubgroup ρ hρ U (fun d : s => d.val) =
      finiteNormOpenStabilizer ρ hρ s U := rfl

/-- Lift every arrow of a diagram with finitely many objects, with no
finiteness restriction on its hom types. -/
def finiteNormInvariantDiagram (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    J ⥤ NormInvariantChart ρ hρ (finiteNormFamilyOpenSubgroup ρ hρ U F.obj) :=
  ObjectProperty.lift _ F
    (fun j => finiteNormFamilyOpenSubgroup_le_stabilizer ρ hρ U F.obj j)

@[simp]
theorem finiteNormInvariantDiagram_forget (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    finiteNormInvariantDiagram ρ hρ U F ⋙
        (normInvariantChartProperty ρ hρ
          (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)).ι = F := rfl

/-- The finite locus diagram keeps its actual continuous equivariant base maps. -/
def finiteNormInvariantLocusOverDiagram (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    J ⥤ Over (normRestrictedBaseSpectrum ρ hρ
      (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)) :=
  finiteNormInvariantDiagram ρ hρ U F ⋙
    normInvariantLocusOverFunctor ρ hρ (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)

@[simp]
theorem finiteNormInvariantLocusOverDiagram_forget (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    finiteNormInvariantLocusOverDiagram ρ hρ U F ⋙
        Over.forget (normRestrictedBaseSpectrum ρ hρ
          (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)) ⋙ forget₂ _ TopCat.{u} =
      F ⋙ locusFunctor K A := rfl

variable [CompleteSpace K]

/-- Apply the continuous spectrum functor to the existing equivariant
bounded structural map, rather than adding point equivariance as an input. -/
def normInvariantSpectrumToBase (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    (normInvariantSpectrumFunctor ρ hρ H).obj d ⟶ normRestrictedBaseSpectrum ρ hρ H :=
  NormContinuousAction.spectrumFunctor.map
    ((normInvariantBaseMapNat ρ hρ H).app (Opposite.op d)).op

@[simp]
theorem normInvariantSpectrumToBase_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (x : BanachSpectrum d.obj.algebra) :
    (normInvariantSpectrumToBase ρ hρ H d).hom.hom x = d.obj.spectrumMap x := rfl

@[simp]
theorem normInvariantSpectrumToBase_apply_eval (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (x : BanachSpectrum d.obj.algebra) (a : A) :
    BanachSpectrum.toMulRingSeminorm
      ((normInvariantSpectrumToBase ρ hρ H d).hom.hom x) a =
        x (d.obj.baseMap a) := rfl

theorem normInvariantSpectrumToBase_naturality (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) :
    (normInvariantSpectrumFunctor ρ hρ H).map f ≫ normInvariantSpectrumToBase ρ hρ H e =
      normInvariantSpectrumToBase ρ hρ H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  exact f.hom.spectrumMap_over_base x

def normInvariantSpectrumToBaseNat (H : OpenSubgroup G) :
    normInvariantSpectrumFunctor ρ hρ H ⟶
      (Functor.const (NormInvariantChart ρ hρ H)).obj
        (normRestrictedBaseSpectrum ρ hρ H) where
  app d := normInvariantSpectrumToBase ρ hρ H d
  naturality _ _ f := by
    change (normInvariantSpectrumFunctor ρ hρ H).map f ≫
      normInvariantSpectrumToBase ρ hρ H _ =
        normInvariantSpectrumToBase ρ hρ H _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact normInvariantSpectrumToBase_naturality ρ hρ H f

/-- The actual continuous quotient spectra and all restrictions over the base. -/
def normInvariantSpectrumOverFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ Over (normRestrictedBaseSpectrum ρ hρ H) :=
  Over.lift (normInvariantSpectrumFunctor ρ hρ H) (normInvariantSpectrumToBaseNat ρ hρ H)

@[simp]
theorem normInvariantSpectrumOverFunctor_obj_hom (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    ((normInvariantSpectrumOverFunctor ρ hρ H).obj d).hom =
      normInvariantSpectrumToBase ρ hρ H d := rfl

@[simp]
theorem normInvariantSpectrumOverFunctor_map_left (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) :
    ((normInvariantSpectrumOverFunctor ρ hρ H).map f).left =
      (normInvariantSpectrumFunctor ρ hρ H).map f := rfl

@[simp]
theorem normInvariantSpectrumOverFunctor_forget (H : OpenSubgroup G) :
    normInvariantSpectrumOverFunctor ρ hρ H ⋙
        Over.forget (normRestrictedBaseSpectrum ρ hρ H) =
      normInvariantSpectrumFunctor ρ hρ H := rfl

/-- The original rational homeomorphism commutes with the actual maps to A. -/
theorem normInvariantSpectrumLocusIso_over_base (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    (normInvariantSpectrumLocusIso ρ hρ H).hom.app d ≫ normInvariantLocusToBase ρ hρ H d =
      normInvariantSpectrumToBase ρ hρ H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

/-- The natural continuous equivariant rational homeomorphism over the original
ambient spectrum, retaining every bounded restriction map. -/
def normInvariantSpectrumLocusOverIso (H : OpenSubgroup G) :
    normInvariantSpectrumOverFunctor ρ hρ H ≅ normInvariantLocusOverFunctor ρ hρ H :=
  NatIso.ofComponents (fun d =>
    Over.isoMk ((normInvariantSpectrumLocusIso ρ hρ H).app d)
      (normInvariantSpectrumLocusIso_over_base ρ hρ H d))
    (fun f => by
      apply Over.OverMorphism.ext
      exact (normInvariantSpectrumLocusIso ρ hρ H).hom.naturality f)

@[simp]
theorem normInvariantSpectrumLocusOverIso_hom_left (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    ((normInvariantSpectrumLocusOverIso ρ hρ H).hom.app d).left =
      (normInvariantSpectrumLocusIso ρ hρ H).hom.app d := rfl

@[simp]
theorem normInvariantSpectrumLocusOverIso_inv_left (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    ((normInvariantSpectrumLocusOverIso ρ hρ H).inv.app d).left =
      (normInvariantSpectrumLocusIso ρ hρ H).inv.app d := rfl

@[simp]
theorem normInvariantSpectrumLocusOverIso_forget (H : OpenSubgroup G) :
    Functor.isoWhiskerRight (normInvariantSpectrumLocusOverIso ρ hρ H)
        (Over.forget (normRestrictedBaseSpectrum ρ hρ H)) =
      normInvariantSpectrumLocusIso ρ hρ H := rfl

/-- The original finite quotient-spectrum diagram with its continuous actions
and structural maps over the constructed common base action. -/
def finiteNormInvariantSpectrumOverDiagram (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    J ⥤ Over (normRestrictedBaseSpectrum ρ hρ
      (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)) :=
  finiteNormInvariantDiagram ρ hρ U F ⋙
    normInvariantSpectrumOverFunctor ρ hρ (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)

@[simp]
theorem finiteNormInvariantSpectrumOverDiagram_forget (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    finiteNormInvariantSpectrumOverDiagram ρ hρ U F ⋙
        Over.forget (normRestrictedBaseSpectrum ρ hρ
          (finiteNormFamilyOpenSubgroup ρ hρ U F.obj)) ⋙ forget₂ _ TopCat.{u} =
      F ⋙ toTopologicalSpace K A := rfl

/-- The entire finite spectrum diagram and locus diagram are naturally
homeomorphic over the unchanged ambient spectrum and the same common subgroup. -/
def finiteNormInvariantSpectrumLocusOverIso (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalChart K A) :
    finiteNormInvariantSpectrumOverDiagram ρ hρ U F ≅
      finiteNormInvariantLocusOverDiagram ρ hρ U F :=
  Functor.isoWhiskerLeft (finiteNormInvariantDiagram ρ hρ U F)
    (normInvariantSpectrumLocusOverIso ρ hρ (finiteNormFamilyOpenSubgroup ρ hρ U F.obj))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
