import Langlands.Cohomology.AnalyticEtaleRelativeGaloisAcyclicity
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Galois–Cartan reduction of analytic étale local acyclicity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open EtaleGermGaloisCover

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- A pointed étale arrow can be refined by a distinguished relative Galois
cover after shrinking the ambient base at the chosen point. -/
def HasPointedEtaleGaloisRefinements : Prop :=
  ∀ (y : localizedSpaceFunctor.obj X) (V : EtaleGermNeighborhood X y)
    (W : EtaleSite X) (f : W ⟶ V.obj) (x : localizedSpaceFunctor.obj W.left),
    localizedSpaceFunctor.map f.left x = V.point →
      ∃ (E : EtaleGermGaloisCover V) (g : E.source.obj ⟶ W), g ≫ f = E.toBase

variable {X} (R : Type (max u (v + 1) uL)) [CommRing R]
variable {y : localizedSpaceFunctor.obj X}

private abbrev EtaleModules (Y : LocalizedCategory.{u, v, v} (K := K))
    (k : Type w) [CommRing k] := Sheaf (etaleTopology Y) (ModuleCat.{w} k)

local notation "J" => etaleTopology X
local notation "Sh" => EtaleModules X R

private theorem germ_map_germι {I : Type (max u (v + 1) uL)} [SmallCategory I]
    (V : I ⥤ EtaleSite X) {F F' : Sh} (f : F ⟶ F') (i : I)
    (s : F.obj.obj (op (V.obj i))) :
    (GaloisGerms.germ J R V).map f (GaloisGerms.germι J R V F i s) =
      GaloisGerms.germι J R V F' i (f.hom.app (op (V.obj i)) s) :=
  ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft V.op f.hom) (op i)) s

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : G →* Aut X}
variable [T2Space (localizedSpaceFunctor.obj X)]

private theorem aug_germι_stage {V : EtaleGermNeighborhood X y}
    (E : EtaleGermGaloisCover V) (hρ : IsContinuousAction ρ) (F : Sh)
    (j : coverIndex.{u, v, uL} E)
    (s : F.obj.obj (op ((baseDiagram.{u, v, uL} E).obj j))) :
    ((toGermCover.{u, v, uL, z} E R hρ).aug.app F)
      (GaloisGerms.germι J R (etaleNeighborhoodDiagram.{u, v, uL} X y V.obj) F j.obj s) =
    GaloisGerms.germι J R (etaleNeighborhoodDiagram.{u, v, uL} X y E.source.obj) F j.obj
      (F.obj.map ((germDatum.{u, v, uL} E).p.app j).op s) := by
  let A := toGermCover.{u, v, uL, z} E R hρ
  let D := germDatum.{u, v, uL} E
  let B := etaleNeighborhoodDiagram.{u, v, uL} X y V.obj
  let C := etaleNeighborhoodDiagram.{u, v, uL} X y E.source.obj
  have := distinguishedNbhdInclusion_initial.{u, v, uL} hρ E.mem_baseOpen
  have hbase :
      A.baseIso.hom.app F (GaloisGerms.germι J R B F j.obj s) =
        GaloisGerms.germι J R (baseDiagram.{u, v, uL} E) F j s :=
    ConcreteCategory.congr_hom
      (GaloisGerms.germι_germReindexIso_hom J R B E.indexInclusion F j) s
  have hcov (t : F.obj.obj (op ((coverDiagram.{u, v, uL} E).obj j))) :
      A.coveringIso.inv.app F (GaloisGerms.germι J R (coverDiagram.{u, v, uL} E) F j t) =
        GaloisGerms.germι J R C F j.obj t :=
    ConcreteCategory.congr_hom
      (GaloisGerms.germι_germReindexIso_inv J R C E.indexInclusion F j) t
  change A.coveringIso.inv.app F
    ((D.aug R).app F (A.baseIso.hom.app F (GaloisGerms.germι J R B F j.obj s))) = _
  rw [hbase, D.germι_aug_apply R F j s]
  exact hcov _

private theorem etaleGermCartan_local_lift (hρ : IsContinuousAction ρ)
    (href : HasPointedEtaleGaloisRefinements X) (S : ShortComplex Sh) (hS : S.ShortExact)
    (V : EtaleGermNeighborhood X y) (s : (etaleSectionGerm.{u, v, uL} R V).obj S.X₃) :
    ∃ (E : EtaleGermGaloisCover V) (t : (etaleSectionGerm.{u, v, uL} R E.source).obj S.X₂),
      (etaleSectionGerm.{u, v, uL} R E.source).map S.g t =
        (toGermCover.{u, v, uL, z} E R hρ).aug.app S.X₃ s := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := etaleSite_essentiallySmall_points.{u, v, uL} X
  have : ∀ Y : (EtaleSite X)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL} (EtaleSite X)).inverse.op)
      (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  have : (etaleTopology X).WEqualsLocallyBijective (ModuleCat.{max u (v + 1) uL} R) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  have : Epi S.g := hS.epi_g
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 inferInstance
  let B := etaleNeighborhoodDiagram.{u, v, uL} X y V.obj
  obtain ⟨i₀, s₀, hs⟩ := Concrete.colimit_exists_rep (B.op ⋙ S.X₃.obj) s
  let i := i₀.unop
  let U := (nbhdOpen.{u, v, uL} X y).obj i
  let P := V.restrict U (mem_nbhdOpen X y i)
  let H := Presheaf.imageSieve S.g.hom s₀
  have hH : H ∈ J P.obj := Presheaf.imageSieve_mem J S.g.hom s₀
  obtain ⟨W, f, ⟨t₀, ht₀⟩, x, hx⟩ :=
    jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting
      (etalePointwiseLifting (K := K)) H hH P.point
  let k := (etaleOpenRestrictionInclusion X U).app V.obj
  have hfx : localizedSpaceFunctor.map (f ≫ k).left x = V.point := by
    change localizedSpaceFunctor.map (f.left ≫ k.left) x = V.point
    have hx' : localizedSpaceFunctor.map f.left x = P.point := hx
    rw [localizedSpaceFunctor.map_comp_apply, hx']
    rfl
  obtain ⟨E, g, hg⟩ := href y V W (f ≫ k) x hfx
  obtain ⟨j, ⟨b⟩⟩ := exists_distinguishedNbhdIndex.{u, v, uL} hρ E.mem_baseOpen i
  let T := (nbhdOpen.{u, v, uL} X y).obj j.obj
  let C := etaleNeighborhoodDiagram.{u, v, uL} X y E.source.obj
  let a : C.obj j.obj ⟶ W := (etaleOpenRestrictionInclusion X T).app E.source.obj ≫ g
  let D := germDatum.{u, v, uL} E
  have h₁ : B.map b ≫ k = (etaleOpenRestrictionInclusion X T).app V.obj :=
    congrArg (fun η => η.app V.obj)
      (etaleOpenRestrictionInclusion_naturality X ((nbhdOpen X y).map b))
  have h₂ : D.p.app j ≫ (etaleOpenRestrictionInclusion X T).app V.obj =
      (etaleOpenRestrictionInclusion X T).app E.source.obj ≫ E.toBase :=
    (etaleOpenRestrictionInclusion X T).naturality E.toBase
  have hcomp : a ≫ f = D.p.app j ≫ B.map b := by
    apply (cancel_mono k).mp
    simp only [a, Category.assoc, hg, h₁, h₂]
  refine ⟨E, GaloisGerms.germι J R C S.X₂ j.obj (S.X₂.obj.map a.op t₀), ?_⟩
  change GaloisGerms.germι J R B S.X₃ i s₀ = s at hs
  have hrepresent := GaloisGerms.GermGaloisDatum.germι_eq_germι_map R S.X₃ b s₀
  change GaloisGerms.germι J R B S.X₃ i s₀ =
    GaloisGerms.germι J R B S.X₃ j.obj (S.X₃.obj.map (B.map b).op s₀) at hrepresent
  rw [← hs, hrepresent, aug_germι_stage R E hρ S.X₃ j]
  change (GaloisGerms.germ J R C).map S.g
      (GaloisGerms.germι J R C S.X₂ j.obj (S.X₂.obj.map a.op t₀)) = _
  rw [germ_map_germι.{u, v, uL} R C S.g j.obj, NatTrans.naturality_apply, ht₀]
  rw [GaloisCovering.map_map_apply S.X₃.obj f a s₀, hcomp]
  exact congrArg (fun t => GaloisGerms.germι J R C S.X₃ j.obj t)
    (GaloisCovering.map_map_apply S.X₃.obj (B.map b) (D.p.app j) s₀).symm

/-- The Cartan system on analytic section germs, given pointed Galois refinement. -/
def etaleGermCartanSystem (hρ : IsContinuousAction ρ) (href : HasPointedEtaleGaloisRefinements X) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    GaloisCartan.GaloisCechSystem
      (etaleSectionGerm.{u, v, uL} (X := X) (y := y) R) := by
  have := etale_hasSheafify.{u, v, uL} X R
  exact GaloisGerms.galoisCechSystemOfGermCovers J R _
    EtaleGermGaloisCover (fun _ E => E.source) (fun _ E => toGermCover.{u, v, uL, z} E R hρ)
    (etaleGermCartan_local_lift R hρ href)

private def baseDiagramIso (y : localizedSpaceFunctor.obj X) :
    etaleNeighborhoodDiagram.{u, v, uL} X y (EtaleGermNeighborhood.base y).obj ≅
      nbhdEtale.{u, v, uL} X y :=
  NatIso.ofComponents (fun i => by
    let U := (nbhdOpen.{u, v, uL} X y).obj i
    let A := (EtaleGermNeighborhood.base y).obj
    let q := (restrictEtaleObject X U A).hom
    letI : IsIso A.hom := inferInstanceAs (IsIso (𝟙 X))
    letI : IsIso q := (isPullback_restrictEtale X U A).isIso_fst_of_isIso
    exact MorphismProperty.Over.isoMk (asIso q) rfl)
    (fun {_ j} _ => @Subsingleton.elim _
      (openEtaleObject_hom_subsingleton X _ ((nbhdOpen.{u, v, uL} X y).obj j)) _ _)

private def germEtaleBaseIso (y : localizedSpaceFunctor.obj X) :
    GaloisGerms.germ J R (nbhdEtale.{u, v, uL} X y) ≅
      etaleSectionGerm.{u, v, uL} R (EtaleGermNeighborhood.base y) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{max u (v + 1) uL} R))
    (Functor.isoWhiskerRight
      ((Functor.whiskeringLeft _ _ _).mapIso (NatIso.op (baseDiagramIso.{u, v, uL} y))) colim)

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

omit [T2Space (localizedSpaceFunctor.obj X)] in
/-- The requested local acyclicity follows from pointed Galois refinement
for the underlying analytic étale site. -/
theorem analyticEtaleGaloisCoinducedLocalAcyclic_of_pointedRefinements
    (href : HasPointedEtaleGaloisRefinements X) :
    AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ := by
  intro hX hρ S hS q
  have : T2Space (localizedSpaceFunctor.obj X) := hX
  have := etale_hasSheafify.{u, v, uL} X R
  have := etale_enoughInjectives.{u, v, uL} X R
  let F := ordinaryEtaleRestriction S
  apply (isZero_etaleUnderlyingHigherDirectImage_iff_germCohomology.{u, v, uL} X R F (q + 1)).2
  intro y
  have : ∀ V : EtaleGermNeighborhood X y, (etaleSectionGerm.{u, v, uL} R V).Additive :=
    fun V => inferInstanceAs ((GaloisGerms.germ J R
      (etaleNeighborhoodDiagram.{u, v, uL} X y V.obj)).Additive)
  have : ∀ V : EtaleGermNeighborhood X y,
      PreservesFiniteLimits (etaleSectionGerm.{u, v, uL} R V) :=
    fun V => inferInstanceAs (PreservesFiniteLimits (GaloisGerms.germ J R
      (etaleNeighborhoodDiagram.{u, v, uL} X y V.obj)))
  let C := etaleGermCartanSystem.{u, v, uL, z} (y := y) R hρ href
  have hA : C.GaloisAcyclic F :=
    fun V E n => isZero_groupCohomology_relativeGaloisGerm S hρ hS E n
  have hz := C.isZero_rightDerived_of_iso (EtaleGermNeighborhood.base y)
    (germEtaleBaseIso.{u, v, uL} R y) F hA q
  exact hz.of_iso ((germCohomologyIso.{u, v, uL} X R y (q + 1)).app F)

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
