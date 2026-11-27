import Langlands.Geometry.Analytic.EquivariantEtaleBaseChangeMorphismStatement
import Langlands.Sheaf.Equivariant.AnalyticEtaleToCompactProbe.Statement
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleDerived

/-! # Evaluation on a quasi-étale object after change of site -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Topology (TopologicalGroup)

universe u v z uR

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section EtaleBaseChange

variable {Y Z : SpaceWithOperators.{u, v, v, z} K} (f : Y ⟶ Z)

local notation "F" => SpaceWithOperators.etalePullbackFunctor f
local notation "projection" => SpaceWithOperators.etalePullbackProjection f
local notation "forgetZ" => GSpace.forget (K := K) (G := Z.group.carrier)
local notation "forgetY" => GSpace.forget (K := K) (G := Y.group.carrier)

private theorem pullbackProjection_naturality {A B : EquivariantEtaleSite Z.space}
    (a : A ⟶ B) :
    (forgetY).map (projection A) ≫ (forgetZ).map a.left =
      (forgetY).map ((F).map a).left ≫ (forgetY).map (projection B) := by
  change (forgetY).map (projection A) ≫ (forgetY).map ((GSpace.res f.groupHom).map a.left) = _
  rw [← (forgetY).map_comp, ← (forgetY).map_comp]
  simp [SpaceWithOperators.etalePullbackFunctor, SpaceWithOperators.etalePullbackProjection]

private theorem pullbackOfEtaleArrow {A B : EquivariantEtaleSite Z.space} (a : A ⟶ B) :
    IsPullback ((forgetY).map (projection A)) ((forgetY).map ((F).map a).left)
      ((forgetZ).map a.left) ((forgetY).map (projection B)) := by
  apply IsPullback.of_bot _ (pullbackProjection_naturality f a)
    (SpaceWithOperators.isPullback_etalePullbackFunctor f B)
  simpa only [← (forgetY).map_comp, ← (forgetZ).map_comp, MorphismProperty.Over.w] using
    SpaceWithOperators.isPullback_etalePullbackFunctor f A

private theorem etaleBaseChange_preservesPullback {P A B T : EquivariantEtaleSite Z.space}
    {a : A ⟶ T} {b : B ⟶ T} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback ((forgetZ).map p.left) ((forgetZ).map q.left)
      ((forgetZ).map a.left) ((forgetZ).map b.left)) :
    IsPullback ((forgetY).map ((F).map p).left) ((forgetY).map ((F).map q).left)
      ((forgetY).map ((F).map a).left) ((forgetY).map ((F).map b).left) := by
  have h' := (pullbackOfEtaleArrow f q).paste_horiz h
  rw [pullbackProjection_naturality f p, pullbackProjection_naturality f b] at h'
  have hpq : p ≫ a = q ≫ b := by
    ext
    exact h.w
  have hpq' := congrArg (fun k => (forgetY).map ((F).map k).left) hpq
  simp only [Functor.map_comp, MorphismProperty.Comma.comp_left] at hpq'
  exact h'.of_right hpq' (pullbackOfEtaleArrow f a)

private theorem etaleBaseChange_preservesCover {B : EquivariantEtaleSite Z.space}
    {S : Presieve B} (hS : S ∈ equivariantEtalePrecoverage Z.space B) :
    S.map F ∈ equivariantEtalePrecoverage Y.space ((F).obj B) := by
  rw [mem_equivariantEtalePrecoverage_iff] at hS ⊢
  intro x
  obtain ⟨A, a, ha, y, hy⟩ := hS (localizedSpaceFunctor.map ((forgetY).map (projection B)) x)
  obtain ⟨z, -, hz⟩ := exists_point_of_isPullback_of_etale (pullbackOfEtaleArrow f a)
    (EquivariantEtaleSite.etale_map_left a) y x hy
  exact ⟨(F).obj A, (F).map a, ⟨ha⟩, z, hz⟩

private theorem etaleBaseChange_isContinuous :
    (F).IsContinuous (equivariantEtaleTopology Z.space) (equivariantEtaleTopology Y.space) := by
  exact (GSpace.representablyFlat_and_isContinuous_of_isPullback_forget F
    (fun _ _ _ a b => EquivariantEtaleSite.exists_analyticPullback a b)
    (fun _ _ _ _ _ _ _ _ h => etaleBaseChange_preservesPullback f h)
    (fun A hA => by
      let B := (EquivariantEtaleSite.res f.groupHom).obj A
      have : IsIso B.hom := inferInstanceAs (IsIso ((GSpace.res f.groupHom).map A.hom))
      change IsIso (pullback.snd B.hom (SpaceWithOperators.restrictedHom f))
      infer_instance)
    (equivariantEtalePrecoverage Z.space) (equivariantEtalePrecoverage Y.space)
    (fun _ _ h => etaleBaseChange_preservesCover f h)).2

variable (R : Type (max u (v + 1) z uR)) [CommRing R]

private theorem equivariantEtale_locallySmall (X : SpaceWithOperators.{u, v, v, z} K) :
    LocallySmall.{max u (v + 1) z uR} (EquivariantEtaleSite X.space) :=
  ⟨fun V W => small_lift.{max u (v + 1), max z uR, max u (v + 1)} (V ⟶ W)⟩

private theorem equivariantEtale_essentiallySmall (X : SpaceWithOperators.{u, v, v, z} K) :
    EssentiallySmall.{max u (v + 1) z uR} (EquivariantEtaleSite X.space) := by
  let : Small.{max u (v + 1) z uR} (EquivariantEtaleSite X.space) :=
    small_lift.{max u (v + 1) z, uR, max u (v + 1) z} _
  let := equivariantEtale_locallySmall.{u, v, z, uR} X
  exact essentiallySmall_of_small_of_locallySmall _

/-- Inverse image of module sheaves along the actual equivariant étale base change. -/
def equivariantEtaleBaseChangeInverseImage :
    Sheaf (equivariantEtaleTopology Z.space) (ModuleCat R) ⥤
      Sheaf (equivariantEtaleTopology Y.space) (ModuleCat R) := by
  let := equivariantEtale_locallySmall.{u, v, z, uR} Y
  let := equivariantEtale_essentiallySmall.{u, v, z, uR} Y
  let := equivariantEtale_essentiallySmall.{u, v, z, uR} Z
  let := hasSheafifyEssentiallySmallSite (equivariantEtaleTopology Y.space) (ModuleCat R)
  let := hasSheafifyEssentiallySmallSite (equivariantEtaleTopology Z.space) (ModuleCat R)
  let := etaleBaseChange_isContinuous f
  exact Langlands.Sheaf.SiteDirectImage.inverseImage F R
    (equivariantEtaleTopology Z.space) (equivariantEtaleTopology Y.space)

end EtaleBaseChange

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : GSpace.{u, v, v} K G) (R : Type (max u (v + 1) z uR)) [CommRing R]

local notation "ofSpace" => SpaceWithOperators.ofGSpace (K := K) (TopologicalGroup.of G)

private abbrev etaleIdentity (V : GSpace.{u, v, v} K G) : EquivariantEtaleSite V :=
  MorphismProperty.Over.mk ⊤ (𝟙 V) (GSpace.etale.id_mem V)

/-- On an equivariant quasi-étale object the inverse image of an étale sheaf
has the same sections as the étale pullback evaluated on its identity object. -/
def EquivariantQuasiEtaleObjectEvaluationStatement : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    ∀ U : EquivariantQuasiEtaleSite X,
      Nonempty (equivariantEtaleBaseChangeInverseImage.{u, v, z, uR} ((ofSpace).map U.hom) R ⋙
          (sheafSections (equivariantEtaleTopology U.left) (ModuleCat R)).obj (op (etaleIdentity U.left)) ≅
        equivariantEtaleToCompactProbeInverseImage.{u, v, z, uR} X R ⋙
          (sheafSections (equivariantCompactProbeQuasiEtaleTopology X) (ModuleCat R)).obj (op U))

end Langlands.Sheaf.Equivariant.Analytic
