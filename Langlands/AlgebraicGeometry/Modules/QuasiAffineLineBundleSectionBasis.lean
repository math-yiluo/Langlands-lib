import Langlands.AlgebraicGeometry.Modules.LineBundlePrincipalSectionExtension
import Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineProof
import Langlands.AlgebraicGeometry.Modules.SectionCoefficients
import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusProof
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Generation opens of a fixed line bundle on a quasi-affine scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule.QuasiAffineSectionBasis

open SectionClearing

variable {X : Scheme.{u}} (L : LineBundle X)

/-- A global section generates on any chart where its coordinate is a unit. -/
theorem le_trivializationOpen_of_chart_unit {T U : X.Opens}
    (e : L.obj.restrict T.ι ≅ structureModule T.toScheme) (hU : U ≤ T)
    (s : GlobalSections L.obj)
    (hu : IsUnit (chartE e U hU (sectionRes L.obj s U))) :
    U ≤ trivializationOpen L.obj s := by
  apply le_trivializationOpen_of_bijective
  intro V hVU
  let c := chartE e V (hVU.trans hU) (sectionRes L.obj s V)
  have hc : IsUnit c := by
    have he := chartE_res e U V hU hVU (sectionRes L.obj s U)
    rw [sectionRes_res] at he
    change IsUnit (chartE e V (hVU.trans hU) (sectionRes L.obj s V))
    rw [he]
    exact hu.map (X.presheaf.map (homOfLE hVU).op).hom
  have key (a : Γ(X, V)) :
      chartE e V (hVU.trans hU) ((sectionHom L.obj s).app V a) = a * c := by
    rw [LineBundleDescent.sectionHom_app, chartE_smul]
  have hmul : Function.Bijective (fun a : Γ(X, V) => a * c) := by
    obtain ⟨v, hv⟩ := hc
    rw [← hv]
    exact (Units.mulRight v).bijective
  refine ⟨fun a b hab => hmul.injective ?_, fun b => ?_⟩
  · rw [← key a, ← key b, hab]
  · obtain ⟨a, ha⟩ := hmul.surjective (chartE e V (hVU.trans hU) b)
    refine ⟨a, (Function.LeftInverse.injective (chartF_chartE e V (hVU.trans hU))) ?_⟩
    exact (key a).trans ha

/-- A global principal open contained in a bundle chart is the exact generation
open of a global section of that same bundle. -/
theorem exists_section_basicOpen [CompactSpace X] [QuasiSeparatedSpace X]
    {T : X.Opens} (e : L.obj.restrict T.ι ≅ structureModule T.toScheme)
    (f : Γ(X, ⊤)) (hf : X.basicOpen f ≤ T) :
    ∃ s : GlobalSections L.obj, trivializationOpen L.obj s = X.basicOpen f := by
  let D := X.basicOpen f
  let fD := X.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op f
  let q := chartF e D hf (1 : Γ(X, D))
  obtain ⟨n, t, ht⟩ := PrincipalSectionExtension.exists_global L f q
  have hcoord : chartE e D hf (sectionRes L.obj t D) = fD ^ n := by
    change chartE e D hf (L.obj.presheaf.map (homOfLE le_top).op t) = _
    rw [ht, chartE_smul, chartE_chartF, mul_one]
  have hDt : D ≤ trivializationOpen L.obj t :=
    le_trivializationOpen_of_chart_unit L e hf t (hcoord ▸
      (X.toRingedSpace.isUnit_res_basicOpen f).pow n)
  let z := tensorSection (structureModule X) L.obj f t
  let s := (tensorLeftUnitor L.obj).hom.app ⊤ z
  refine ⟨s, ?_⟩
  change trivializationOpen L.obj ((tensorLeftUnitor L.obj).hom.app ⊤ z) = D
  rw [trivializationOpen_mapIso]
  change trivializationOpen (tensorObj (LineBundle.trivial X).obj L.obj)
    (tensorSection (LineBundle.trivial X).obj L.obj f t) = D
  rw [tensorSectionGenerationLocus X (LineBundle.trivial X) L f t]
  change trivializationOpen (structureModule X) f ⊓ trivializationOpen L.obj t = D
  rw [trivializationOpen_structureModule]
  exact inf_eq_left.mpr hDt

/-- A chosen global section whose exact generation open is a principal open
contained in the given bundle chart. -/
def sectionOnBasicOpen [CompactSpace X] [QuasiSeparatedSpace X]
    {T : X.Opens} (e : L.obj.restrict T.ι ≅ structureModule T.toScheme)
    (f : Γ(X, ⊤)) (hf : X.basicOpen f ≤ T) :
    {s : GlobalSections L.obj // trivializationOpen L.obj s = X.basicOpen f} :=
  ⟨(exists_section_basicOpen L e f hf).choose,
    (exists_section_basicOpen L e f hf).choose_spec⟩

/-- The generation opens of global sections of a fixed line bundle form a basis
on a quasi-affine scheme. -/
theorem isBasis [Scheme.IsQuasiAffine X] :
    Opens.IsBasis (Set.range (trivializationOpen L.obj)) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.property x
  obtain ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, hxf, hsub⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open
      (show x ∈ T ⊓ U from ⟨hxT, hxU⟩) (T ⊓ U).2
  obtain ⟨s, hs⟩ := exists_section_basicOpen L e f (hsub.trans inf_le_left)
  exact ⟨trivializationOpen L.obj s, ⟨s, rfl⟩, hs ▸ hxf,
    hs.symm ▸ hsub.trans inf_le_right⟩

end Langlands.SchemeModule.QuasiAffineSectionBasis
