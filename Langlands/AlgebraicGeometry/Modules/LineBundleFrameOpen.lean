import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpenStatement

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

noncomputable def unitEndCoefficient (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) : Γ(X, U) := φ.app U (1 : Γ(X, U))

lemma unitEndCoefficient_app (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) : φ.app U a = a * (unitEndCoefficient φ U) := by
  have h := φ.app_smul a (1 : Γ(X, U))
  change φ.app U ((a * 1 : Γ(X, U))) = a * unitEndCoefficient φ U at h
  simpa using h

lemma unitEnd_naturality (φ : structureModule X ⟶ structureModule X)
    {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) :
    φ.app U (X.presheaf.map i.op a) = X.presheaf.map i.op (φ.app V a) := by
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) a)

lemma unitEnd_app_isIso (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) (h : IsUnit (unitEndCoefficient φ U)) : IsIso (φ.app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain ⟨r, hr⟩ := h
  have he : (fun a : Γ(X, U) ↦ φ.app U a) = fun a : Γ(X, U) ↦ a * (r : Γ(X, U)) := by
    funext a
    rw [unitEndCoefficient_app, hr]
  change @Function.Bijective Γ(X, U) Γ(X, U) (fun a ↦ φ.app U a)
  rw [he]
  exact ⟨fun a b h ↦ (Units.mul_left_inj r).mp h,
    fun a ↦ ⟨a * ↑r⁻¹, by simp [mul_assoc]⟩⟩

lemma unitEnd_localUnit (φ : structureModule X ⟶ structureModule X) (x : X)
    [IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)] :
    ∃ V : X.Opens, x ∈ V ∧ IsUnit (unitEndCoefficient φ V) := by
  let P := (structureModule X).presheaf
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)).surjective
      (P.germ ⊤ x trivial (1 : Γ(X, ⊤)))
  obtain ⟨U, hxU, a, ha⟩ := P.exists_germ_eq b
  change Γ(X, U) at a
  rw [← ha, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hb
  obtain ⟨V, hxV, iU, iT, he⟩ := P.germ_eq x hxU (by trivial) _ _ hb
  have he' : φ.app V (X.presheaf.map iU.op a) = (1 : Γ(X, V)) := by
    rw [unitEnd_naturality]
    change X.presheaf.map iU.op (φ.app U a) = X.presheaf.map iT.op (1 : Γ(X, ⊤)) at he
    simpa only [map_one] using he
  refine ⟨V, hxV, ?_⟩
  rw [unitEndCoefficient_app, mul_comm] at he'
  exact IsUnit.of_mul_eq_one _ he'

lemma unitEnd_restrict_isIso (φ : structureModule X ⟶ structureModule X)
    (V : X.Opens) (h : IsUnit (unitEndCoefficient φ V)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso (φ.app (V.ι ''ᵁ W))
  apply unitEnd_app_isIso
  let i : (V.ι ''ᵁ W) ⟶ V := homOfLE (by
    rintro z ⟨y, _, rfl⟩
    exact y.2)
  have he : unitEndCoefficient φ (V.ι ''ᵁ W) = X.presheaf.map i.op (unitEndCoefficient φ V) := by
    have he := unitEnd_naturality φ i (1 : Γ(X, V))
    rw [map_one] at he
    exact he
  rw [he]
  exact h.map (X.presheaf.map i.op).hom

/-- The locus where an endomorphism of the structure module is a stalk isomorphism is open. -/
theorem isOpen_unitEnd_stalkIso (φ : structureModule X ⟶ structureModule X) :
    IsOpen {x : X | IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) := hx
  obtain ⟨V, hxV, hV⟩ := unitEnd_localUnit φ x
  refine ⟨V, ?_, V.isOpen, hxV⟩
  intro y hy
  have := unitEnd_restrict_isIso φ V hV
  exact (isIso_stalk_restrict_iff φ V ⟨y, hy⟩).mp (by infer_instance)

open Langlands.AlgebraicGeometry.Picard

/-- The stalk-frame condition for a section of a line bundle is open. -/
theorem isOpen_lineBundle_stalkFrame (L : LineBundle X) (s : GlobalSections L.obj) :
    IsOpen {x : X | IsStalkFrame L.obj s x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.property x
  let φ := sectionHom L.obj s
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e.hom
  have hψ (y : U.toScheme) :
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ.mapPresheaf) ↔
        IsStalkFrame L.obj s (U.ι y) := by
    change IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ) ↔ _
    simp only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff φ U y
  let W : U.toScheme.Opens := ⟨_, isOpen_unitEnd_stalkIso ψ⟩
  refine ⟨(U.ι ''ᵁ W : X.Opens), ?_, (U.ι ''ᵁ W).isOpen, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hψ z).mp hz
  · exact ⟨⟨x, hxU⟩, (hψ ⟨x, hxU⟩).mpr hx, rfl⟩

/-- For a line bundle, the whole stalk-frame set is the trivialization open. -/
theorem lineBundle_stalkFrame_set_eq (L : LineBundle X) (s : GlobalSections L.obj) :
    {x : X | IsStalkFrame L.obj s x} = (trivializationOpen L.obj s : Set X) := by
  rw [trivializationOpenInterior X L.obj s, (isOpen_lineBundle_stalkFrame L s).interior_eq]

/-- Openness and the full trivialization-locus comparison for line-bundle stalk frames. -/
theorem lineBundleStalkFrameOpen : LineBundleStalkFrameOpen.{u} := by
  intro X L s
  exact ⟨isOpen_lineBundle_stalkFrame L s, lineBundle_stalkFrame_set_eq L s⟩

end Langlands.SchemeModule
