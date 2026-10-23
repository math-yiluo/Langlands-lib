import Langlands.AlgebraicGeometry.Modules.UnitEndResidueStalkStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}}

private noncomputable def scalarValue (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) : Γ(X, U) := φ.app U (1 : Γ(X, U))

private lemma scalar_app (φ : structureModule X ⟶ structureModule X)
    (U : X.Opens) (a : Γ(X, U)) :
    φ.app U a = a * scalarValue φ U := by
  have h := φ.app_smul a (1 : Γ(X, U))
  change φ.app U (a * 1 : Γ(X, U)) = a * scalarValue φ U at h
  simpa only [mul_one] using h

private lemma scalar_res (φ : structureModule X ⟶ structureModule X)
    {U V : X.Opens} (i : U ⟶ V) :
    X.presheaf.map i.op (scalarValue φ V) = scalarValue φ U := by
  have h := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) (1 : Γ(X, V))
  change φ.app U (X.presheaf.map i.op (1 : Γ(X, V))) = X.presheaf.map i.op (scalarValue φ V) at h
  rw [map_one] at h
  exact h.symm

private lemma scalar_restrict_isIso (φ : structureModule X ⟶ structureModule X)
    (V : X.Opens) (h : IsUnit (scalarValue φ V)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso (φ.app (V.ι ''ᵁ W))
  let i : (V.ι ''ᵁ W) ⟶ V := homOfLE (by
    rintro z ⟨y, _, rfl⟩
    exact y.2)
  have hu := h.map (X.presheaf.map i.op).hom
  rw [scalar_res] at hu
  obtain ⟨r, hr⟩ := hu
  rw [ConcreteCategory.isIso_iff_bijective]
  change @Function.Bijective Γ(X, V.ι ''ᵁ W) Γ(X, V.ι ''ᵁ W)
    (fun a ↦ φ.app (V.ι ''ᵁ W) a)
  simp only [scalar_app, ← hr]
  exact ⟨fun a b hab ↦ (Units.mul_left_inj r).mp hab,
    fun a ↦ ⟨a * ↑r⁻¹, by simp [mul_assoc]⟩⟩

/-- For a scalar endomorphism, invertibility on an abelian-group stalk is
    equivalent to nonzero residue of its value at one. -/
theorem unitEnd_stalkIso_iff_residue_ne_zero
    (φ : structureModule X ⟶ structureModule X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ↔
      X.Γevaluation x (φ.app ⊤ (1 : Γ(X, ⊤))) ≠ 0 := by
  constructor
  · intro hx
    let V : X.Opens := ⟨_, isOpen_unitEnd_stalkIso φ⟩
    have hxV : x ∈ V := hx
    have hV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
      rw [isIso_iff_stalk_isIso]
      intro y
      exact (isIso_stalk_restrict_iff φ V y).mpr y.2
    let W : X.Opens := V.ι ''ᵁ (⊤ : V.toScheme.Opens)
    have hxW : x ∈ W := ⟨⟨x, hxV⟩, by trivial, rfl⟩
    have hW : IsIso (φ.app W) :=
      Scheme.Modules.Hom.isIso_iff_isIso_app.mp hV ⊤
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (φ.app W)).surjective
      (1 : Γ(X, W))
    rw [scalar_app] at ha
    have hu : IsUnit (scalarValue φ W) :=
      IsUnit.of_mul_eq_one _ (by simpa only [mul_comm] using ha)
    have hg := hu.map (X.presheaf.germ W x hxW).hom
    rw [← scalar_res φ (homOfLE (show W ≤ ⊤ from le_top)),
      X.presheaf.germ_res_apply] at hg
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hg
  · intro hx
    have hg : IsUnit (X.presheaf.germ ⊤ x trivial (scalarValue φ ⊤)) :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hx
    obtain ⟨V, i, hxV, hV⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ
      ⊤ (scalarValue φ ⊤) x trivial hg
    rw [scalar_res] at hV
    have := scalar_restrict_isIso φ V hV
    exact (isIso_stalk_restrict_iff φ V ⟨x, hxV⟩).mp (by infer_instance)

/-- The exact scalar residue/stalk criterion. -/
theorem unitEndResidueStalkCriterion : UnitEndResidueStalkCriterion.{u} := by
  intro X φ x
  exact unitEnd_stalkIso_iff_residue_ne_zero φ x

end Langlands.SchemeModule
