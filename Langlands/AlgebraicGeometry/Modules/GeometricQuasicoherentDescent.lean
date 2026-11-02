import Langlands.AlgebraicGeometry.Modules.GeometricModuleEffectivity
import Langlands.AlgebraicGeometry.Modules.GeometricModuleDescent
import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatQuasicoherentDescent
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessDescent

/-! # Effective geometric descent with quasi-coherence and relative flatness -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules.GeometricQuasicoherentDescent

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- An effective structure on the base gives its actual pullback isomorphism. -/
def pullbackIsoOfStr {M : Y.Modules} (S : Str D (𝟙 Y) M) :
    (Scheme.Modules.pullback p).obj M ≅ F :=
  S.γ X (𝟙 X) p (by simp) ≪≫ (Scheme.Modules.pullbackId X).app F

/-- Every effective structure for a quasi-coherent cocycle has a quasi-coherent module,
on every base test. -/
lemma isQuasicoherent_of_str [IsAffineHom p] [Flat p] [Surjective p]
    [F.IsQuasicoherent] {T : Scheme.{u}} {t : T ⟶ Y} {N : T.Modules}
    (S : Str D t N) : N.IsQuasicoherent := by
  let q := pullback.snd p t
  have : IsAffineHom q :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback p t) inferInstance
  let e := S.γ _ (pullback.fst p t) q pullback.condition.symm
  have : ((Scheme.Modules.pullback q).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback p t).ringCatSheaf).prop_of_iso
      e.symm inferInstance
  exact isQuasicoherent_of_pullback_of_affine_flat_surjective q N

/-- Every geometric quasi-coherent cocycle along an affine flat surjection is effective
over every base test scheme. -/
lemma exists_str [IsAffineHom p] [Flat p] [Surjective p] [F.IsQuasicoherent]
    {T : Scheme.{u}} (t : T ⟶ Y) :
    ∃ N : T.Modules, N.IsQuasicoherent ∧ Nonempty (Str D t N) := by
  obtain ⟨M, ⟨S⟩⟩ := GeometricModuleEffectivity.exists_str D
  let S' := S.restrict t t (by simp)
  exact ⟨_, isQuasicoherent_of_str D S', ⟨S'⟩⟩

/-- The isomorphism compatible with two effective structures is unique, with
quasi-coherence supplied by the structures themselves. -/
lemma existsUnique_iso [IsAffineHom p] [Flat p] [Surjective p] [F.IsQuasicoherent]
    {T : Scheme.{u}} {t : T ⟶ Y} {N N' : T.Modules}
    (S : Str D t N) (S' : Str D t N') :
    ∃! e : N ≅ N', Str.Hom S S' e.hom := by
  have : N'.IsQuasicoherent := isQuasicoherent_of_str D S'
  exact GeometricModuleDescent.existsUnique_iso D S S'

/-- Relative stalk flatness of a cocycle over a fixed base descends to every effective
module on the original base. -/
lemma isFlatOver_of_str [Flat p] [Surjective p] {B : Scheme.{u}} (f : Y ⟶ B)
    {M : Y.Modules} (S : Str D (𝟙 Y) M) (hF : IsFlatOver (p ≫ f) F) :
    IsFlatOver f M := by
  apply isFlatOver_of_pullback_flat_surjective p f M
  exact (isFlatOver_iff_of_iso (p ≫ f) (pullbackIsoOfStr D S)).mpr hF

/-- In a Cartesian base-change square with flat surjective base map, relative flatness
of the cover module descends to every effective module. -/
lemma isFlatOver_of_str_of_isPullback
    {B T : Scheme.{u}} {f : Y ⟶ B} {g : T ⟶ B} {q : X ⟶ T}
    (H : IsPullback p q f g) [Flat g] [Surjective g]
    {M : Y.Modules} (S : Str D (𝟙 Y) M) (hF : IsFlatOver q F) :
    IsFlatOver f M := by
  have : Flat p := MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective p := MorphismProperty.of_isPullback H.flip inferInstance
  apply isFlatOver_of_str D f S
  rw [H.w]
  exact isFlatOver_comp_of_flat q g F hF

end Langlands.AlgebraicGeometry.Modules.GeometricQuasicoherentDescent
