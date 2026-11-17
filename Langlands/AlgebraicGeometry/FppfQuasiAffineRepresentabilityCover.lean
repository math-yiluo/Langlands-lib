import Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Langlands.AlgebraicGeometry.QuasiAffineCoverDescent

/-! # Quasi-affine representability from finite affine fppf covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Quasi-affine representatives over a finite affine fppf covering family
produce a quasi-affine representative over an affine base. -/
theorem exists_quasiAffine_representation_of_finite_cover
    {S : Scheme.{u}} [IsAffine S] {F : Presheaf S}
    (hF : Presheaf.IsSheaf (fppfTopology S) F)
    {I : Type u} [Finite I] (B : I → Scheme.{u}) (q : ∀ i, B i ⟶ S)
    [∀ i, IsAffine (B i)] [∀ i, Flat (q i)]
    [∀ i, LocallyOfFinitePresentation (q i)]
    (hq : ∀ s : S, ∃ i, ∃ b : B i, q i b = s)
    (H : ∀ i, Over (B i))
    (e : ∀ i, (schemeYoneda (B i)).obj (H i) ≅ (Over.map (q i)).op ⋙ F)
    (hH : ∀ i, (H i).left.IsQuasiAffine) :
    ∃ V : Over S, V.left.IsQuasiAffine ∧ Nonempty ((schemeYoneda S).obj V ≅ F) := by
  classical
  let b : (∐ B) ⟶ S := Sigma.desc q
  let F' : Presheaf (∐ B) := (Over.map b).op ⋙ F
  have hF' : Presheaf.IsSheaf (fppfTopology (∐ B)) F' :=
    ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) b).obj ⟨F, hF⟩).property
  let e' (i : I) : (schemeYoneda (B i)).obj (H i) ≅
      (Over.map (Sigma.ι B i)).op ⋙ F' :=
    e i ≪≫ ((Functor.associator (Over.map (Sigma.ι B i)).op (Over.map b).op F).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (Over.mapComp (Sigma.ι B i) b)) F ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (Over.mapCongr ((Sigma.ι B i) ≫ b) (q i)
          (Sigma.ι_comp_desc q i))).symm F).symm
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation hF' (sigmaOpenCover B) H e'
  have (i : I) : (pullback V.hom (Sigma.ι B i)).IsQuasiAffine := by
    let d := LocalRepresentation.localRepresentativeIso (Sigma.ι B i) V eV (H i) (e' i)
    let : (H i).left.IsQuasiAffine := hH i
    exact Scheme.IsQuasiAffine.of_isAffineHom d.hom.left
  have : V.left.IsQuasiAffine :=
    QuasiAffineCoverDescent.isQuasiAffine_of_finite_affine_cover V.hom B (Sigma.ι B)
      (fun s => (sigmaOpenCover B).exists_eq s)
  have : Flat b := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstanceAs (Flat (q i))
  have : LocallyOfFinitePresentation b :=
    IsZariskiLocalAtSource.sigmaDesc fun i => inferInstanceAs (LocallyOfFinitePresentation (q i))
  have : Surjective b := by
    constructor
    intro s
    obtain ⟨i, x, rfl⟩ := hq s
    exact ⟨Sigma.ι B i x, by simp [b, ← Scheme.Hom.comp_apply]⟩
  let r : F'.RepresentableBy V :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eV
  let D := quasiAffineModel (π := b) r hF
  exact ⟨D.val, D.property.1,
    ⟨(Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (Classical.choice D.property.2)⟩⟩

/-- Choose the quasi-affine model obtained from a finite affine fppf family. -/
def quasiAffineModelOfFiniteCover
    {S : Scheme.{u}} [IsAffine S] {F : Presheaf S}
    (hF : Presheaf.IsSheaf (fppfTopology S) F)
    {I : Type u} [Finite I] (B : I → Scheme.{u}) (q : ∀ i, B i ⟶ S)
    [∀ i, IsAffine (B i)] [∀ i, Flat (q i)]
    [∀ i, LocallyOfFinitePresentation (q i)]
    (hq : ∀ s : S, ∃ i, ∃ b : B i, q i b = s)
    (H : ∀ i, Over (B i))
    (e : ∀ i, (schemeYoneda (B i)).obj (H i) ≅ (Over.map (q i)).op ⋙ F)
    (hH : ∀ i, (H i).left.IsQuasiAffine) :
    {V : Over S // V.left.IsQuasiAffine ∧ Nonempty ((schemeYoneda S).obj V ≅ F)} :=
  ⟨_, (exists_quasiAffine_representation_of_finite_cover hF B q hq H e hH).choose_spec⟩

end Langlands.AlgebraicGeometry.FppfQuasiAffineRepresentabilityDescent
