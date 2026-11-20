import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.GroupScheme.IntegralModel.KernelCentralizerTorus
import Langlands.GroupScheme.KernelTriviality
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.ProperCocharacters
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # The cocharacters of a split semiabelian identity component -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Langlands.GroupScheme
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)

namespace GroupScheme.cocharacterLattice

/-- The cocharacters of the ambient field group are exactly those of its
represented identity component. -/
def ofRelativeIdentityComponent {G J : CommGroupScheme S} (i : J ⟶ G)
    (hi : IsRelativeIdentityComponent G.toGrp (CommGroupScheme.groupHom i)) :
    cocharacterLattice J ≃+ cocharacterLattice G := by
  let : Mono (CommGroupScheme.groupHom i).hom.hom := hi.mono_hom
  let : GeometricallyConnected (Gm S).X.hom := isSplitTorus_gm.geometricallyConnected
  refine AddEquiv.ofBijective (CommGroupScheme.postcompose i (Gm S)) ⟨?_, ?_⟩
  · intro f g h
    apply Additive.toMul.injective
    apply Grp.hom_ext
    apply (cancel_mono (CommGroupScheme.groupHom i).hom.hom).mp
    exact congrArg (fun v => (CommGroupScheme.groupHom v).hom.hom) h
  · intro f
    obtain ⟨g, hg⟩ := hi.exists_hom_lift (CommGroupScheme.groupHom f)
    exact ⟨Additive.ofMul g, congrArg Additive.ofMul hg⟩

end GroupScheme.cocharacterLattice

namespace AbelianScheme.SplitSemiabelianPresentation

variable {J : CommGroupScheme (Spec (CommRingCat.of k))} (P : SplitSemiabelianPresentation J)

/-- Cocharacters of a semiabelian group over a separably closed field are
exactly the cocharacters of its toric kernel. -/
def cocharacters [IsSepClosed k] :
    cocharacterLattice J ≃+ (ULift.{u} (Fin P.torusRank) → ℤ) := by
  let q := P.quotientMap
  let i := CommGroupScheme.kernelι q
  let e : cocharacterLattice (CommGroupScheme.kernel q) ≃+ cocharacterLattice J := by
    refine AddEquiv.ofBijective (CommGroupScheme.postcompose i (Gm S)) ⟨?_, ?_⟩
    · exact fun _ _ h => CommGroupScheme.kernel_hom_ext q h
    · intro f
      have hf : f ≫ q = 0 := cocharacter_eq_zero_of_isProper (f ≫ q)
      exact ⟨CommGroupScheme.kernelLift q f hf, CommGroupScheme.kernelLift_ι q f hf⟩
  exact e.symm.trans ((cocharacterLattice.congr P.torusIso.symm).trans
    (splitTorus.cocharacterLatticeEquiv k (ULift.{u} (Fin P.torusRank))))

/-- Over a separably closed field, the rational cocharacters of a group with
supplied semiabelian identity component have one coordinate for each torus factor. -/
def rationalCocharacters [IsSepClosed k] {G : CommGroupScheme S} (i : J ⟶ G)
    (hi : IsRelativeIdentityComponent G.toGrp (CommGroupScheme.groupHom i)) :
    (ℚ ⊗[ℤ] cocharacterLattice G) ≃ₗ[ℚ] (ULift.{u} (Fin P.torusRank) → ℚ) :=
  let e := ((cocharacterLattice.ofRelativeIdentityComponent i hi).symm.trans
    P.cocharacters).toIntLinearEquiv
  e.baseChange ℤ ℚ _ _ ≪≫ₗ TensorProduct.piScalarRight ℤ ℚ ℚ _

/-- The rational cocharacter module of the ambient group is finite dimensional. -/
theorem finite_rationalCocharacters [IsSepClosed k] (P : SplitSemiabelianPresentation J)
    {G : CommGroupScheme S} (i : J ⟶ G)
    (hi : IsRelativeIdentityComponent G.toGrp (CommGroupScheme.groupHom i)) :
    Module.Finite ℚ (ℚ ⊗[ℤ] cocharacterLattice G) :=
  let e := P.rationalCocharacters i hi
  Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- Its rational dimension equals the number of split torus factors. -/
theorem finrank_rationalCocharacters [IsSepClosed k] {G : CommGroupScheme S} (i : J ⟶ G)
    (hi : IsRelativeIdentityComponent G.toGrp (CommGroupScheme.groupHom i)) :
    Module.finrank ℚ (ℚ ⊗[ℤ] cocharacterLattice G) = P.torusRank := by
  rw [(P.rationalCocharacters i hi).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_ulift, Fintype.card_fin]

/-- When the torus rank is zero the semiabelian group is itself proper. -/
theorem isProper_of_torusRank_eq_zero (hr : P.torusRank = 0) : IsProper J.X.hom := by
  let q := CommGroupScheme.groupHom P.quotientMap
  let I := ULift.{u} (Fin P.torusRank)
  let : IsEmpty I := by
    dsimp [I]
    rw [hr]
    infer_instance
  let e : (splitTorus S I) ≅ (GroupScheme.kernel q) :=
    ⟨CommGroupScheme.groupHom P.torusIso.hom, CommGroupScheme.groupHom P.torusIso.inv,
      congrArg CommGroupScheme.groupHom P.torusIso.hom_inv_id,
      congrArg CommGroupScheme.groupHom P.torusIso.inv_hom_id⟩
  let e₀ := e.symm ≪≫ Pi.reindex (Equiv.equivPEmpty I)
    (fun _ : PEmpty.{u + 1} => (Gm S).toGrp) ≪≫ (trivialSplitTorusIso S).symm
  have he : IsIso e₀.hom.hom.hom.left :=
    ((Grp.forget (Over S)) ⋙ Over.forget S).map_isIso e₀.hom
  let : IsIso (GroupScheme.kernel q).X.hom := by
    rw [← Over.w e₀.hom.hom.hom]
    let : IsIso (Grp.trivial (Over S)).X.hom := by
      change IsIso (𝟙 S)
      infer_instance
    infer_instance
  let : Mono q.hom.hom := GroupScheme.mono_of_kernel_hom_isIso q
  let : Smooth q.hom.hom.left := P.smooth
  let : Surjective q.hom.hom.left := P.surjective
  let : IsOpenImmersion q.hom.hom.left := IsOpenImmersion.of_flat_of_mono _
  let : IsIso q.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  rw [← Over.w q.hom.hom]
  infer_instance

end AbelianScheme.SplitSemiabelianPresentation
end Langlands
