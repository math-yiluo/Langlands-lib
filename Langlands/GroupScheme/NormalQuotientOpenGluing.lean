import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.NormalQuotientGroup
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Gluing affine normal quotients over an open cover of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

/-- The full kernel condition gives the exact right-coset fibers on every test. -/
theorem fibers {S : Scheme.{u}} {G Q : GroupScheme S} {H : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient H q)
    (T : Over S) (x y : T ⟶ G.X) :
    x ≫ q.hom.hom = y ≫ q.hom.hom ↔ x⁻¹ * y ∈ H.carrier T := by
  rw [← hq.2.2.2, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
    inv_mul_eq_one]

end RelativeRoot.IsFppfQuotient

namespace NormalQuotient

variable {S S' : Scheme.{u}}

/-- Restriction of a scheme presentation uses the actual pullback of its source. -/
def restrictedPresentation (b : S' ⟶ S) {W : Over S} {F : Presheaf S}
    (a : (schemeYoneda S).obj W ⟶ F) :
    (schemeYoneda S').obj ((Over.pullback b).obj W) ⟶ (Over.map b).op ⋙ F :=
  (schemeYonedaBaseChangeIso b W).hom ≫ Functor.whiskerLeft (Over.map b).op a

/-- A locally surjective presentation remains so over every change of base. -/
theorem restrictedPresentation_locallySurjective
    (b : S' ⟶ S) {W : Over S} {F : Presheaf S}
    (a : (schemeYoneda S).obj W ⟶ F)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S')
      (restrictedPresentation b a) := by
  let := ha
  have := CategoryTheory.Presheaf.isLocallySurjective_whisker
    (fppfTopology S') (fppfTopology S) (Over.map b) a
  unfold restrictedPresentation
  infer_instance

/-- A local fppf quotient with the same all-test fibers represents the restriction
of the original quotient sheaf, compatibly with the quotient map. -/
theorem exists_restriction_iso
    (b : S' ⟶ S) {W : Over S} {F : FppfSheaf S}
    (a : (schemeYoneda S).obj W ⟶ F.obj)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a)
    {Q : Over S'} (q : (Over.pullback b).obj W ⟶ Q)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hker : ∀ (T : Over S') (x y : T ⟶ (Over.pullback b).obj W),
      (restrictedPresentation b a).app (op T) ⟨x⟩ =
          (restrictedPresentation b a).app (op T) ⟨y⟩ ↔
        x ≫ q = y ≫ q) :
    ∃ e : (schemeYoneda S').obj Q ≅ (Over.map b).op ⋙ F.obj,
      (schemeYoneda S').map q ≫ e.hom = restrictedPresentation b a := by
  let F' : FppfSheaf S' :=
    ⟨(Over.map b).op ⋙ F.obj,
      (Over.map b).op_comp_isSheaf (fppfTopology S') (fppfTopology S) F⟩
  exact exists_iso_of_locallySurjective_of_same_kernel
    (F := F') (restrictedPresentation b a) q
    (restrictedPresentation_locallySurjective b a ha)
    (isLocallySurjective_schemeYoneda_map q) hker

/-- Affine normal quotient schemes supplied on an open base cover glue to an
actual affine fppf group quotient over the whole base. -/
theorem exists_affine_fppfQuotient_of_openCover
    {G N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.OpenCover.{u} S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M),
      IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  let R := HomogeneousQuotientFromEmbedding.arrowSpace i
  let s := HomogeneousQuotientFromEmbedding.source i
  let t := HomogeneousQuotientFromEmbedding.target i
  let h := HomogeneousQuotientFromEmbedding.isEquivalenceRelation i
  have hgeom := smoothRelationQuotient S G.X R s t h
    (HomogeneousQuotientFromEmbedding.hasSmoothProjections i hN) inferInstance
  let F : FppfSheaf S := ⟨(quotientSheaf R s t h).obj, hgeom.1⟩
  let a : (schemeYoneda S).obj G.X ⟶ F.obj := quotientMap R s t h
  have ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a :=
    CategoryTheory.Presheaf.isLocallySurjective_of_le
      (Langlands.AlgebraicGeometry.Sites.etaleTopologyOver_le_fppfTopologyOver S) a
      (isLocallySurjective_quotientMap R s t h)
  have hfib : ∀ (T : Over S) (x y : T ⟶ G.X),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T := by
    intro T x y
    exact (quotientMap_eq_iff R s t h ⟨x⟩ ⟨y⟩).trans
      (HomogeneousQuotientFromEmbedding.relation_iff i T x y)
  have hlocal : ∀ j,
      ∃ e : (schemeYoneda (𝒰.X j)).obj (Q j).X ≅ (Over.map (𝒰.f j)).op ⋙ F.obj,
        (schemeYoneda (𝒰.X j)).map (q j).hom.hom ≫ e.hom =
          restrictedPresentation (𝒰.f j) a := by
    intro j
    let := (hq j).1
    let := (hq j).2.1
    let := (hq j).2.2.1
    apply exists_restriction_iso (𝒰.f j) a ha (q j).hom.hom
    intro T x y
    change a.app (op ((Over.map (𝒰.f j)).obj T))
        ⟨baseChangePointsEquiv (𝒰.f j) G T x⟩ =
      a.app (op ((Over.map (𝒰.f j)).obj T))
        ⟨baseChangePointsEquiv (𝒰.f j) G T y⟩ ↔ _
    rw [hfib, (hq j).fibers T x y, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.mem_baseChange, map_mul, map_inv]
  choose e he using hlocal
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation F.property
    𝒰 (fun j => (Q j).X) e
  have hAffine : IsAffineHom V.hom :=
    LocalRepresentation.property_of_local_representations (@IsAffineHom)
      V eV 𝒰 (fun j => (Q j).X) e hQ
  let := hAffine
  let r : G.X ⟶ V := (schemeYoneda S).preimage (a ≫ eV.inv)
  have hr : (schemeYoneda S).map r ≫ eV.hom = a := by
    dsimp [r]
    rw [Functor.map_preimage, Category.assoc, eV.inv_hom_id, Category.comp_id]
  have hp : IsPullback (𝟙 ((schemeYoneda S).obj G.X))
      ((schemeYoneda S).map r) a eV.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hr.symm⟩
  have hsm : Smooth r.left := hgeom.2.2.2.1.projection eV.hom (𝟙 _) r hp
  have hsurj : Surjective r.left := hgeom.2.2.2.2.1.projection eV.hom (𝟙 _) r hp
  let := hsm
  let := hsurj
  have hqc : QuasiCompact r.left := by
    have : QuasiCompact (r.left ≫ V.hom) := by
      rw [Over.w r]
      infer_instance
    exact QuasiCompact.of_comp r.left V.hom
  let := hqc
  have hrfib : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ r = y ≫ r ↔ x⁻¹ * y ∈ (SubgroupFunctor.range i).carrier T := by
    intro T x y
    rw [← hfib]
    have hrx := congrArg (fun f => f.app (op T) ⟨x⟩) hr
    have hry := congrArg (fun f => f.app (op T) ⟨y⟩) hr
    rw [← hrx, ← hry]
    change x ≫ r = y ≫ r ↔
      eV.hom.app (op T) ⟨x ≫ r⟩ = eV.hom.app (op T) ⟨y ≫ r⟩
    constructor
    · intro hxy
      rw [hxy]
    · intro hxy
      exact congrArg ULift.down ((eV.app (op T)).toEquiv.injective hxy)
  exact ⟨groupScheme G (SubgroupFunctor.range i) hn r hrfib,
    hom G (SubgroupFunctor.range i) hn r hrfib,
    hAffine, isFppfQuotient G (SubgroupFunctor.range i) hn r hrfib⟩

end NormalQuotient

/-- Open-cover gluing of supplied affine fppf quotients by a smooth normal subgroup. -/
def AffineNormalQuotientOpenGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G N : GroupScheme S)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom],
    Smooth N.X.hom → (SubgroupFunctor.range i).IsNormal →
    ∀ (𝒰 : Scheme.OpenCover.{u} S)
      (Q : ∀ j, GroupScheme (𝒰.X j))
      (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j),
      (∀ j, IsAffineHom (Q j).X.hom) →
      (∀ j, RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) →
      ∃ (M : GroupScheme S) (r : G ⟶ M),
        IsAffineHom M.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r

/-- Supplied local affine quotients glue over every scheme and in every universe. -/
theorem affineNormalQuotientOpenGluing : AffineNormalQuotientOpenGluingStatement.{u} := by
  intro S G N _ _ i _ hN hn 𝒰 Q q hQ hq
  exact NormalQuotient.exists_affine_fppfQuotient_of_openCover i hN hn 𝒰 Q q hQ hq

end Langlands.GroupScheme
