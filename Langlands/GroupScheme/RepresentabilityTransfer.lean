import Langlands.GroupScheme.FixedRepresentabilityStatement

/-! # Transferring scheme representability to a subgroup scheme -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- A subgroup functor, regarded as a presheaf of groups. -/
def toFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (F.carrier T.unop)
  map b := GrpCat.ofHom
    { toFun := fun x => ⟨b.unop ≫ x.1, F.comp_mem b.unop x.2⟩
      map_one' := Subtype.ext (MonObj.comp_one b.unop)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul b.unop x.1 y.1) }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.id_comp x.1
  map_comp b c := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact Category.assoc c.unop b.unop x.1

/-- The natural inclusion into the ambient group-valued point functor. -/
def inclusion : F.toFunctor ⟶ GroupScheme.points G where
  app T := GrpCat.ofHom (F.carrier T.unop).subtype

variable {Z : Over S} (i : Z ⟶ G.X) [Mono i]
  (hi : ∀ (T : Over S) (x : T ⟶ G.X),
    x ∈ F.carrier T ↔ ∃ y : T ⟶ Z, y ≫ i = x)

/-- A monomorphism whose points are exactly the subgroup gives a set-valued
representation, on every test scheme. -/
def schemeRepresentableBy :
    (F.toFunctor ⋙ forget GrpCat).RepresentableBy Z where
  homEquiv {T} := Equiv.ofBijective
    (fun y => (⟨y ≫ i, (hi T _).2 ⟨y, rfl⟩⟩ : F.carrier T))
    ⟨fun y y' h => (cancel_mono i).1 (congrArg Subtype.val h), fun x => by
      obtain ⟨y, hy⟩ := (hi T x.1).1 x.2
      exact ⟨y, Subtype.ext hy⟩⟩
  homEquiv_comp b y := Subtype.ext (Category.assoc b y i)

/-- The group scheme carried by a scheme representing the subgroup functor. -/
abbrev representingGroupScheme : GroupScheme S :=
  letI := GrpObj.ofRepresentableBy Z F.toFunctor (F.schemeRepresentableBy i hi)
  Grp.mk Z

/-- The inclusion of the subgroup induces an actual group-scheme homomorphism. -/
def representingHom : F.representingGroupScheme i hi ⟶ G :=
  yonedaGrpFullyFaithful.preimage
    ((yonedaGrpObjIsoOfRepresentableBy Z F.toFunctor (F.schemeRepresentableBy i hi)).hom ≫
      F.inclusion)

/-- The induced group homomorphism has the given underlying scheme morphism. -/
theorem representingHom_hom :
    (F.representingHom i hi).hom.hom = i := by
  have h := congrArg
    (fun α : yonedaGrp.obj (F.representingGroupScheme i hi) ⟶ yonedaGrp.obj G =>
      (α.app (op Z)).hom (𝟙 Z))
    (yonedaGrpFullyFaithful.map_preimage
      ((yonedaGrpObjIsoOfRepresentableBy Z F.toFunctor
        (F.schemeRepresentableBy i hi)).hom ≫ F.inclusion))
  change 𝟙 Z ≫ (F.representingHom i hi).hom.hom = 𝟙 Z ≫ i at h
  simpa only [Category.id_comp] using h

/-- The induced group-scheme inclusion represents the original subgroup functor. -/
theorem isRepresentedBy_representingHom :
    F.IsRepresentedBy (F.representingHom i hi) := by
  constructor
  · rw [F.representingHom_hom i hi]
    infer_instance
  · ext T x
    rw [mem_range, F.representingHom_hom i hi]
    exact (hi T x).symm

include hi in
/-- Closed representability of a subgroup follows from a closed immersion of
schemes with the same all-test membership condition. -/
theorem isClosedRepresentable_of_scheme [IsClosedImmersion i.left] :
    F.IsClosedRepresentable := by
  refine ⟨F.representingGroupScheme i hi, F.representingHom i hi,
    F.isRepresentedBy_representingHom i hi, ?_⟩
  unfold IsClosedSubgroup
  rw [F.representingHom_hom i hi]
  infer_instance

end Langlands.GroupScheme.SubgroupFunctor
