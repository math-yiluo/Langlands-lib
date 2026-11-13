import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Concrete limits of smooth representations over small diagrams

For a diagram `F : J ⥤ SmoothRep R G` indexed by a small category, the smooth vectors of the
representation on compatible families form a limit. Consequently every limit cone of such a
diagram has jointly injective projections, and every compatible family fixed by one open
subgroup is the image of a vector of its cone point.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe uR uG uV

namespace Langlands.SmoothRep

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {J : Type} [SmallCategory J] (F : J ⥤ SmoothRep.{uR, uG, uV} R G)

/-- The componentwise action on all families of vectors of a diagram. -/
def familyRepresentation : Representation R G (∀ j, F.obj j) where
  toFun g := LinearMap.piMap fun j => (F.obj j).representation g
  map_one' := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp

@[simp]
theorem familyRepresentation_apply (g : G) (x : ∀ j, F.obj j) (j : J) :
    familyRepresentation F g x j = (F.obj j).representation g (x j) := rfl

/-- Families compatible with all transition maps of the diagram. -/
def compatibleFamilies : Subrepresentation (familyRepresentation F) where
  toSubmodule :=
    { carrier := {x | ∀ ⦃i j : J⦄ (f : i ⟶ j), hom (F.map f) (x i) = x j}
      add_mem' := by
        intro x y hx hy i j f
        change hom (F.map f) (x i + y i) = x j + y j
        rw [map_add, hx f, hy f]
      zero_mem' := by
        intro i j f
        change hom (F.map f) 0 = 0
        exact map_zero _
      smul_mem' := by
        intro a x hx i j f
        change hom (F.map f) (a • x i) = a • x j
        rw [map_smul, hx f] }
  apply_mem_toSubmodule g x hx := by
    intro i j f
    change hom (F.map f) ((F.obj i).representation g (x i)) = (F.obj j).representation g (x j)
    rw [(hom (F.map f)).isIntertwining, hx f]

variable [IsTopologicalGroup G]

/-- Compatible families fixed by some open subgroup. -/
def smoothCompatibleFamilies : Subrepresentation (familyRepresentation F) :=
  compatibleFamilies F ⊓ smoothSubrepresentation (familyRepresentation F)

/-- The concrete limit: smooth compatible families. -/
def concreteLimit : SmoothRep.{uR, uG, uV} R G :=
  of (smoothCompatibleFamilies F).toRepresentation (by
    intro x
    obtain ⟨K, hK⟩ := x.property.2
    refine ⟨K, ?_⟩
    intro k
    exact Subtype.ext (hK k))

/-- The underlying family of a vector of the concrete limit. -/
def concreteLimitFamily (x : concreteLimit F) : ∀ j, F.obj j :=
  (x : (smoothCompatibleFamilies F).toSubmodule).1

/-- The projection of the concrete limit to one vertex. -/
def concreteLimitπ (j : J) : concreteLimit F ⟶ F.obj j :=
  ofHom {
    toLinearMap :=
      (LinearMap.proj j).comp (smoothCompatibleFamilies F).toSubmodule.subtype
    isIntertwining' g := by
      ext x
      rfl }

theorem concreteLimit_ext {x y : concreteLimit F}
    (h : concreteLimitFamily F x = concreteLimitFamily F y) : x = y :=
  Subtype.ext h

@[simp]
theorem concreteLimitFamily_zero : concreteLimitFamily F 0 = 0 := rfl

@[simp]
theorem hom_concreteLimitπ_apply (j : J) (x : concreteLimit F) :
    hom (concreteLimitπ F j) x = concreteLimitFamily F x j := rfl

/-- The cone of projections from the concrete limit. -/
def concreteLimitCone : Cone F where
  pt := concreteLimit F
  π :=
    { app := concreteLimitπ F
      naturality := by
        intro i j f
        apply ObjectProperty.hom_ext
        ext x
        change concreteLimitFamily F x j = hom (F.map f) (concreteLimitFamily F x i)
        exact ((x : (smoothCompatibleFamilies F).toSubmodule).2.1 f).symm }

/-- The intertwiner from a cone point to smooth compatible families. -/
def coneToConcreteLimit (s : Cone F) :
    s.pt.representation.IntertwiningMap (concreteLimit F).representation where
  toLinearMap :=
    { toFun := fun v => ⟨fun j => hom (s.π.app j) v, by
        refine ⟨fun i j f => congrArg (fun φ => hom φ v) (s.w f), ?_⟩
        obtain ⟨K, hK⟩ := s.pt.isSmooth v
        refine ⟨K, ?_⟩
        intro k
        funext j
        change (F.obj j).representation (k : G) (hom (s.π.app j) v) = hom (s.π.app j) v
        rw [← (hom (s.π.app j)).isIntertwining]
        exact congrArg (hom (s.π.app j)) (hK k)⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        funext j
        exact map_add (hom (s.π.app j)) v w
      map_smul' := by
        intro a v
        apply Subtype.ext
        funext j
        exact map_smul (hom (s.π.app j)) a v }
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (funext fun j => ?_)
    exact (hom (s.π.app j)).isIntertwining _ _ g v

/-- The concrete limit cone is a limit. -/
def concreteLimitIsLimit : IsLimit (concreteLimitCone F) where
  lift s := ofHom (coneToConcreteLimit F s)
  fac s j := by
    apply ObjectProperty.hom_ext
    ext v
    rfl
  uniq s m h := by
    apply ObjectProperty.hom_ext
    ext v
    apply Subtype.ext
    funext j
    exact congrArg (fun φ => hom φ v) (h j)

variable {F}

/-- In any limit cone of smooth representations, the projections are jointly injective. -/
theorem eq_zero_of_isLimit {c : Cone F} (hc : IsLimit c) (x : c.pt)
    (hx : ∀ j, hom (c.π.app j) x = 0) : x = 0 := by
  let e : c.pt ≅ concreteLimit F := hc.conePointUniqueUpToIso (concreteLimitIsLimit F)
  have hfam : hom e.hom x = 0 := by
    apply concreteLimit_ext
    funext j
    have hj := congrArg (fun φ => hom φ x)
      (hc.conePointUniqueUpToIso_hom_comp (concreteLimitIsLimit F) j)
    exact hj.trans (hx j)
  have hinv : hom e.inv (hom e.hom x) = x :=
    congrArg (fun φ => hom φ x) e.hom_inv_id
  rw [← hinv, hfam, map_zero]

/-- In any limit cone of smooth representations, a compatible family fixed by one open
subgroup is the family of projections of a vector of the cone point. -/
theorem exists_eq_of_isLimit {c : Cone F} (hc : IsLimit c) (y : ∀ j, F.obj j)
    (hy : ∀ ⦃i j : J⦄ (f : i ⟶ j), hom (F.map f) (y i) = y j) (K : OpenSubgroup G)
    (hK : ∀ k ∈ K, ∀ j, (F.obj j).representation k (y j) = y j) :
    ∃ x : c.pt, ∀ j, hom (c.π.app j) x = y j := by
  let e : c.pt ≅ concreteLimit F := hc.conePointUniqueUpToIso (concreteLimitIsLimit F)
  let z : concreteLimit F := ⟨y, hy, ⟨K, by
    intro k
    funext j
    exact hK k k.property j⟩⟩
  refine ⟨hom e.inv z, fun j => ?_⟩
  exact congrArg (fun φ => hom φ z)
    (hc.conePointUniqueUpToIso_inv_comp (concreteLimitIsLimit F) j)

/-- In any limit cone of smooth representations, a compatible family fixed by one open
subgroup `K` is the family of projections of a `K`-fixed vector of the cone point. -/
theorem exists_fixed_eq_of_isLimit {c : Cone F} (hc : IsLimit c) (y : ∀ j, F.obj j)
    (hy : ∀ ⦃i j : J⦄ (f : i ⟶ j), hom (F.map f) (y i) = y j) (K : OpenSubgroup G)
    (hK : ∀ k ∈ K, ∀ j, (F.obj j).representation k (y j) = y j) :
    ∃ x : c.pt, (∀ k ∈ K, c.pt.representation k x = x) ∧ ∀ j, hom (c.π.app j) x = y j := by
  obtain ⟨x, hx⟩ := exists_eq_of_isLimit hc y hy K hK
  refine ⟨x, fun k hk => ?_, hx⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_isLimit hc
  intro j
  have hint : hom (c.π.app j) (c.pt.representation k x) =
      (F.obj j).representation k (hom (c.π.app j) x) :=
    (hom (c.π.app j)).isIntertwining _ _ k x
  rw [map_sub, hint, hx j, hK k hk j, sub_self]

omit [IsTopologicalGroup G] in
/-- Over the opposite of a discrete category every family of vectors is compatible: the
only morphisms are identities. -/
theorem discreteOp_map_apply {ι : Type} (H : (Discrete ι)ᵒᵖ ⥤ SmoothRep.{uR, uG, uV} R G)
    (y : ∀ j, H.obj j) ⦃i j : (Discrete ι)ᵒᵖ⦄ (f : i ⟶ j) : hom (H.map f) (y i) = y j := by
  obtain rfl : i = j := Opposite.unop_injective (Discrete.ext (Discrete.eq_of_hom f.unop).symm)
  obtain rfl : f = 𝟙 i := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [H.map_id]
  rfl

end Langlands.SmoothRep
